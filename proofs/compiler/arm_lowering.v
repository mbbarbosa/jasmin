From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.

Require Import
  compiler_util
  expr
  lowering.
Require Import
  arch_decl
  arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section ARM_LOWERING.

Context
  (is_var_in_memory : var_i -> bool).

Notation is_lval_in_memory := (is_lval_in_memory is_var_in_memory).

(* TODO_ARM: This might be architecture independent? *)
Definition wsize_of_stype (ty : stype) : wsize :=
  if ty is sword sz
  then sz
  else reg_size.


(* -------------------------------------------------------------------- *)
(* Lowering of assignments. *)

Definition get_arg_shift
  (ws : wsize) (e : pexpr) : option (pexpr * shift_kind * pexpr) :=
  if e is
    Papp2 op ((Pvar _) as v) ((Papp1 (Oword_of_int U8) (Pconst z)) as n)
  then
    if shift_of_sop2 ws op is Some sh
    then
      if check_shift_amount sh z then Some (v, sh, n) else None
    else
      None
  else
    None.


(** Lowering of [pexpr]s. *)

Notation lowered_pexpr := (option (arm_op * seq pexpr)).


(*** Lowering of [Pvar]. *)

(* Lower an expression of the form [v].
   Precondition:
   - [v] is a one of the following:
     + a register.
     + a stack variable. *)
Definition lower_Pvar (ws : wsize) (v : gvar) : lowered_pexpr :=
  let omn :=
    if is_var_in_memory (gv v)
    then load_mn_of_wsize ws
    else if ws is U32 then Some MOV else None
  in
  if omn is Some mn
  then Some (ARM_op mn default_opts, [:: Pvar v ])
  else None.


(*** Lowering of [Pload]. *)

(* Lower an expression of the form [(ws)[v + e]].
   Precondition:
   - [v] is a register.
   - [e] is one of the following:
     + a register.
     + an immediate. *)
Definition lower_Pload (ws : wsize) (v : var_i) (e : pexpr) : lowered_pexpr :=
  if load_mn_of_wsize ws is Some op
  then Some (ARM_op op default_opts, [:: Pload ws v e ])
  else None.


(*** Lowering of [Papp1]. *)

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : lowered_pexpr :=
  match ws, op with
  | U32, Oword_of_int U32 => Some (ARM_op MOV default_opts, [:: Papp1 op e ])
  | _, _ => None
  end.

(*** Lowering of [Papp2]. *)

Definition lower_Papp2_op (ws : wsize) (op : sop2) : option arm_mnemonic :=
  match ws, op with
  | U32, Oadd (Op_w U32) => Some ADD
  | U32, Osub (Op_w U32) => Some SUB
  | U32, Oland U32 => Some AND
  | _, _ => None
  end.

(* Lower an expression of the form [a <+> b].
   Precondition:
   - [a] is a register.
   - [b] is one of the following:
     + a register.
     + a shifted register.
     + an immediate word. *)
Definition lower_Papp2 (ws : wsize) (op : sop2) (a b : pexpr) : lowered_pexpr :=
  let '(osh, es) :=
    if get_arg_shift ws b is Some (b', sh, n)
    then (Some sh, [:: a; b'; n ])
    else (None, [:: a; b ])
  in
  (* TODO_ARM: Should we check [ws] here? *)
  (* Perhaps, because the instruction to use depends on the size of the
     output and on the size of the inputs. *)
  if lower_Papp2_op ws op is Some mn
  then
    let opts :=
      {| set_flags := false; is_conditional := false; has_shift := osh; |}
    in
    Some (ARM_op mn opts, es)
  else
    None.


(*** Lowering of [Pif]. *)

(* Lower an expression of the form [if c then e0 else e1].
   Precondition:
   - [c] is a flag.
   - [c] has been set correctly: we do not introduce comparisons.
   - [e0] can be lowered.
   - [e1] is a register (the same as the one being assigned to). *)
Definition lower_Pif
  (lower_pexpr : pexpr -> lowered_pexpr) (c e0 e1 : pexpr) : lowered_pexpr :=
  if lower_pexpr e0 is Some (ARM_op mn opts, es)
  then Some (ARM_op mn (set_is_conditional opts), es ++ [:: c; e1 ])
  else None.


Fixpoint lower_pexpr (ws : wsize) (e : pexpr) : lowered_pexpr :=
  match e with
  | Pvar v =>
      lower_Pvar ws v

  | Pload ws' v e =>
      if ws == ws' (* TODO_ARM: is this correct? *)
      then lower_Pload ws v e
      else None

  | Papp1 op e =>
      lower_Papp1 ws op e

  | Papp2 op a b =>
      lower_Papp2 ws op a b

  | Pif (sword ws') c e0 e1 =>
      if ws == ws'
      then lower_Pif (lower_pexpr ws) c e0 e1
      else None

  | _ =>
      None
  end.


(** Lower store instructions. *)

(* Lower an assignment to memory.
   Precondition:
   - [lv] must be one of the following:
     + a variable in memory.
     + a memory location.
   - [e] must be one of the following:
     + a register.
     + an if expression. *)
Definition lower_store (ws : wsize) (e : pexpr) : lowered_pexpr :=
  if store_mn_of_wsize ws is Some op
  then
    let args :=
      match e with
      | Pvar _ =>
          Some (default_opts, [:: e ])
      | Pif _ c e0 e1 =>
          Some (set_is_conditional default_opts, [:: e0; c; e1 ])
      | _ =>
          None
      end
    in
    if args is Some (opts, es)
    then Some (ARM_op op opts, es)
    else None
  else
    None.

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn
  (lv : lval) (ty : stype) (e : pexpr) : option (lvals * sopn * pexprs) :=
  if ty is sword ws
  then
    let le :=
      if is_lval_in_memory lv
      then lower_store ws e
      else lower_pexpr ws e
    in
    if le is Some (op, es)
    then Some ([:: lv ], Oarm op, es)
    else None
  else None.


(* -------------------------------------------------------------------- *)

(* TODO_ARM: Complete. *)
(* Refine expressions passed to architecture-specific operations. *)
Definition lower_copn
  (lvs : lvals) (op : sopn) (es : seq pexpr) : option (lvals * sopn * pexprs) :=
  match op with
  | Oasm (BaseOp (None, ARM_op mn opts)) =>
      if mn \in has_shift_mnemonics
      then Some (lvs, op, es)
      else None
  | _ => None
  end.

(* -------------------------------------------------------------------- *)

Definition fresh_vars := unit.
Definition lowering_options := unit.

Definition arm_fvars_correct
  (_ : fresh_vars) {eft : eqType} {_ : progT eft} (_ : fun_decls) : bool :=
  true.

Definition lower_condition
  (ii : instr_info) (cond : pexpr) : seq instr_r * pexpr :=
  ([::], cond).

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      let ir' :=
        if lower_cassgn lv ty e is Some (lvs, op, es)
        then Copn lvs tag op es
        else ir
      in
      [:: MkI ii ir' ]

  | Copn lvs tag op es =>
      let ir' :=
        if lower_copn lvs op es is Some (lvs', op', es')
        then Copn lvs' tag op' es'
        else ir
      in
      [:: MkI ii ir' ]

  | Cif e c1 c2  =>
      let '(pre, e') := lower_condition xH e in
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])

  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e c1 =>
      let '(pre, e') := lower_condition xH e in
      let c0' := conc_map lower_i c0 in
      let c1' := conc_map lower_i c1 in
      [:: MkI ii (Cwhile a (c0' ++ map (MkI xH) pre) e' c1') ]

  | _ =>
      [:: i ]
  end.

End ARM_LOWERING.
