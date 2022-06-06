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

Notation copn_args := (seq lval * sopn * seq pexpr)%type (only parsing).
Notation lowered_pexpr := (option (arm_op * seq pexpr)) (only parsing).

(* -------------------------------------------------------------------- *)
(* Fresh variables. *)
(* This pass is parameterized by four variable names that will be used to create
   variables for the processor flags. *)

Record fresh_vars :=
  {
    fv_NF : Ident.ident;
    fv_ZF : Ident.ident;
    fv_CF : Ident.ident;
    fv_VF : Ident.ident;
  }.

Definition all_fresh_vars (fv : fresh_vars) : seq Ident.ident :=
  [:: fv_NF fv; fv_ZF fv; fv_CF fv; fv_VF fv ].

Definition fvNF (fv : fresh_vars) : var := vbool (fv_NF fv).
Definition fvZF (fv : fresh_vars) : var := vbool (fv_ZF fv).
Definition fvCF (fv : fresh_vars) : var := vbool (fv_CF fv).
Definition fvVF (fv : fresh_vars) : var := vbool (fv_VF fv).

Definition fresh_flags (fv : fresh_vars) : seq var :=
  [:: fvNF fv; fvZF fv; fvCF fv; fvVF fv ].

Definition fvars (fv : fresh_vars) : Sv.t := sv_of_list id (fresh_flags fv).


(* -------------------------------------------------------------------- *)

Section ARM_LOWERING.

Context
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool).

Notation is_lval_in_memory := (is_lval_in_memory is_var_in_memory).


(* -------------------------------------------------------------------- *)
(* Lowering of conditions. *)

#[ local ]
Definition mk_fv_vari x := {| v_var := x; v_info := xH; |}.

#[ local ]
Definition mk_fv_gvar x := {| gv := mk_fv_vari x; gs := Slocal; |}.

Definition lflags : seq lval :=
  map (fun x => Lvar (mk_fv_vari x)) (fresh_flags fv).

Definition lower_condition_Papp2 (op : sop2) (e0 e1 : pexpr) : option pexpr :=
  let eNF := Pvar (mk_fv_gvar (fvNF fv)) in
  let eZF := Pvar (mk_fv_gvar (fvZF fv)) in
  let eCF := Pvar (mk_fv_gvar (fvCF fv)) in
  let eVF := Pvar (mk_fv_gvar (fvVF fv)) in
  match op with
  | Oeq (Op_w U32) => Some eZF
  | Oneq (Op_w U32) => Some (enot eZF)
  | Olt (Cmp_w Signed U32) => Some (eneq eNF eVF)
  | Olt (Cmp_w Unsigned U32) => Some (enot eCF)
  | Ole (Cmp_w Signed U32) => Some (eor eZF (eneq eNF eVF))
  | Ole (Cmp_w Unsigned U32) => Some (eor (enot eCF) eZF)
  | Ogt (Cmp_w Signed U32) => Some (eand (enot eZF) (eeq eNF eVF))
  | Ogt (Cmp_w Unsigned U32) => Some (eand eCF (enot eZF))
  | Oge (Cmp_w Signed U32) => Some (eeq eNF eVF)
  | Oge (Cmp_w Unsigned U32) => Some eCF
  | _ => None
  end.

Definition lower_condition_pexpr
  (e : pexpr) : option (seq lval * sopn * seq pexpr * pexpr) :=
  if e is Papp2 op e0 e1
  then
    if lower_condition_Papp2 op e0 e1 is Some e'
    then Some (lflags, Oarm (ARM_op CMP default_opts), [:: e0; e1 ], e')
    else None
  else
    None.

Definition lower_condition (e : pexpr) : seq instr_r * pexpr :=
  if lower_condition_pexpr e is Some (lvs, op, es, c)
  then ([:: Copn lvs AT_none op es ], c)
  else ([::], e).


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

(* Lower an expression of the form [(ws)[v + e]].
   Precondition:
   - [v] is a register.
   - [e] is one of the following:
     + a register.
     + an immediate. *)
Definition lower_Pload
  (ws ws' : wsize) (v : var_i) (e : pexpr) : lowered_pexpr :=
  if ws == ws'
  then
    if load_mn_of_wsize ws is Some mn
    then Some (ARM_op mn default_opts, [:: Pload ws v e ])
    else None
  else
    None.

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : lowered_pexpr :=
  match ws, op with
  | U32, Oword_of_int U32 => Some (ARM_op MOV default_opts, [:: Papp1 op e ])
  | _, _ => None
  end.

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
  if lower_Papp2_op ws op is Some mn
  then
    let opts :=
      {| set_flags := false; is_conditional := false; has_shift := osh; |}
    in
    Some (ARM_op mn opts, es)
  else
    None.

Definition lower_pexpr_aux (ws : wsize) (e : pexpr) : lowered_pexpr :=
  match e with
  | Pvar v => lower_Pvar ws v
  | Pload ws' v e => lower_Pload ws ws' v e
  | Papp1 op e => lower_Papp1 ws op e
  | Papp2 op a b => lower_Papp2 ws op a b
  | _ => None
  end.

Definition no_pre (ole : lowered_pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  if ole is Some (aop, es) then Some ([::], aop, es) else None.

Definition lower_pexpr (ws : wsize) (e : pexpr) :
  option (seq instr_r * arm_op * seq pexpr) :=
  if e is Pif (sword ws') c e0 e1 then
    if lower_pexpr_aux ws e0 is Some (ARM_op mn opts, es)
    then
      if ws == ws'
      then
        let '(pre, c') := lower_condition c in
        Some (pre, ARM_op mn (set_is_conditional opts), es ++ [:: c'; e1 ])
      else
        None
    else
      None
  else
    no_pre (lower_pexpr_aux ws e).

(* Lower an assignment to memory.
   Precondition:
   - [lv] must be one of the following:
     + a variable in memory.
     + a memory location.
   - [e] must be one of the following:
     + a register.
     + an if expression. *)
Definition lower_store (ws : wsize) (e : pexpr) : option (arm_op * seq pexpr) :=
  if store_mn_of_wsize ws is Some op
  then
    let args :=
      match e with
      | Pvar _ => Some (default_opts, [:: e ])
      | Pif _ c e0 e1 => Some (set_is_conditional default_opts, [:: e0; c; e1 ])
      | _ => None
      end
    in
    if args is Some (opts, es)
    then Some (ARM_op op opts, es)
    else None
  else
    None.

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn
  (lv : lval) (ty : stype) (e : pexpr) : option (seq instr_r * copn_args) :=
  if ty is sword ws
  then
    let le :=
      if is_lval_in_memory lv
      then no_pre (lower_store ws e)
      else lower_pexpr ws e
    in
    if le is Some (pre, aop, es)
    then Some (pre, ([:: lv ], Oarm aop, es))
    else None
  else None.


(* -------------------------------------------------------------------- *)
(* Lowering of architecture-specific operations. *)

Definition lower_copn
  (lvs : seq lval) (op : sopn) (es : seq pexpr) : option copn_args :=
  match op with
  | Oasm (BaseOp (None, ARM_op mn opts)) =>
      if mn \in has_shift_mnemonics
      then Some (lvs, op, es) (* TODO_ARM: Complete. *)
      else None
  | _ => None
  end.


(* -------------------------------------------------------------------- *)

Definition lowering_options := unit.

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn lv tag ty e =>
      let irs :=
        if lower_cassgn lv ty e is Some (pre, (lvs, op, es))
        then pre ++ [:: Copn lvs tag op es ]
        else [:: ir ]
      in
      map (MkI ii) irs

  | Copn lvs tag op es =>
      let ir' :=
        if lower_copn lvs op es is Some (lvs', op', es')
        then Copn lvs' tag op' es'
        else ir
      in
      [:: MkI ii ir' ]

  | Cif e c1 c2  =>
      let '(pre, e') := lower_condition e in
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])

  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e c1 =>
      let '(pre, e') := lower_condition e in
      let c0' := conc_map lower_i c0 in
      let c1' := conc_map lower_i c1 in
      [:: MkI ii (Cwhile a (c0' ++ map (MkI ii) pre) e' c1') ]

  | _ =>
      [:: i ]
  end.

End ARM_LOWERING.
