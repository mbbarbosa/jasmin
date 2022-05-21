From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  arch_params
  compiler_util
  expr
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  lowering
  stack_alloc.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition addi x tag y ofs :=
  let eofs := Papp1 (Oword_of_int reg_size) (Pconst ofs) in
  Copn [:: x ] tag (Oarm (ARM_op ADD default_opts)) [:: y; eofs ].

Definition arm_mov_ofs
  (x : lval) tag (_ : vptr_kind) (y : pexpr) (ofs : Z) : option instr_r :=
  Some (addi x tag y ofs).

Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  let esz := Papp1 (Oword_of_int reg_size) (Pconst sz) in
  ([:: Lvar rspi ], Oarm (ARM_op ADD default_opts), [:: Pvar rspg; esz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  let esz := Papp1 (Oword_of_int reg_size) (Pconst (-sz)) in
  ([:: Lvar rspi ], Oarm (ARM_op ADD default_opts), [:: Pvar rspg; esz ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Papp1 (Oword_of_int reg_size) (Pconst (- wsize_size al)) in
  ([:: Lvar rspi ], Oarm (ARM_op AND default_opts), [:: p0; p1 ]).

Definition arm_lassign (x : lval) (_ : wsize) (e : pexpr) :=
  let mn :=
    match x with
    | Lvar _ =>
        if e is Pload _ _ _
        then LDR
        else MOV
    | Lmem _ _ _ =>
        STR
    | _ =>
        TODO_ARM "arm_lassign"
    end
  in
  ([:: x ], Oarm (ARM_op mn default_opts), [:: e ]).

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp := "r12"%string; (* TODO_ARM: Review. *)
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lip_lassign := arm_lassign;
  |}.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition arm_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := fun _ _ _ => lower_i;
    lop_fvars_correct := arm_fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition assemble_cond ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v => Let r := of_var_e ii (gv v) in ok (condt_of_rflag r)
  | _ => Error (E.berror ii e "Invalid condition.") (* TODO_ARM: Complete. *)
  end.

Definition arm_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition arm_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, ARM_op MOV opts) =>
      [&& ~~ set_flags opts
        , ~~ is_conditional opts
        & ~~ has_shift opts
      ]

  | _ =>
      false
  end.

Definition arm_params : architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := (fun _ => arm_saparams);
    ap_lip := arm_liparams;
    ap_lop := arm_loparams;
    ap_agp := arm_agparams;
    ap_is_move_op := arm_is_move_op;
  |}.
