(* ARM Cortex-M4 instruction set

   These are the THUMB instructions of ARMv7-M, the instruction set of the M4
   processor. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.

Require Import
  sem_type
  strings
  utils
  word.
Require Export arch_decl.
Require Import arm_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* -------------------------------------------------------------------- *)
(* ARM instruction options. *)

Record arm_options :=
  {
    args_size : wsize;
    set_flags : bool;
    is_conditional : bool;
    has_shift : option shift_kind;
  }.

Definition arm_options_beq (ao0 ao1 : arm_options) : bool :=
  [&& args_size ao0 == args_size ao1
    , set_flags ao0 == set_flags ao1
    , is_conditional ao0 == is_conditional ao1
    & has_shift ao0 == has_shift ao1
  ].

Lemma arm_options_eq_axiom : Equality.axiom arm_options_beq.
Proof.
  move=> [? ? ? ?] [? ? ? ?].
  apply: (iffP idP);
    last move=> <-;
    rewrite /arm_options_beq /=.
  - move=> /and4P [].
    repeat move=> /eqP ?.
    by subst.
  - by apply/and4P.
Qed.

Instance eqTC_arm_options : eqTypeC arm_options :=
  { ceqP := arm_options_eq_axiom }.

Canonical arm_options_eqType := @ceqT_eqType _ eqTC_arm_options.

Lemma arm_options_dec_eq (ao0 ao1 : arm_options) :
  { ao0 = ao1 } + { ao0 <> ao1 }.
Proof.
  case: (ao0 == ao1) /arm_options_eq_axiom.
  - by left.
  - by right.
Qed.

Definition default_opts (ws : wsize) : arm_options :=
  {|
    args_size := ws;
    set_flags := false;
    is_conditional := false;
    has_shift := None;
  |}.

Definition set_is_conditional (ao : arm_options) : arm_options :=
  {|
    args_size := args_size ao;
    set_flags := set_flags ao;
    is_conditional := true;
    has_shift := has_shift ao;
  |}.

Definition unset_is_conditional (ao : arm_options) : arm_options :=
  {|
    args_size := args_size ao;
    set_flags := set_flags ao;
    is_conditional := false;
    has_shift := has_shift ao;
  |}.


(* -------------------------------------------------------------------- *)
(* ARM instruction mnemonics. *)

Variant arm_mnemonic : Type :=
(* Arithmetic *)
| ADC                            (* Add with carry *)
| ADD                            (* Add without carry *)

| SBC                            (* Subtract with carry *)
| SUB                            (* Subtract without carry *)

| MUL                            (* Multiply *)
| MLA                            (* Multiply and accumulate *)
| MLS                            (* Multiply and subtract *)
| SMLAL                          (* Signed multiply accumulate long *)
| SMULL                          (* Signed multiply long *)
| UMLAL                          (* Unsigned multiply accumulate long *)
| UMULL                          (* Unsigned multiply long *)

| SDIV                           (* Signed integer division *)
| UDIV                           (* Unsigned integer division *)

| SSAT                           (* Signed saturate *)
| USAT                           (* Unsigned saturate *)

| SXTB                           (* Signed extend byte *)
| SXTH                           (* Signed extend halfword *)
| UXTB                           (* Unsigned extend byte *)
| UXTH                           (* Unsigned extend halfword *)

(* Logical *)
| AND                            (* Bitwise AND *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)
| ORR                            (* Bitwise OR *)

(* Shifts *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)

(* Comparison *)
| CMP                            (* Compare *)
| TST                            (* Test flags *)

(* Other data processing instructions *)
| BIC                            (* Bitwise bit clear *)
| MOV                            (* Copy operand to destination *)

(* Loads *)
| LDR                            (* Load a 32-bit word *)
| LDRH                           (* Load a 16-bit unsigned halfword *)
| LDRSH                          (* Load a 16-bit signed halfword *)
| LDRB                           (* Load a 8-bit unsigned byte *)
| LDRSB                          (* Load a 8-bit signed byte *)
| LDRD                           (* Load two 32-bit words *)
| LDM                            (* Load multiple 32-bit words *)
| LDMIA                          (* Load multiple 32-bit words,
                                    increment base after *)
| LDMDB                          (* Load multiple 32-bit words,
                                    decrement base before *)
| POP                            (* Load multiple 32-bit words from the stack,
                                    decrement sp (defined in terms of LDMIA) *)

(* Stores *)
| STR                            (* Store a 32-bit word *)
| STRH                           (* Store a 16-bit halfword *)
| STRB                           (* Store a 8-bit byte *)
| STRD                           (* Store two 32-bit words *)
| STM                            (* Store multiple 32-bit words *)
| STMIA                          (* Store multiple 32-bit words,
                                    increment base after *)
| STMDB                          (* Store multiple 32-bit words,
                                    decrement base before *)
| PUSH.                          (* Store multiple 32-bit words from the stack,
                                    decrement sp (defined in terms of STMDB) *)

Definition arm_mnemonic_dec_eq (mn0 mn1 : arm_mnemonic) :
  {mn0 = mn1} + {mn0 <> mn1}.
  by repeat decide equality.
Defined.

Definition arm_mnemonic_beq (mn0 mn1 : arm_mnemonic) : bool :=
  if arm_mnemonic_dec_eq mn0 mn1 is left _
  then true
  else false.

Lemma arm_mnemonic_eq_axiom : Equality.axiom arm_mnemonic_beq.
Proof.
  move=> mn0 mn1.
  apply: (iffP idP);
    last move=> <-;
    rewrite /arm_mnemonic_beq;
    by case: arm_mnemonic_dec_eq.
Qed.

Instance eqTC_arm_mnemonic : eqTypeC arm_mnemonic :=
  { ceqP := arm_mnemonic_eq_axiom }.

Canonical arm_mnemonic_eqType := @ceqT_eqType _ eqTC_arm_mnemonic.

Definition arm_mnemonics : seq arm_mnemonic :=
  [:: ADC; ADD; SBC; SUB; MUL; MLA; MLS; SMLAL; SMULL; UMLAL; UMULL
    ; SDIV; UDIV; SSAT; USAT; SXTB; SXTH; UXTB; UXTH
    ; AND; EOR; MVN; ORR
    ; LSL; LSR; ROR
    ; CMP; TST
    ; BIC; MOV
    ; LDR; LDRH; LDRSH; LDRB; LDRSB; LDRD; LDM; LDMIA; LDMDB; POP
    ; STR; STRH; STRB; STRD; STM; STMIA; STMDB; PUSH
  ].

Lemma arm_mnemonic_fin_axiom : Finite.axiom arm_mnemonics.
Proof. by case. Qed.

Instance finTC_arm_mnemonic : finTypeC arm_mnemonic :=
  {
    cenum := arm_mnemonics;
    cenumP := arm_mnemonic_fin_axiom;
  }.

Canonical arm_mnemonic_finType := @cfinT_finType _ finTC_arm_mnemonic.

Definition string_of_arm_mnemonic (mn : arm_mnemonic) : string :=
  match mn with
  | ADC => "adc"
  | ADD => "add"
  | SBC => "sbc"
  | SUB => "sub"
  | MUL => "mul"
  | MLA => "mla"
  | MLS => "mls"
  | SMLAL => "smlal"
  | SMULL => "smull"
  | UMLAL => "umlal"
  | UMULL => "umull"
  | SDIV => "sdiv"
  | UDIV => "udiv"
  | SSAT => "ssat"
  | USAT => "usat"
  | SXTB => "sxtb"
  | SXTH => "sxth"
  | UXTB => "uxtb"
  | UXTH => "uxth"
  | AND => "and"
  | EOR => "eor"
  | MVN => "mvn"
  | ORR => "orr"
  | LSL => "lsl"
  | LSR => "lsr"
  | ROR => "ror"
  | CMP => "cmp"
  | TST => "tst"
  | BIC => "bic"
  | MOV => "mov"
  | LDR => "ldr"
  | LDRH => "ldrh"
  | LDRSH => "ldrsh"
  | LDRB => "ldrb"
  | LDRSB => "ldrsb"
  | LDRD => "ldrd"
  | LDM => "ldm"
  | LDMIA => "ldmia"
  | LDMDB => "ldmdb"
  | POP => "pop"
  | STR => "str"
  | STRH => "strh"
  | STRB => "strb"
  | STRD => "strd"
  | STM => "stm"
  | STMIA => "stmia"
  | STMDB => "stmdb"
  | PUSH => "push"
  end.

Lemma string_of_register_inj : injective string_of_register.
Proof.
  move=> x y /eqP h; apply/eqP; case: x y h => -[]; by vm_compute.
Qed.


(* -------------------------------------------------------------------- *)
(* ARM operators are pairs of mnemonics and options. *)

Variant arm_op :=
| ARM_op : arm_mnemonic -> arm_options -> arm_op.

Definition arm_op_beq (op0 op1 : arm_op) : bool :=
  let '(ARM_op mn0 ao0) := op0 in
  let '(ARM_op mn1 ao1) := op1 in
  (mn0 == mn1) && (ao0 == ao1).

Lemma arm_op_eq_axiom : Equality.axiom arm_op_beq.
Proof.
  move=> [mn0 ao0] [mn1 ao1].
  apply: (iffP idP);
    last move=> <-;
    rewrite /arm_op_beq /=.
  - move=> /andP [].
    move=> /arm_mnemonic_eq_axiom <-.
    by move=> /arm_options_eq_axiom <-.
  - apply/andP. split.
    + by apply/arm_mnemonic_eq_axiom.
    + by apply/arm_options_eq_axiom.
Qed.

Instance eqTC_arm_op : eqTypeC arm_op :=
  { ceqP := arm_op_eq_axiom }.

Canonical arm_op_eqType := @ceqT_eqType _ eqTC_arm_op.

Lemma arm_op_dec_eq (op0 op1 : arm_op) :
  { op0 = op1 } + { op0 <> op1 }.
Proof.
  case: (op0 == op1) /arm_op_eq_axiom.
  - by left.
  - by right.
Qed.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation wreg_ty := (sem_tuple [:: sreg ]).

(* Tuple for flag values: (NF, ZF, CF, VF). *)
Notation sflag := (sbool) (only parsing).
Notation sflags := ([:: sflag; sflag; sflag; sflag ]) (only parsing).
Notation nzcv_ty := (sem_tuple sflags) (only parsing).

Notation flag_ty := (sem_tuple [:: sflag ]) (only parsing).
Notation nzcvr_ty := (sem_tuple (sflags ++ [:: sreg ])) (only parsing).

Notation nzcvw_ty sz := (sem_tuple (sflags ++ [:: sword sz ])) (only parsing).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions.*)

Definition rflags_ad : seq arg_desc := map F rflags.


(* -------------------------------------------------------------------- *)
(* Common argument kinds. *)

Definition reg_reg_ak := [:: [:: [:: CAreg ]; [:: CAreg ] ] ].
Definition reg_imm_ak := [:: [:: [:: CAreg ]; [:: CAimm reg_size ] ] ].
Definition reg_reg_reg_ak := [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ] ] ].
Definition reg_reg_imm_ak := [:: [:: [:: CAreg ]; [:: CAimm reg_size ] ] ].
Definition reg_addr_ak := [:: [:: [:: CAreg ]; [:: CAmem true ] ] ].


(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (sz : wsize) (w : word sz) := msb w.
Definition ZF_of_word (sz : wsize) (w : word sz) := w == 0%R.

(* Compute the value of the flags for an arithmetic operation.
 * For instance, for <+> a binary operation, this function should be called
 * with
 *   res = w <+> w'
 *   res_unsigned = wunsigned w Z.<+> wunsigned w'
 *   res_signed = wsigned w Z.<+> wsigned w'
 *)
Definition nzcv_of_aluop
  {sz : wsize}
  (res : word sz)     (* Actual result. *)
  (res_unsigned : Z)  (* Result with unsigned interpretation. *)
  (res_signed : Z)    (* Result with signed interpretation. *)
  : nzcv_ty :=
  (:: Some (NF_of_word res)                 (* NF *)
    , Some (ZF_of_word res)                 (* ZF *)
    , Some (wunsigned res != res_unsigned)  (* CF *)
    & Some (wsigned res != res_signed)      (* VF *)
  ).

Definition nzcvw_of_aluop (sz : wsize) (w : word sz) (wu ws : Z) :=
  merge_tuple (nzcv_of_aluop w wu ws) (w : sem_tuple [:: sword sz ]).


(* -------------------------------------------------------------------- *)
(* Flag setting transformations.
 * Instruction descriptions are defined setting flags. The case where
 * the flags should not be set is considered with `drop_nzcv`.
 *)

Notation behead4 xs := (behead (behead (behead (behead xs)))).

Definition drop_semi_nzcv
  {tin tout} (semi : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod tin (exec (sem_tuple (behead4 tout))) :=
  behead_tuple (behead_tuple (behead_tuple (behead_tuple semi))).

#[ local ]
Lemma drop_nzcv_eq_size {A B} {p} {xs : seq A} {ys : seq B} :
  p && (size xs == size ys)
  -> p && (size (behead4 xs) == size (behead4 ys)).
Proof.
  move=> /andP [] Hp /eqP Hxy.
  apply/andP.
  by rewrite !size_behead Hxy.
Qed.

#[ local ]
Lemma drop_nzcv_check_dest
  {A B} {p : A -> B -> bool} {xs : seq A} {ys : seq B} :
  all2 p xs ys -> all2 p (behead4 xs) (behead4 ys).
Proof.
  move=> H.
  by do 4 apply: all2_behead.
Qed.

#[ local ]
Lemma drop_nzcv_tout_narr {A} {p : A -> bool} {xs : seq A} :
  all p xs -> all p (behead4 xs).
Proof.
  move=> H.
  by do 4 apply: all_behead.
Qed.

Definition drop_nzcv (idt : instr_desc_t) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := id_tin idt;
    id_in := id_in idt;
    id_tout := behead4 (id_tout idt);
    id_out := behead4 (id_out idt);
    id_semi := drop_semi_nzcv (id_semi idt);
    id_nargs := id_nargs idt;
    id_args_kinds := id_args_kinds idt;
    id_eq_size := drop_nzcv_eq_size (id_eq_size idt);
    id_tin_narr := id_tin_narr idt;
    id_tout_narr := drop_nzcv_tout_narr (id_tout_narr idt);
    id_check_dest := drop_nzcv_check_dest (id_check_dest idt);
    id_str_jas := id_str_jas idt;
    id_wsize := reg_size;
    id_safe := [::];
    id_pp_asm := id_pp_asm idt;
  |}.
Arguments drop_nzcv : clear implicits.


(* -------------------------------------------------------------------- *)
(* Conditional transformations.
 * Instruction descriptions are defined unconditionally. The following
 * transformation converts an unconditional instruction into a conditional
 * one.
 * The output type is unchanged.
 * The input type is expanded with:
 * - A boolean. It is used to determine if the instruction is executed
 * - The output type. It is used to return the unchanged values if the
 *   instruction is not exectuted
 * The semantics and the rest of the fields are updated accordingly.
 *)

#[ local ]
Lemma mk_cond_eq_size
  {A B} {x y} {xs0 xs1 : seq A} {ys0 ys1 : seq B} :
  (size xs0 == size ys0) && (size xs1 == size ys1)
  -> (size (xs0 ++ x :: xs1) == size (ys0 ++ y :: ys1))
     && (size xs1 == size ys1).
Proof.
  move=> /andP [] /eqP H0 /eqP H1.
  apply/andP.
  by rewrite 2!size_cat /= H0 H1.
Qed.

#[ local ]
Lemma mk_cond_tin_narr {A} {p : A -> bool} {x} {xs ys : seq A} :
  p x
  -> all p xs
  -> all p ys
  -> all p (xs ++ x :: ys).
Proof.
  move=> Hx Hxs Hys.
  rewrite /= all_cat.
  apply/andP.
  split;
    first done.
  by apply/andP.
Qed.

Definition mk_semi_cond tin tout (semi : sem_prod tin (exec (sem_tuple tout)))
  : sem_prod (tin ++ sbool :: tout) (exec (sem_tuple tout)) :=
  let f0 res cond : sem_prod tout (exec (sem_tuple tout)) :=
    if cond
    then sem_prod_const tout res
    else sem_prod_app (sem_prod_tuple tout) (@Ok _ _)
  in
  let f1 : sem_prod tin (sem_prod (sbool :: tout) (exec (sem_tuple tout))) :=
    sem_prod_app semi f0
  in
  add_arguments f1.

Definition mk_cond (idt : instr_desc_t) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ sbool :: (id_tout idt);
    id_in := (id_in idt) ++ E (id_nargs idt) :: (id_out idt);
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := mk_semi_cond (id_semi idt);
    id_nargs := (id_nargs idt).+1;
    id_args_kinds := map (fun x => x ++ [:: [:: CAcond ] ]) (id_args_kinds idt);
    id_eq_size := mk_cond_eq_size (id_eq_size idt);
    id_tin_narr :=
      mk_cond_tin_narr
        (is_true_true: is_not_sarr sbool)
        (id_tin_narr idt)
        (id_tout_narr idt);
    id_tout_narr := id_tout_narr idt;
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_wsize := reg_size;
    id_safe := [::];
    id_pp_asm := id_pp_asm idt;
  |}.
Arguments mk_cond : clear implicits.


(* -------------------------------------------------------------------- *)
(* Shift transformations.
 * Instruction descriptions are defined without optionally shifted registers.
 * The following transformation adds a shift argument to an instruction
 * and updates the semantics and the rest of the fields accordingly.
 *)

Definition mk_semi_shifted
  {A} (sk : shift_kind) (semi : sem_prod [:: sreg; sreg ] (exec A)) :
  sem_prod [:: sreg; sreg; sword8 ] (exec A) :=
  fun wn wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi wn (shift_op sk wm sham).

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

#[ local ]
Lemma mk_shifted_tin_narr {A} {p : A -> bool} {x} {xs : seq A} :
  p x
  -> all p xs
  -> all p (xs ++ [:: x ]).
Proof.
  move=> Hx Hxs.
  apply: all_catP;
    first done.
  by apply/andP.
Qed.

Definition mk_shifted (sk : shift_kind) (idt : instr_desc_t) semi' :
  instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := (id_tin idt) ++ [:: sword8 ];
    id_in := (id_in idt) ++ [:: E (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm reg_size] ]) (id_args_kinds idt);
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_tin_narr :=
      mk_shifted_tin_narr
        (is_true_true: is_not_sarr sword8)
        (id_tin_narr idt);
    id_tout_narr := id_tout_narr idt;
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_wsize := reg_size;
    id_safe := [::];
    id_pp_asm := id_pp_asm idt;
  |}.
Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Printing. *)

Definition pp_arm_op
  (mn : arm_mnemonic) (opts : arm_options) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_arm_mnemonic mn; (* TODO_ARM: This is not used. *)
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (args_size opts, a)) args;
  |}.


(* -------------------------------------------------------------------- *)
(* Instruction semantics and description. *)

Section ARM_INSTR.

Context
  (opts : arm_options).

Definition arm_ADD_semi (wn wm : wreg_ty) : exec nzcvr_ty :=
  let res :=
    nzcvw_of_aluop
      (wn + wm)
      (wunsigned wn + wunsigned wm)%Z
      (wsigned wn + wsigned wm)%Z
  in
  ok res.

Definition arm_ADD_instr : instr_desc_t :=
  let mn := ADD in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: E 1; E 2 ];
      id_tout := sflags ++ [:: sreg ];
      id_out := rflags_ad ++ [:: E 0 ];
      id_semi := arm_ADD_semi;
      id_nargs := 3;
      id_args_kinds := reg_reg_reg_ak ++ reg_reg_imm_ak;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_wsize := reg_size;
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_AND_semi (wn wm : wreg_ty) : exec nzcvr_ty :=
  let res := wand wn wm in
  ok (:: Some (NF_of_word res)
       , Some (ZF_of_word res)
       , TODO_ARM (* FIXME: C depends on the shift. *)
       , TODO_ARM (* FIXME: V should be unchanged. *)
       & res
     ).

Definition arm_AND_instr : instr_desc_t :=
  let mn := AND in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sreg; sreg ];
      id_in := [:: E 1; E 2 ];
      id_tout := sflags ++ [:: sreg ]; (* FIXME: Does not set V. *)
      id_out := rflags_ad ++ [:: E 0 ]; (* FIXME: Does not set V. *)
      id_semi := arm_AND_semi;
      id_nargs := 3;
      id_args_kinds := reg_reg_reg_ak ++ reg_reg_imm_ak;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_wsize := reg_size;
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  let x :=
    if has_shift opts is Some sk
    then mk_shifted sk x (mk_semi_shifted sk (id_semi x))
    else x
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_MOV_semi {sz : wsize} (wn : word sz) :
  exec (sem_tuple (sflags ++ [:: sword sz ])) :=
  ok (nzcvw_of_aluop wn (wunsigned wn) (wsigned wn)).

Definition arm_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let sz := args_size opts in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := [:: sword sz ];
      id_in := [:: E 1 ];
      id_tout := sflags ++ [:: sword sz ];
      id_out := rflags_ad ++ [:: E 0 ];
      id_semi := arm_MOV_semi;
      id_nargs := 2;
      id_args_kinds := reg_reg_ak ++ reg_imm_ak;
      id_eq_size := refl_equal;
      id_tin_narr := refl_equal;
      id_tout_narr := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_arm_mnemonic mn);
      id_wsize := reg_size;
      id_safe := [::];
      id_pp_asm := pp_arm_op mn opts;
    |}
  in
  if set_flags opts
  then x
  else drop_nzcv x.

Definition arm_LDR_semi (wn : wreg_ty) : exec wreg_ty :=
  ok wn.

Definition arm_LDR_instr : instr_desc_t :=
  let mn := LDR in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg ];
    id_in := [:: E 1 ];
    id_tout := [:: sreg ];
    id_out := [:: E 0 ];
    id_semi := arm_LDR_semi;
    id_nargs := 2;
    id_args_kinds := reg_addr_ak;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_wsize := reg_size;
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

Definition arm_STR_semi (wn : wreg_ty) : exec wreg_ty :=
  ok wn.

Definition arm_STR_instr : instr_desc_t :=
  let mn := STR in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg ];
    id_in := [:: E 1 ];
    id_tout := [:: sreg ];
    id_out := [:: E 0 ];
    id_semi := arm_STR_semi;
    id_nargs := 2;
    id_args_kinds := reg_addr_ak;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_arm_mnemonic mn);
    id_wsize := reg_size;
    id_safe := [::];
    id_pp_asm := pp_arm_op mn opts;
  |}.

End ARM_INSTR.


(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition mn_desc (mn : arm_mnemonic) : arm_options -> instr_desc_t :=
  match mn with
  | ADD => arm_ADD_instr
  | AND => arm_AND_instr
  | MOV => arm_MOV_instr
  | LDR => arm_LDR_instr
  | STR => arm_STR_instr
  | _ => TODO_ARM
  end.

Definition arm_instr_desc (o : arm_op) : instr_desc_t :=
  let '(ARM_op mn opts) := o in
  let x := mn_desc mn opts in
  if is_conditional opts
  then mk_cond x
  else x.

Definition arm_prim_string : seq (string * prim_constructor arm_op) :=
  let mk_prim mn sf ic hs :=
    let opts :=
      {|
        args_size := reg_size;
        set_flags := sf;
        is_conditional := ic;
        has_shift := hs;
      |}
    in
    ARM_op mn opts
  in
  map (fun mn => (string_of_arm_mnemonic mn, PrimARM (mk_prim mn))) cenum.

Instance arm_op_decl : asm_op_decl arm_op :=
  {|
    instr_desc_op := arm_instr_desc;
    prim_string := arm_prim_string;
  |}.


(* -------------------------------------------------------------------- *)
(* Miscellaneous functions. *)

Definition load_op_of_wsize (ws : wsize) : option arm_mnemonic :=
  match ws with
  | U8 => Some TODO_ARM
  | U16 => Some TODO_ARM
  | U32 => Some LDR
  | U64 => Some TODO_ARM
  | U128 => None
  | U256 => None
  end.

Definition store_op_of_wsize (ws : wsize) : option arm_mnemonic :=
  match ws with
  | U8 => Some TODO_ARM
  | U16 => Some TODO_ARM
  | U32 => Some STR
  | U64 => Some TODO_ARM
  | U128 => None
  | U256 => None
  end.
