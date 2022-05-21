From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.

Require Import utils.

Require Import
  arm_decl
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma mn_desc_is_conditional mn sf ic hs ic' :
  let opts :=
    {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
  in
  let opts' :=
    {| set_flags := sf; is_conditional := ic'; has_shift := hs; |}
  in
  mn_desc mn opts = mn_desc mn opts'.
Proof.
  case: mn => //=.

  (* Should be done by this point. *)
  all:
    match goal with
    | [|- TODO_ARM _ _ = TODO_ARM _ _ ] => exact: TODO_ARM_PROOF
    end.
Qed.

(* Comparison instructions ignore [set_flags]. *)
Lemma cmpmn_opts mn sf ic hs sf' :
  mn \in comparison_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf'; is_conditional := ic; has_shift := hs; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof.
  case: mn => //=.

  (* Should be done by this point. *)
  all: move=> _.
  all:
    match goal with
    | [|- TODO_ARM _ _ = TODO_ARM _ _ ] => exact: TODO_ARM_PROOF
    end.
Qed.

(* Memory instructions ignore [set_flags] and [has_shift]. *)
Lemma memmn_opts mn sf ic hs sf' hs' :
  mn \in memory_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf'; is_conditional := ic; has_shift := hs'; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof.
  case: mn => //=.

  (* Should be done by this point. *)
  all: move=> _.
  all:
    match goal with
    | [|- TODO_ARM _ _ = TODO_ARM _ _ ] => exact: TODO_ARM_PROOF
    end.
Qed.
