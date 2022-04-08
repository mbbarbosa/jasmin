From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.

Require Import
  arm_decl
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma mn_desc_args_size
  mn opt_sz opt_sf opt_cond opt_hs opt_sz' opt_cond' :
  let opts :=
    {|
      args_size := opt_sz;
      set_flags := opt_sf;
      is_conditional := opt_cond;
      has_shift := opt_hs;
    |}
  in
  let opts' :=
    {|
      args_size := opt_sz';
      set_flags := opt_sf;
      is_conditional := opt_cond';
      has_shift := opt_hs;
    |}
  in
  mn_desc mn opts = mn_desc mn opts'.
Proof.
  case: mn => //=.
  all: try match goal with
           | [|- TODO_ARM _ = TODO_ARM _ ] => exact: TODO_ARM
           end.
  (* Should be done by this point. *)

  all: exact: TODO_ARM.
Qed.
