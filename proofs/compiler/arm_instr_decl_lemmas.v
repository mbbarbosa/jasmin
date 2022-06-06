From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.

Require Import psem.

Require Import
  arm_decl
  arm_extra
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
Proof. by case: mn. Qed.

Lemma ignore_set_flags mn sf ic hs sf' :
  mn \notin set_flags_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf'; is_conditional := ic; has_shift := hs; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof. by case: mn. Qed.

Lemma ignore_has_shift mn sf ic hs hs' :
  mn \notin has_shift_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs'; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof. by case: mn. Qed.
