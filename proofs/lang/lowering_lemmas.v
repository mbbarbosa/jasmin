From mathcomp Require Import all_ssreflect all_algebra.

Require Import expr low_memory psem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma subset_diff xs ys :
  disjoint xs ys -> Sv.Subset xs (Sv.diff xs ys).
Proof.
  move=> /Sv.is_empty_spec.
  SvD.fsetdec.
Qed.

Lemma disjoint_union_r xs ys zs :
  disjoint (Sv.union xs ys) zs -> disjoint xs zs /\ disjoint ys zs.
Proof.
  move=> /Sv.is_empty_spec H.
  split;
    apply/Sv.is_empty_spec;
    SvD.fsetdec.
Qed.


Section ESTATE_EQ_EXCEPT.

Context
  {pd : PointerData}
  {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

(* State equality up to a set of variables. *)
Definition estate_eq_except ys s1 s2 :=
  [/\ s1.(escs) = s2.(escs), s1.(emem) = s2.(emem) & s1.(evm) = s2.(evm) [\ ys]].

(* FIXME syscall : why it is needed to redeclare it here *)
(* note that in utils, it is CMorphisms.Proper, here it is Morpisms.Proper *)
#[global]
Instance and3_impl_morphism :
  Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and3 | 1.
Proof. apply and3_impl_morphism. Qed.

#[global]
Instance and3_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. apply and3_iff_morphism. Qed. 
(* END FIXME syscall *)

Lemma eeq_excR xs s :
  estate_eq_except xs s s.
Proof. done. Qed.

Lemma eeq_excS xs s0 s1 :
  estate_eq_except xs s0 s1
  -> estate_eq_except xs s1 s0.
Proof. by rewrite /estate_eq_except => -[-> -> ->]. Qed.

Lemma eeq_excT xs s0 s1 s2 :
  estate_eq_except xs s0 s1
  -> estate_eq_except xs s1 s2
  -> estate_eq_except xs s0 s2.
Proof. by rewrite /estate_eq_except => -[-> -> ->]. Qed.

Lemma eeq_exc_disjoint xs ys s0 s1 :
  disjoint xs ys
  -> estate_eq_except ys s0 s1
  -> [/\ escs s0 = escs s1, emem s0 = emem s1 & evm s0 =[ xs ] evm s1].
Proof.
  move=> Hdisj [-> -> Hvm]; split=> //.
  move=> x Hxxs.
  apply: Hvm => Hyys.
  rewrite /disjoint in Hdisj.
  apply Sv.is_empty_spec in Hdisj.
  SvD.fsetdec.
Qed.

(* The semantics of an expression in two states is the same if they only differ
 * in variables that don't appear in the expression.
 *)
Lemma eeq_exc_sem_pexprs gd xs es v s0 s1 :
  disjoint (read_es es) xs
  -> estate_eq_except xs s1 s0
  -> sem_pexprs gd s0 es = ok v
  -> sem_pexprs gd s1 es = ok v.
Proof.
  move=> Hdisj Heq.
  have [Hscs Hmem Hvm] := eeq_exc_disjoint Hdisj Heq.
  rewrite (read_es_eq_on gd Hvm).
  rewrite /with_vm.
  rewrite Hscs Hmem.
  by rewrite -(surj_estate s0).
Qed.

Lemma eeq_exc_sem_pexpr gd xs e v s0 s1 :
  disjoint (read_e e) xs
  -> estate_eq_except xs s1 s0
  -> sem_pexpr gd s0 e = ok v
  -> sem_pexpr gd s1 e = ok v.
Proof.
  move=> Hdisj Heq Hsem.

  have Hdisj' : disjoint (read_es [:: e ]) xs.
  - done.

  have Hsem' : sem_pexprs gd s0 [:: e ] = ok [:: v ].
  - by rewrite /= Hsem.

  have := eeq_exc_sem_pexprs Hdisj' Heq Hsem'.
  rewrite /=.
  by t_xrbindP => ? ? <-.
Qed.

(* If two states s0 and s0' are equal up to a set xs of variables,
 * and writing to different variables ls in s0 succeeds in s1,
 * then doing so in s0' succeeds in s1' and
 * s1' is equal to s1 up to xs.
 *
 *           s0 ------- write_lvals ls -------> s1
 *           |                                  |
 *           |                                  |
 *  estate_eq_except xs                estate_eq_except xs
 *           |                                  |
 *           |                                  |
 *           s0' ------ write_lvals ls -------> s1'
 *)
Lemma eeq_exc_write_lvals gd xs s0 s1 s0' ls vs :
  disjoint (vars_lvals ls) xs
  -> estate_eq_except xs s0' s0
  -> write_lvals gd s0 ls vs = ok s1
  -> exists s1',
      write_lvals gd s0' ls vs = ok s1' /\ estate_eq_except xs s1' s1.
Proof.
  move=> Hdisj.
  move: s0 s0' => [scs0 mem0 vm0] [scs0' mem0' vm0'].
  move=> [/= Hscs Hmem Hvm] Hwrite.
  subst scs0 mem0.

  have Hsub : Sv.Subset (read_rvs ls) (Sv.diff (read_rvs ls) xs).
  - rewrite /vars_lvals in Hdisj.
    have [Hdisj' _] := disjoint_union_r Hdisj.
    exact: subset_diff Hdisj'.

  have Hvm' : vm0 =[Sv.diff (read_rvs ls) xs] vm0'.
  - move=> x Hx. apply: vmap_eq_exceptS. apply: Hvm. SvD.fsetdec.

  have [vm1' [Hvm1' Hwrite']] := write_lvals_eq_on Hsub Hwrite Hvm'.

  exists (with_vm s1 vm1').
  split.
  - exact: Hwrite'.
  - split=> //.
    move=> x Hx /=.
    case Hxvrv : (Sv.mem x (vrvs ls)).
    + move: Hxvrv => /Sv_memP Hxvrv.
      rewrite Hvm1'; first done.
      SvD.fsetdec.
    move: Hxvrv => /Sv_memP Hxvrv.
    rewrite -(vrvsP Hwrite' Hxvrv).
    rewrite -(vrvsP Hwrite Hxvrv).
    exact: Hvm.
Qed.

Lemma eeq_exc_write_lval gd xs s0 s1 s0' l v :
  disjoint (vars_lval l) xs
  -> estate_eq_except xs s0' s0
  -> write_lval gd l v s0 = ok s1
  -> exists s1',
      write_lval gd l v s0' = ok s1' /\ estate_eq_except xs s1' s1.
Proof.
  move=> Hdisj Heq Hwrite.

  have Hdisj' : disjoint (vars_lvals [:: l ]) xs.
  - done.

  have Hwrite' : write_lvals gd s0 [:: l ] [:: v ] = ok s1.
  - by rewrite /= Hwrite.

  have [s1' [Hwrite1 Heq1]] := eeq_exc_write_lvals Hdisj' Heq Hwrite'.

  exists s1'.
  split.
  - move: Hwrite1. rewrite /=. by t_xrbindP => ? ? <-.
  - exact: Heq1.
Qed.

Lemma eeq_exc_get_gvar gd s0 s1 (x : gvar) vs :
  ~~ Sv.mem (gv x) vs
  -> estate_eq_except vs s0 s1
  -> get_gvar gd (evm s0) x = get_gvar gd (evm s1) x.
Proof.
  move=> /Sv_memP hx [hscs hmem hvm].
  rewrite /get_gvar /=.
  case: is_lvar; last done.
  rewrite /get_var /=.
  by rewrite (hvm _ hx).
Qed.

End ESTATE_EQ_EXCEPT.
