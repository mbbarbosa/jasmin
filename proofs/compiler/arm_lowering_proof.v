From mathcomp Require Import
  all_ssreflect
  all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz.

Require Import
  compiler_util
  expr
  lowering
  lowering_lemmas
  psem
  utils.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_instr_decl_lemmas
  arm_sem
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Context
  {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
  {eft : eqType}
  {pT : progT eft}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool).

Context
  (fvars_correct : arm_fvars_correct fv (p_funcs p)).

(* Fix parameters. *)
Notation lower_Pvar := (lower_Pvar is_var_in_memory).
Notation lower_pexpr := (lower_pexpr is_var_in_memory).
Notation lower_i := (lower_i is_var_in_memory).
Notation lower_cmd :=
  (lower_cmd (fun _ _ _ _ => lower_i) options warning fv is_var_in_memory).
Notation lower_prog :=
  (lower_prog (fun _ _ _ _ => lower_i) options warning fv is_var_in_memory).

Notation p' := (lower_prog p).

Definition fvars : Sv.t :=
  Sv.empty.

Lemma fvars_empty xs : disjoint xs fvars.
Proof.
  apply/Sv.is_empty_spec. SvD.fsetdec.
Qed.

Definition eq_fv s0 s1 := estate_eq_except fvars s0 s1.

#[ local ]
Definition Pc (s0 : estate) (c : cmd) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
         sem p' ev s0' (lower_cmd c) s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pi (s0 : estate) (i : instr) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
         sem p' ev s0' (lower_i i) s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pi_r (s0 : estate) (i : instr_r) (s1 : estate) :=
  forall ii, Pi s0 (MkI ii i) s1.

#[ local ]
Definition Pfor
  (i : var_i) (rng : seq Z) (s0 : estate) (c : cmd) (s1 : estate) :=
  forall s0',
    eq_fv s0' s0
    -> exists s1',
         sem_for p' ev i rng s0' (lower_cmd c) s1' /\ eq_fv s1' s1.

#[ local ]
Definition Pfun
  scs0 (m0 : mem) (fn : funname) (vargs : seq value) scs1 (m1 : mem) (vres : seq value) :=
  sem_call p' ev scs0 m0 fn vargs scs1 m1 vres.

Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> ? s1 heq.
  exists s1.
  split.
  - exact: Eskip p' ev s1.
  - exact: heq.
Qed.

Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hpi _ hpc.
  move=> s1' hs1'.
  have [s2' [hsem_s2' hs2']] := hpi _ hs1'.
  have [s3' [hsem_s3' hs3']] := hpc _ hs2'.
  exists s3'.
  split.
  - exact: sem_app hsem_s2' hsem_s3'.
  - exact: hs3'.
Qed.

Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ hi. exact: hi ii.
Qed.

(* -------------------------------------------------------------------- *)
(* Lowering of assignments. *)

Lemma sem_i_lower_store s0 s0' s1' ws ws' e aop es (w : word ws') lv tag :
  (ws <= ws')%CMP
  -> eq_fv s0' s0
  -> sem_pexpr (p_globs p) s0 e = ok (Vword w)
  -> write_lval (p_globs p) lv (Vword (zero_extend ws w)) s0' = ok s1'
  -> lower_store ws e = Some (aop, es)
  -> sem_i p' ev s0' (Copn [:: lv ] tag (Oarm aop) es) s1'.
Proof.
  move=> hws hs0' hsem hwrite.
  rewrite /lower_store.
  elim hop: store_op_of_wsize => [op|] //.
  case: e hsem => [||| gx ||||||| ty' c e0 e1] // hsem [? ?];
    subst aop es.

  all: apply Eopn.
  all: rewrite /sem_sopn /=.
  all: move: hsem => /(eeq_exc_sem_pexpr (fvars_empty _) hs0') {hs0'} /=.

  move=> -> /=.
  all: cycle 1.

  t_xrbindP=> /=.
  move=> b v' ->.
  t_of_val.
  case: b => vw0 v0 -> hw0 vw1 v1 -> hw1 ? /=.

  (* Three cases:
     1. Conditional execution, condition is true.
     2. Conditional execution, condition is false.
     3. Unconditional execution. *)

  subst vw0.
  have [ws0 [w0 [? /truncate_wordP [hws0 ?] ->]]] := truncate_valI hw0;
    subst w ty'.
  move: hw1.
  t_truncate_val.
  move=> _ {vw1}.
  all: cycle 1.

  subst vw1.
  have [ws1 [w1 [? /truncate_wordP [hws1 ?] ->]]] := truncate_valI hw1;
    subst w ty'.
  move: hw0.
  t_truncate_val.
  move=> _ {vw0}.
  all: cycle 1.

  all: case: ws hws hwrite hop => //= hws hwrite [?]; subst op.
  all: rewrite /exec_sopn /sopn_sem /=.
  all: rewrite /truncate_word.

  rewrite hws /=.
  2-3: rewrite (cmp_le_trans hws hws0) (cmp_le_trans hws hws1) /=.
  2-3: rewrite -(zero_extend_idem _ hws) {hws}.

  all: by rewrite hwrite.
Qed.

Lemma lower_PvarP s gx ws ws' (w : word ws') aop es :
  (ws <= ws')%CMP
  -> sem_pexpr (p_globs p) s (Pvar gx) = ok (Vword w)
  -> lower_Pvar ws gx = Some (aop, es)
  -> exists2 vs,
       sem_pexprs (p_globs p) s es = ok vs
       & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ].
Proof.
  move=> hws /= hget.
  rewrite /lower_Pvar.
  case: is_var_in_memory.
  all: case: ws hws => //= hws [? ?]; subst aop es.
  all: rewrite /= hget {hget} /=.
  all: eexists; first reflexivity.
  all: rewrite /exec_sopn /=.
  all: by rewrite /truncate_word hws.
Qed.

Lemma lower_PloadP s x e ws ws' (w : word ws') aop es :
  sem_pexpr (p_globs p) s (Pload ws x e) = ok (Vword w)
  -> lower_Pload ws x e = Some (aop, es)
  -> exists2 vs,
       sem_pexprs (p_globs p) s es = ok vs
       & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ].
Proof.
  rewrite /sem_pexpr /= -/(sem_pexpr _ s e).
  t_xrbindP.
  move=> wbase vbase hget; t_of_val.
  move=> woff voff hsem; t_of_val.
  move=> wres hread ?; subst ws'.
  move=> [?]; subst wres.
  case: ws w hread => // w hread [? ?]; subst aop es.
  all: rewrite /sem_pexprs /=.
  all: rewrite hget {hget} /=.
  all: rewrite hsem {hsem} /=.
  all: rewrite /truncate_word hws hws0 {hws hws0} /=.
  all: rewrite hread {hread} /=.
  all: eexists; first reflexivity.
  all: done.
Qed.

Lemma lower_Papp1P s op e ws ws' (w : word ws') aop es :
  (ws <= ws')%CMP
  -> sem_pexpr (p_globs p) s (Papp1 op e) = ok (Vword w)
  -> lower_Papp1 ws op e = Some (aop, es)
  -> exists2 vs,
       sem_pexprs (p_globs p) s es = ok vs
       & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ].
Proof.
  move=> hws.
  rewrite /sem_pexpr /= -/(sem_pexpr _ s e).
  t_xrbindP.
  move=> v hsem hw.

  rewrite /lower_Papp1.
  case: ws hws => // hws'.
  case: op hw => [[]||||||] // hw [? ?]. subst aop es.

  rewrite /=.
  rewrite hsem {hsem} /=.
  rewrite hw {hw} /=.

  eexists; first reflexivity.

  rewrite /exec_sopn /=.
  by rewrite /truncate_word hws' {hws'}.
Qed.

Lemma get_arg_shiftP_aux z :
  (0 <= z <= 31)%Z
  -> wunsigned (wand (wrepr U8 z) (wrepr U8 31)) = wunsigned (wrepr U8 z).
Proof.
  move=> hrange.
  change 31%Z with (2 ^ Z.of_nat 5 - 1)%Z.
  rewrite wand_modulo.
  rewrite wunsigned_repr_small.
  - apply Z.mod_small. lia.
  change (wbase U8) with 256%Z.
  lia.
Qed.

Lemma get_arg_shiftP s e ws ws0 (w : word ws0) e' sh n :
  sem_pexpr (p_globs p) s e = ok (Vword w)
  -> get_arg_shift ws e = Some (e', sh, n)
  -> exists ws1 (wbase : word ws1) (wsham : word U8),
       [/\ (ws <= ws1)%CMP
         , sem_pexpr (p_globs p) s e' = ok (Vword wbase)
         , sem_pexpr (p_globs p) s n = ok (Vword wsham)
         & w = shift_op sh (zero_extend ws0 wbase) (wunsigned wsham)
       ].
Proof.
  case: e => // op.
  move=> [] //= gx.
  move=> [] //.
  move=> [[]||||||] //.
  move=> [] // z.

  rewrite /=.
  t_xrbindP=> vbase hget hsem.

  case: ws w hsem => // w hsem.
  case: op hsem => // [[] | [|[]] | [|[]]] //= hsem.
  all: case: ifP => // /andP [] /ZleP hlo /ZleP hhi.
  all: move=> [? ? ?]; subst e' sh n.
  all: rewrite /sem_pexpr /=.
  all: rewrite hget {hget} /=.
  all: have /= [wbase [wsham [wres []]]] := sem_sop2I hsem.
  all: t_of_val.
  all: rewrite /truncate_word.
  all: rewrite wsize_le_U8 /=.
  all: rewrite /mk_sem_sop2 /=.
  all: move=> [?] [?] [?]; subst wsham wres ws0.
  all: move=> [?]; subst w.
  all: eexists; eexists; eexists; split.
  all: try reflexivity.
  all: try done.
  all: match goal with
       | [ |- ?f _ _ = _ _ _ ] => rewrite /f /=
       end.
  all: rewrite /sem_shift /=.
  all: f_equal.
  all: rewrite zero_extend_u.
  all: apply get_arg_shiftP_aux.
  all: lia.
Qed.

Lemma zero_extend_shift_op sh sz sz' (x : word sz') i :
  (sz <= sz')%CMP
  -> zero_extend sz (shift_op sh x i) = shift_op sh (zero_extend sz x) i.
Proof.
  case: sh => /=.
  - exact: zero_extend_wshl.
  - exact: TODO_ARM_PROOF.
  - exact: TODO_ARM_PROOF.
  - exact: TODO_ARM_PROOF.
  - exact: TODO_ARM_PROOF.
Qed.

Lemma lower_Papp2P s op e0 e1 ws ws' (w : word ws') aop es :
  (ws <= ws')%CMP
  -> sem_pexpr (p_globs p) s (Papp2 op e0 e1) = ok (Vword w)
  -> lower_Papp2 ws op e0 e1 = Some (aop, es)
  -> exists2 vs,
       sem_pexprs (p_globs p) s es = ok vs
       & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ].
Proof.
  move=> hws.
  rewrite /sem_pexpr /= -!/(sem_pexpr _ s _).
  t_xrbindP.
  move=> v0 hsem0 v1 hsem1 hw.
  rewrite /lower_Papp2.
  elim harg: get_arg_shift => [[[e1' sh] n]|]; first last.
  all: case: ws hws harg => hws harg.
  all: case: op hw => //= [[|[]] | []] //.
  all: move=> hw [<- <-] {aop es} /=.
  all: rewrite hsem0 /=.
  all: have /= [w0 [w1 [w2 []]]] := sem_sop2I hw.
  all: t_of_val.
  all: t_of_val.
  all: rewrite /mk_sem_sop2 /=.
  all: move=> [?] [?]; subst ws' w2.
  all: move=> [?]; subst w.

  (* Non-shift case. *)
  1-2: rewrite hsem1 /=.
  1-2: exists [:: Vword w3; Vword w0 ]; first done.
  1-2: rewrite /exec_sopn /=.
  1-2: rewrite /truncate_word hws0 hws1 /=.
  1-2: by rewrite zero_extend_u.

  all: have [ws2 [wbase [wsham [hws2 hseme1' hsemn ?]]]] :=
         get_arg_shiftP hsem1 harg;
         subst w0.
  all: rewrite hseme1' {hseme1'} /=.
  all: rewrite hsemn {hsemn} /=.
  all: eexists; first reflexivity.
  all: rewrite /exec_sopn /=.
  all: rewrite /sopn_sem /=.
  all: rewrite /truncate_word hws0 hws2 {hws0 hws2} /=.
  all: rewrite (zero_extend_shift_op _ _ _ hws1).
  all: rewrite !zero_extend_u.
  all: by rewrite (zero_extend_idem _ hws1).
Qed.

Lemma lower_PifP s c e0 e1 ws ws0 (w : word ws0) aop es :
  (forall aop' es',
      lower_pexpr ws e0 = Some (aop', es')
      -> exists2 vs,
           sem_pexprs (p_globs p) s es' = ok vs
           & exec_sopn (Oarm aop') vs = ok [:: Vword (zero_extend ws w) ])
  -> sem_pexpr (p_globs p) s (Pif (sword ws) c e0 e1) = ok (Vword w)
  -> lower_Pif (lower_pexpr ws) c e0 e1 = Some (aop, es)
  -> exists2 vs,
       sem_pexprs (p_globs p) s es = ok vs
       & exec_sopn (Oarm aop) vs = ok [:: Vword (zero_extend ws w) ].
Proof.
  move=> hind.
  rewrite /sem_pexpr /truncate_val /= -!/(sem_pexpr _ s _).
  t_xrbindP.
  move=> b ? hsemc; t_of_val.
  move=> ? ? hsemw0 ?; t_of_val=> <-.
  move=> ? ? hsemw1 ?; t_of_val=> <-.
  move=> hw.

  rewrite /lower_Pif.
  elim he0: lower_pexpr => [[[op opts] es0]|] //.
  move=> [<- <-] {aop es}.

  have [vs' hsem hexec] := hind _ _ he0.
  clear hind.
  rewrite /sem_pexprs /=.
  rewrite mapM_cat.
  rewrite -2![mapM _ _]/(sem_pexprs _ _ _).
  rewrite hsem {hsem} /=.
  rewrite hsemc {hsemc} /=.
  rewrite hsemw1 {hsemw1} /=.
  eexists; first reflexivity.

  case: b hw.
  all: move=> -[?]; subst ws.
  all: move=> -[?]; subst w.
  all: exact: TODO_ARM_PROOF. (* How to continue? *)
Qed.

Lemma sem_i_lower_pexpr s0 s0' s1' ws ws' e aop es (w : word ws') lv tag :
  (ws <= ws')%CMP
  -> eq_fv s0' s0
  -> sem_pexpr (p_globs p) s0 e = ok (Vword w)
  -> write_lval (p_globs p) lv (Vword (zero_extend ws w)) s0' = ok s1'
  -> lower_pexpr ws e = Some (aop, es)
  -> sem_i p' ev s0' (Copn [:: lv ] tag (Oarm aop) es) s1'.
Proof.
  move=> hws hs0' hsem hwrite.
  move: s0 aop es tag hws hs0' hsem.
  elim: e
    => [||| gx ||| ws0 x e _ | op e _ | op e0 _ e1 _ || ty c _ e0 he0 e1 _] //.

  all: move=> s0 aop es tag hws hs0' hsem /= hlower.
  all: apply Eopn.
  all: rewrite /sem_sopn /=.
  all: move: hsem => /(eeq_exc_sem_pexpr (fvars_empty _) hs0') hsem.

  have := lower_PvarP hws hsem hlower.
  all: cycle 1.

  move: hlower.
  case: ifP => // /eqP ? hlower; subst ws0.
  have := lower_PloadP hsem hlower.
  all: cycle 1.

  have := lower_Papp1P hws hsem hlower.
  all: cycle 1.

  have := lower_Papp2P hws hsem hlower.
  all: cycle 1.

  move: hlower.
  case: ty hsem => // ws0 hsem.
  case: ifP => // /eqP ? hlower; subst ws0.

 (* Is this the way? *)
  have := lower_PifP TODO_ARM_PROOF hsem hlower.
  all: cycle 1.

  all: move=> [? hsem' hexec].
  all: rewrite hsem' {hsem} /=.
  all: rewrite hexec {hexec} /=.
  all: by rewrite hwrite.
Qed.

Lemma lower_cassgnP s0 lv tag ty e v v' s0' s1' lvs op es :
  sem_pexpr (p_globs p) s0 e = ok v
  -> truncate_val ty v = ok v'
  -> write_lval (p_globs p) lv v' s0' = ok s1'
  -> eq_fv s0' s0
  -> sem_i p' ev s0' (Cassgn lv tag ty e) s1'
  -> lower_cassgn is_var_in_memory lv ty e = Some (lvs, op, es)
  -> sem_i p' ev s0' (Copn lvs tag op es) s1'.
Proof.
  move=> hsem htruncate hwrite hs0' hassgn.
  rewrite /lower_cassgn.
  case: ty htruncate hassgn => [|||ws] // htruncate hasssgn.
  move: htruncate.
  rewrite /truncate_val.
  t_xrbindP=> ?.
  t_of_val.
  move=> ?; subst v'.

  case hlv: is_lval_in_memory.
  - elim hlstore: lower_store => [[op' es']|] //.
    move=> [? ? ?]. subst lvs op es.
    exact: sem_i_lower_store _ hws hs0' hsem hwrite hlstore.
  - elim hlpexpr: lower_pexpr => [[op' es']|] //.
    move=> [? ? ?]. subst lvs op es.
    exact: sem_i_lower_pexpr _ hws hs0' hsem hwrite hlpexpr.
Qed.


(* -------------------------------------------------------------------- *)

Lemma lower_copnP s0' s1' lvs tag op es lvs' op' es' :
  sem_i p' ev s0' (Copn lvs tag op es) s1'
  -> lower_copn lvs op es = Some (lvs', op', es')
  -> sem_i p' ev s0' (Copn lvs' tag op' es') s1'.
Proof.
  move=> hcopn.
  rewrite /lower_copn.
  case: op hcopn => // [[[[] aop]|]] //.
  move: aop => [mn opts] hcopn.
  case: ifP => // hmn.
  move=> [? ? ?]. subst lvs' op' es'.
  exact: hcopn.
Qed.


(* -------------------------------------------------------------------- *)

Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s0 s1 lv tag ty e v v' hsem htruncate hwrite.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hwrite' hs1']] := eeq_exc_write_lval (fvars_empty _) hs0' hwrite.
  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI.

  have hassgn : sem_i p' ev s0' (Cassgn lv tag ty e) s1'.
  - apply: Eassgn.
    + exact: eeq_exc_sem_pexpr (fvars_empty _) hs0' hsem.
    + exact: htruncate.
    + exact: hwrite'.

  case h : lower_cassgn => [[[lvs op] es]|].
  - exact: lower_cassgnP hsem htruncate hwrite' hs0' hassgn h.
  - exact: hassgn.
Qed.

Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s0 s1 tag op lvs es hsem.
  move=> ii s0' hs0'.
  rewrite /=.

  move: hsem.
  apply: rbindP=> vs.
  apply: rbindP=> xs hsem hexec hwrite0.

  have [s1' [hwrite1 hs1']] := eeq_exc_write_lvals (fvars_empty _) hs0' hwrite0.
  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI.

  have hcopn : sem_i p' ev s0' (Copn lvs tag op es) s1'.
  - apply Eopn.
    rewrite /sem_sopn /=.
    rewrite (eeq_exc_sem_pexprs (fvars_empty _) hs0' hsem) /=.
    rewrite hexec /=.
    exact: hwrite1.

  case h : lower_copn => [[[lvs' op'] es']|].
  - exact: lower_copnP hcopn h.
  - exact: hcopn.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hw.
  move=> ii s1' hs1' /=.

  have hes' := eeq_exc_sem_pexprs (fvars_empty _) hs1' hes.
  have hs1'w: eq_fv (with_scs (with_mem s1' m) scs) (with_scs (with_mem s1 m) scs). 
  + by rewrite /eq_fv /estate_eq_except /=; case: hs1' => ?? ->.
  have [s2' [hw' hs2']] := eeq_exc_write_lvals (fvars_empty _) hs1'w hw.
  exists s2'; split => //.
  apply sem_seq1; constructor; econstructor; eauto.
  by case: hs1' => -> -> _.
Qed.

Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hsem_pexpr _ hc.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hsem' hs1']] := hc s0' hs0'.
  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eif_true.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs0' hsem_pexpr.
  - exact: hsem'.
Qed.

Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hsem_pexpr _ hc.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hsem' hs1']] := hc s0' hs0'.
  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI. apply: Eif_false.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs0' hsem_pexpr.
  - exact: hsem'.
Qed.

Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 e c1 hsem0 hc0 hsem_pexpr _ hc1 _ hwhile.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hsem0' hs1']] := hc0 s0' hs0'.
  have [s2' [hsem1' hs2']] := hc1 s1' hs1'.
  have [s3' [hsem' hs3']] := hwhile ii s2' hs2'.

  exists s3'.
  split; last exact: hs3'.
  apply: sem_seq1. apply: EmkI. apply: Ewhile_true.
  - rewrite cats0. exact: hsem0'.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs1' hsem_pexpr.
  - exact: hsem1'.
  - have [? [hsemI hsem3']] := semE hsem'.
    rewrite -(semE hsem3') in hsemI.
    have hsemi := sem_IE hsemI.
    exact: hsemi.
Qed.

Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 al c0 e c1 hsem0 hc0 hsem_pexpr.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hsem0' hs1']] := hc0 s0' hs0'.

  exists s1'.
  split; last exact hs1'.
  apply: sem_seq1. apply: EmkI. apply: Ewhile_false.
  - rewrite cats0. exact: hsem0'.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs1' hsem_pexpr.
Qed.

Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s0 s1 i d lo hi c vlo vhi hlo hhi _ hfor.
  move=> ii s0' hs0'.
  rewrite /=.

  have [s1' [hsem' hs1']] := hfor s0' hs0'.

  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI. apply: Efor.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs0' hlo.
  - exact: eeq_exc_sem_pexpr (fvars_empty _) hs0' hhi.
  - exact: hsem'.
Qed.

Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s0 i c.
  move=> s0' hs0'.
  rewrite /=.

  exists s0'.
  split; last exact: hs0'.
  exact: EForDone.
Qed.

Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 i v vs c hwrite hsem hc hsem_for hfor.
  move=> s0' hs0'.
  rewrite /=.

  have hwrite' : write_lval (p_globs p) i v s0 = ok s1.
  - exact: hwrite.

  have [s1' [hwrite1 hs1']] := eeq_exc_write_lval (fvars_empty _) hs0' hwrite'.

  have [s2' [hsem2 hs2']] := hc _ hs1'.
  have [s3' [hsem3 hs3']] := hfor _ hs2'.

  exists s3'.
  split; last exact: hs3'.
  apply: EForOne.
  - exact: hwrite1.
  - exact: hsem2.
  - exact: hsem3.
Qed.

Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s0 scs0 m0 s1 inl_i ls fn args vargs vs hsem_pexprs _ hfun hwrite0.
  move=> ii s0' hs0'.
  rewrite /=.

  have hwith_s0' : eq_fv (with_scs (with_mem s0' m0) scs0) (with_scs (with_mem s0 m0) scs0).
  - split=> //. move: hs0' => [_ _ hvm0']. exact: hvm0'.

  have [s1' [hwrite0' hs1']] :=
    eeq_exc_write_lvals (fvars_empty _) hwith_s0' hwrite0.
  exists s1'.
  split; last exact: hs1'.
  apply: sem_seq1. apply: EmkI. apply: Ecall.
  - exact: eeq_exc_sem_pexprs (fvars_empty _) hs0' hsem_pexprs.
  - move: hs0' => [-> -> _]. exact: hfun.
  - exact: hwrite0'.
Qed.

Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs0 m0 scs1 m1 fn fd vargs vargs' s0 s1 s2 vres vres'.
  move=> hget htruncate_args hinit hwrite _ hc hres htruncate_res hscs hfin.

  have [s2' [hsem1 hs2']] := hc _ (eeq_excR fvars s1).

  apply: EcallRun.
  - by rewrite get_map_prog hget.
  - exact: htruncate_args.
  - exact: hinit.
  - exact: hwrite.
  - exact: hsem1.
  - rewrite -(sem_pexprs_get_var (p_globs p)).
    rewrite -(sem_pexprs_get_var (p_globs p)) in hres.
    exact: eeq_exc_sem_pexprs (fvars_empty _) hs2' hres.
  - exact: htruncate_res.
  - move: hs2' => [-> _ _]. done.
  - move: hs2' => [_ -> _]. exact: hfin.
Qed.

Theorem lower_callP
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  sem_call p ev scs mem f va scs' mem' vr ->
     sem_call (lower_prog p) ev scs mem f va scs' mem' vr.
Proof.
  exact (@sem_call_Ind
           _ _ _ _ _ _ _ _ p ev
           Pc Pi_r Pi Pfor Pfun
           Hskip
           Hcons
           HmkI
           Hassgn
           Hopn
           Hsyscall
           Hif_true Hif_false
           Hwhile_true Hwhile_false
           Hfor Hfor_nil Hfor_cons
           Hcall
           Hproc
           scs mem f va scs' mem' vr).
Qed.

End PROOF.
