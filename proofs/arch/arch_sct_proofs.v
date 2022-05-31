From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith
utils
strings wsize
memory_model
gen_map
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
syscall
arch_decl
label
values
word
asm_gen_proof
arch_sem
arch_sem_no_spec
arch_sct.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Public_only_less_than_Public : forall t, (t <= Public)%CMP -> t = Public.
Proof.
move=> t ht. by case: t ht=> //=.
Qed.

Lemma zero_extend_small_size : forall s sz sz' (w1: word s) (w2: word s),
(sz <= sz')%CMP -> 
zero_extend sz' w1 = zero_extend sz' w2 ->
zero_extend sz  w1 = zero_extend sz  w2.
Proof.
move=> s sz sz' w1 w2 hsz ht.
have hz := zero_extend_idem. move: (hz s sz sz' w1 hsz)=> <-.
move: (hz s sz sz' w2 hsz)=> <-. by rewrite ht /=.
Qed.

Section PROOFS.

Context {reg regx xreg rflag cond asm_op} {asm_d : asm reg regx xreg rflag cond asm_op}. 

Context (wt_cond : constraints -> env_t -> cond_t -> Sl.t -> bool).

Context (fn: funname).

Context (sec_ty_op : asm_op_t' -> sec_ty).

Lemma state_equiv_env_env' : forall c rho s1 s2 env env',
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
le_env c env env' ->
state_equiv rho s1 s2 env'. 
Proof.
move=> c rho [] m1 fn1 code1 ip1 [] m2 fn2 code2 ip2 env env' hequiv hvalid hle.
case: hequiv=> /= hcode hpc hrpc hmemequiv. case: hmemequiv=> /= hreg hregx hxreg hflag hmem; subst.
constructor; auto; rewrite /=; subst. constructor; auto; rewrite /=.
+ move=> r l ws hregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hr r)=> /= hle. rewrite hregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_reg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hregxty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hrx r)=> /= hle. rewrite hregxty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_regx env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). + by case: (e_regx env r)=> //=.
  move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hxregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hxr r)=> /= hle. rewrite hxregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_xreg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). + by case: (e_xreg env r)=> //=.
  move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> f l hfty hrho. rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hf f)=> /= hle. rewrite hfty /= in hle. rewrite /le_ws /= in hle.
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_flag env f) l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_flag env f = e_flag env f. + by auto. 
  by move: (hflag f (e_flag env f) henv hpub).
move=> pt l adr vp pts hwvp hvp hpty hrho i hi.
rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
move: (hm pt)=> /= hle. rewrite hpty /= in hle. rewrite /le_ws /= in hle.
inversion hvalid. case: H0=> hsecret hl. move: (hl (get_pt env pt) l hle)=> /= hl'.
rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
have henv : get_pt env pt = get_pt env pt. + by auto.
by move: (hmem pt (get_pt env pt) adr vp pts hwvp hvp henv hpub i hi).
Qed.                                                                                                                              

Lemma l_mem: forall l S S' S'',
Sl.mem l S ->
Sl.subset (Sl.add S' S) S'' ->
Sl.mem l S''.
Proof.
move=> l S S' S'' hmem hsub.
have hmem' := SlP.add_mem_3 S S' l hmem. 
by have hmem'' := SlP.subset_mem_2 (Sl.add S' S) S'' hsub l hmem'.
Qed.

Lemma l_subset: forall S S' S'',
Sl.subset (Sl.add S' S) S'' ->
Sl.mem S' S'' /\ Sl.subset S S''.
Proof.
move=> S S' S'' hsub. 
Admitted.

Lemma public_mem: forall S,
Sl.subset spublic S ->
Sl.mem public S.
Proof.
move=> S hsub. rewrite /spublic /= in hsub. 
have hmem : Sl.mem public (Sl.singleton public). + by auto.
by have := SlP.subset_mem_2 (Sl.singleton public) S hsub public hmem.
Qed.

Lemma type_prev_arg : forall c env a S ad pt ty sty s1 s2 rho v1 leak1 v2 leak2,
wt_arg_in wt_cond c env a S ad pt ty sty ->
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
eval_arg_in_v_leak s1.(asm_m) a ad ty = ok (v1, leak1) ->
eval_arg_in_v_leak s2.(asm_m) a ad ty = ok (v2, leak2) ->
(forall l, Sl.mem l S -> value_equiv v1 v2 (rho l) ty) /\ value_equiv v1 v2 sty ty /\ leak1 = leak2.
Proof.
move=> c env a S ad pt ty sty [] m1 fn' code1 ip1 [] m2 fn'' code2 ip2 rho 
v1 leak1 v2 leak2 hwt hequiv hvalid hstep hstep'.
case: hequiv=> /= hcode hip hrip hmemequiv. 
case: hmemequiv=> /= hreg hregx hxreg hflag hmem; subst.
case: hvalid=> hpub [hsec hle'].
inversion hstep; inversion hstep'; subst; move=> {hstep} {hstep'}.
rewrite /eval_arg_in_v /= in H0 H1. 
case: ad H0 H1 hwt=> //=.
(* implicit *)
+ move=> i H0 H1 hwt. case: i H0 H1 hwt=> //=.
  (* implicit flag *)
  + move=> f. t_xrbindP=> b hset hb hleak b' hset' hb' hleak' hle; subst.
    rewrite /st_get_rflag in hset hset'. 
    rewrite /value_equiv. split=> //=. 
    + move=> l hl hrho.
      move: (hflag f (e_flag env f) erefl)=> hflag'.
      rewrite /le_all in hle. rewrite /is_le in hle'. have l_mem' := l_mem hl hle.
      move: (hle' (e_flag env f) l l_mem')=> hle1. rewrite hrho /= in hle1. 
      apply Public_only_less_than_Public in hle1.
      move: (hflag f (e_flag env f) erefl hle1)=> {hreg} hreg. rewrite hreg in hset hset'.
      case: (asm_flag m2 f) hset hset'=> //=.
      by move=> b'' [] hb'' [] hb'''; subst. 
   split=> //=. move=> hsty.
   rewrite /of_val /=. case: ty=> //=.
   move: (hflag f (e_flag env f) erefl)=> hflag'.
   rewrite /le_all in hle. apply l_subset in hle; subst.
   rewrite /= in hle. case: hle=> hle1 hle2.  
   rewrite /is_le in hle'. move: (hle' (e_flag env f) public hle1)=> /= hrho'.
   rewrite hpub in hrho'. apply Public_only_less_than_Public in hrho'.
   move: (hflag' hrho')=> hasm. rewrite -hasm in hset'. case: (asm_flag m1 f) hset hset'=> //=.
   by move=> b'' [] <- [] <-.
  (* implicit reg *)
  move=> r [] hr hl [] hr' hl'; subst. case: ty=> //=.
  move=> ws hregty. rewrite /value_equiv. split=> //=. 
  + move=> l hl hrho. 
    have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
    rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
    rewrite /le_all in hle. rewrite /is_le in hle'. have l_mem' := l_mem hl hle.
    move: (hle' (e_reg env r).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
    apply Public_only_less_than_Public in hle1.
    move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1)=> {hreg} hreg. 
    rewrite /of_val /= /truncate_word /=. case: ifP=> //= hsz. 
    have hreg' := zero_extend_small_size hws hreg. by rewrite hreg'.
  split=> //=. move=> hsty. have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
  rewrite /le_all in hle. apply l_subset in hle; subst. case: hle=> hle1 hle2.
  rewrite /is_le in hle'. move: (hle' (e_reg env r).1 public hle1)=> hle1'. 
  rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1')=> {hreg} hreg. 
  rewrite /truncate_word /=. case: ifP=> //= hsz. 
  have hreg' := zero_extend_small_size hws hreg. by rewrite hreg'.
(* explicit *)
move=> ak n o /=. case: (onth a n)=> //=.
move=> asm_arg /=. t_xrbindP=> ut hassert heval ut' hassert' heval' hwt.
rewrite /eval_asm_arg /= in heval heval'. rewrite /wt_asm_arg in hwt.
case: asm_arg hassert heval hassert' heval' hwt=> //=.
(* condt *)
+ move=> condt /= hassert. t_xrbindP=> b heval hb hleak hassert' b' heval' hb' hleak'; subst.
  case: ty=> //=. move=> hwt. rewrite /eval_cond_mem /st_get_rflag in heval heval'. 
  rewrite /value_equiv. split=> //=. move=> l hl hrho.
  + admit.
  split=> //=. move=> hsty. admit.
(* Imm *)
+ move=> ws s hassert. case: ty=> //=.
  by move=> w [] hv1 hleak1 hassert' [] hv2 hleak2 hle''; subst.
(* Reg *)
+ move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
  move=> ws hregty. rewrite /value_equiv. split=> //=.
  + move=> l hl hrho. 
    have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
    rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
    rewrite /le_all in hle. rewrite /is_le in hle'. have l_mem' := l_mem hl hle.
    move: (hle' (e_reg env r).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
    apply Public_only_less_than_Public in hle1.
    move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1)=> {hreg} hreg. 
    rewrite /of_val /= /truncate_word /=. case: ifP=> //= hsz. 
    have hreg' := zero_extend_small_size hws hreg. by rewrite hreg'.
  split=> //=. move=> hsty. have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
  rewrite /le_all in hle. apply l_subset in hle; subst. case: hle=> hle1 hle2.
  rewrite /is_le in hle'. move: (hle' (e_reg env r).1 public hle1)=> hle1'. 
  rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1')=> {hreg} hreg. 
  rewrite /truncate_word /=. case: ifP=> //= hsz. 
  have hreg' := zero_extend_small_size hws hreg. by rewrite hreg'.
(* Regx *)
+ move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
  move=> ws hregxty. rewrite /value_equiv. split=> //=.
  + move=> l hl hrho. 
    have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). 
    + by case: (e_regx env r)=> //=.
    rewrite henv /= in hregxty. move: hregxty. move=> /andP [] hle hws.
    rewrite /le_all in hle. rewrite /is_le in hle'. have l_mem' := l_mem hl hle.
    move: (hle' (e_regx env r).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
    apply Public_only_less_than_Public in hle1.
    move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hle1)=> {hregx} hregx. 
    rewrite /of_val /= /truncate_word /=. case: ifP=> //= hsz. 
    have hregx' := zero_extend_small_size hws hregx. by rewrite hregx'.
  split=> //=. move=> hsty. have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). + by case: (e_regx env r)=> //=.
  rewrite henv /= in hregxty. move: hregxty. move=> /andP [] hle hws.
  rewrite /le_all in hle. apply l_subset in hle; subst. case: hle=> hle1 hle2.
  rewrite /is_le in hle'. move: (hle' (e_regx env r).1 public hle1)=> hle1'. 
  rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
  move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hle1')=> {hregx} hregx. 
  rewrite /truncate_word /=. case: ifP=> //= hsz. 
  have hregx' := zero_extend_small_size hws hregx. by rewrite hregx'.
(* Addr *)
+ move=> adr hassert. case: ty=> //=.
  move=> ws. case: ak=> //=.
  (* AK_compute *)
  + move=> [] hv1 hleak1 hassert' [] hv2 hleak2 /andP [hwsz hwt]; subst. 
    rewrite /value_equiv /decode_addr /decode_reg_addr.
    split=> //=. 
    + move=> l hl hrho.
      rewrite /decode_addr. case: adr hassert hassert' hwt=> //=.
      (* reg adr *)
      + move=> r hassert hassert' /andP [] hwt hwt'. rewrite /wt_oreg in hwt hwt'.
        case: (ad_base r) hwt.
        (* some *)   
        + move=> ar /= har. case: (ad_offset r) hwt'=> //=.
          (* some *)
          + move=> ao /= hao. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
            + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
            move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
            have l_mem' := l_mem hl hle.
            move: (hle' (e_reg env ar).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
            apply Public_only_less_than_Public in hle1.
            move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1)=> hreg1. 
            have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
            + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
            move=> /andP [] hle'' hws'. rewrite /le_all in hle''. rewrite /is_le in hle'. 
            have l_mem'' := l_mem hl hle''.
            move: (hle' (e_reg env ao).1 l l_mem'')=> hle1'. rewrite hrho /= in hle1'. 
            apply Public_only_less_than_Public in hle1'.
            move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hle1')=> hreg2. 
            rewrite /of_val /= /truncate_word /=. case: ifP=> //= hsz.
            rewrite !zero_extend_idem; auto. rewrite !wadd_zero_extend; auto.
            rewrite !wmul_zero_extend; auto. 
            have hreg1' := zero_extend_small_size hws hreg1. rewrite hreg1'.
            have hreg2' := zero_extend_small_size hws' hreg2. by rewrite hreg2'.
           (* none *)
           move=> ht. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
           + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
           move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
           have l_mem' := l_mem hl hle.
           move: (hle' (e_reg env ar).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
           apply Public_only_less_than_Public in hle1.
           move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1)=> hreg1.
           rewrite /truncate_word. case: ifP=> //=. move=> h. rewrite !zero_extend_idem /=; auto.
           have hreg1' := zero_extend_small_size hws hreg1.
           rewrite !wadd_zero_extend; auto. by rewrite hreg1'.
         (* None *)
         case: (ad_offset r) hwt'=> //=. move=> ao hao ht.
         have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
         + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
         move=> /andP [] hle'' hws'. rewrite /le_all in hle''. rewrite /is_le in hle'. 
         have l_mem'' := l_mem hl hle''.
         move: (hle' (e_reg env ao).1 l l_mem'')=> hle1'. rewrite hrho /= in hle1'. 
         apply Public_only_less_than_Public in hle1'.
         move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hle1')=> hreg2.
         rewrite /truncate_word. case: ifP=> //=. move=> h. rewrite !zero_extend_idem /=; auto.
         have hreg2' := zero_extend_small_size hws' hreg2. rewrite !wadd_zero_extend; auto.
         rewrite !wmul_zero_extend; auto. by rewrite hreg2'. 
      (* Arip *)
      move=> s hassert hassert' hle. rewrite /le_all in hle; subst.
      rewrite /truncate_word /=. case: ifP=> //= hws. by rewrite hrip. 
   (* sty *)
   split=> //=. move=> hsty; subst. case: adr hassert hassert' hwt=> //=.
   (* reg adr *)
   + move=> r hassert hassert' /andP [] hwt hwt'. rewrite /wt_oreg in hwt hwt'.
     case: (ad_base r) hwt.
     (* some *)   
     + move=> ar /= har. case: (ad_offset r) hwt'=> //=.
       (* some *)
       + move=> ao /= hao. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
         + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
         move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
         apply l_subset in hle; subst. case: hle=> hle1 hle2.
         move: (hle' (e_reg env ar).1 public hle1)=> hle1'. 
         rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
         move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1')=> hregr. 
         rewrite /truncate_word /=. case: ifP=> //= hsz. 
         have hreg' := zero_extend_small_size hws hregr. rewrite !wadd_zero_extend; auto. rewrite hreg'.
         have henvo : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
         + by case: (e_reg env ao)=> //=. rewrite henvo in hao. move: hao.
         move=> /andP [] hleo hwso. rewrite /le_all in hleo. rewrite /is_le in hle'. 
         apply l_subset in hleo; subst. case: hleo=> hleo1 hleo2.
         move: (hle' (e_reg env ao).1 public hleo1)=> hleo1'. 
         rewrite hpub /= in hleo1'. apply Public_only_less_than_Public in hleo1'.
         move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henvo hleo1')=> hrego. 
         rewrite !zero_extend_idem /=; auto. have hrego' := zero_extend_small_size hwso hrego. 
         rewrite !wmul_zero_extend; auto. by rewrite hrego'.
        (* none *)
        move=> ht. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
        + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
        move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
        apply l_subset in hle; subst. case: hle=> hle1 hle2.
        move: (hle' (e_reg env ar).1 public hle1)=> hle1'. 
        rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
        move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1')=> hregr. 
        rewrite /truncate_word /=. case: ifP=> //= hsz. 
        have hreg' := zero_extend_small_size hws hregr. rewrite !wadd_zero_extend; auto. by rewrite hreg'.
       (* none *)
       case: (ad_offset r) hwt'=> //=. move=> ao hao ht.
       have henvo : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
       + by case: (e_reg env ao)=> //=. rewrite henvo in hao. move: hao.
       move=> /andP [] hleo hwso. rewrite /le_all in hleo. rewrite /is_le in hle'. 
       apply l_subset in hleo; subst. case: hleo=> hleo1 hleo2.
       move: (hle' (e_reg env ao).1 public hleo1)=> hleo1'. 
       rewrite hpub /= in hleo1'. apply Public_only_less_than_Public in hleo1'.
       move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henvo hleo1')=> hrego.
       rewrite /truncate_word. case: ifP=> //=. move=> h.
       rewrite !zero_extend_idem /=; auto. have hrego' := zero_extend_small_size hwso hrego. 
       rewrite !wadd_zero_extend; auto. rewrite !wmul_zero_extend; auto. by rewrite hrego'.
   (* Arip *)
   move=> s hassert hassert' hle. rewrite /le_all in hle; subst.
   rewrite /truncate_word /=. case: ifP=> //= hws. by rewrite hrip. 
 (* mem *)
 t_xrbindP=> rv hread hv1 hleak1 hassert' rv' hread' hv2 hleak2 hwt; subst.
 rewrite /value_equiv /of_val /= /truncate_word /decode_addr. 
 case: adr hassert hassert' hread hread' hwt=> //=.
 (* reg address *)
 + move=> r hassert hassert' hread hread' /andP [/andP [hwt hwt']]. case: pt=> //=.
   move=> ptsto hle. rewrite /decode_reg_addr /=. rewrite /decode_reg_addr /= in hread hread'. 
   rewrite /wt_oreg in hwt hwt'. case: (ad_base r) hwt hread hread'=> //=.
   (* some *)
   + move=> ar har hread hread'. case: (ad_offset r) hwt' hread hread'=> //=.
     (* some *)
     + move=> ao hao hread hread'. split.
       + move=> l hl hrho. case: ifP=> //= hws.
         rewrite /le_all in hle har. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2).
          + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har. 
          move=> /andP [] hle'' hws''.  rewrite /is_le in hle'.
          move: (hle' (e_reg env ar).1 public)=> hle1.
          admit.
       split=> //=.
       + admit.
       (* leakage *)
       have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2).
       + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har. 
       move=> /andP [] hle'' hws''. rewrite /is_le in hle'. rewrite /le_all in hle''.
       have hpub' := public_mem hle''. move: (hle' (e_reg env ar).1 public hpub')=> hrhor.
       rewrite hpub in hrhor.
       have hrhor' := Public_only_less_than_Public hrhor. 
       move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hrhor')=> hz.
       have hwr := word_uincl_zero_extR (asm_reg m1 ar) hws''. rewrite /word_uincl in hwr.
       move: hwr. move=> /andP [_ /eqP hwr]. rewrite zero_extend_idem in hwr; auto.
       have hwr' := word_uincl_zero_extR (asm_reg m2 ar) hws''. rewrite /word_uincl in hwr'.
       move: hwr'. move=> /andP [_ /eqP hwr']. rewrite zero_extend_idem in hwr'; auto.
       have hwreq := zero_extend_small_size hws'' hz; auto. rewrite -hwr -hwr' in hwreq. rewrite hwreq.
       have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2).
       + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
       rewrite /le_all. move=> /andP [] hleo hwso. 
       have hpubo := public_mem hleo. move: (hle' (e_reg env ao).1 public hpubo)=> hrhoo.
       rewrite hpub in hrhoo.
       have hrhoo' := Public_only_less_than_Public hrhoo. 
       move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hrhoo')=> hz'.
       have hwo := word_uincl_zero_extR (asm_reg m1 ao) hwso. rewrite /word_uincl in hwo.
       move: hwo. move=> /andP [_ /eqP hwo]. rewrite zero_extend_idem in hwo; auto.
       have hwo' := word_uincl_zero_extR (asm_reg m2 ao) hwso. rewrite /word_uincl in hwo'.
       move: hwo'. move=> /andP [_ /eqP hwo']. rewrite zero_extend_idem in hwo'; auto.
       have hwoeq := zero_extend_small_size hwso hz'; auto. rewrite -hwo -hwo' in hwoeq. by rewrite hwoeq.
     (* None *)
     move=> _ hread hread'. split.
     + move=> l hl hrho. case: ifP=> //= _. admit.
     split=> //=.
     + admit.
     (* leakage *)
     have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2).
     + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har. 
     move=> /andP [] hle'' hws''. rewrite /is_le in hle'. rewrite /le_all in hle''.
     have hpub' := public_mem hle''. move: (hle' (e_reg env ar).1 public hpub')=> hrhor.
     rewrite hpub in hrhor.
     have hrhor' := Public_only_less_than_Public hrhor. 
     move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hrhor')=> hz.
     have hwr := word_uincl_zero_extR (asm_reg m1 ar) hws''. rewrite /word_uincl in hwr.
     move: hwr. move=> /andP [_ /eqP hwr]. rewrite zero_extend_idem in hwr; auto.
     have hwr' := word_uincl_zero_extR (asm_reg m2 ar) hws''. rewrite /word_uincl in hwr'.
     move: hwr'. move=> /andP [_ /eqP hwr']. rewrite zero_extend_idem in hwr'; auto.
     have hwreq := zero_extend_small_size hws'' hz; auto. rewrite -hwr -hwr' in hwreq. by rewrite hwreq.
   (* None *)
   case: (ad_offset r) hwt'=> //=. 
   (* Some *) 
   + move=> ao hao _ hread hread'. split.
     + move=> l hl hrho. case: ifP=> //= _. admit.
     split=> //=.
     + admit.
     (* leakage *)
     have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2).
     + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
     rewrite /le_all. move=> /andP [] hleo hwso. 
     have hpubo := public_mem hleo. move: (hle' (e_reg env ao).1 public hpubo)=> hrhoo.
     rewrite hpub in hrhoo.
     have hrhoo' := Public_only_less_than_Public hrhoo. 
     move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hrhoo')=> hz'.
     have hwo := word_uincl_zero_extR (asm_reg m1 ao) hwso. rewrite /word_uincl in hwo.
     move: hwo. move=> /andP [_ /eqP hwo]. rewrite zero_extend_idem in hwo; auto.
     have hwo' := word_uincl_zero_extR (asm_reg m2 ao) hwso. rewrite /word_uincl in hwo'.
     move: hwo'. move=> /andP [_ /eqP hwo']. rewrite zero_extend_idem in hwo'; auto.
     have hwoeq := zero_extend_small_size hwso hz'; auto. rewrite -hwo -hwo' in hwoeq. by rewrite hwoeq.
   move=> _ _ hread hread'. split=> //=.
   move=> l hl hrho. case: ifP=> //= _. admit.   
   split=> //=. admit.
 (* Rip address *)
 move=> wsz hassert hassert' hread hread' /andP [hle]. case: pt=> //=.
 move=> ptto. rewrite /le_all. move=> hle''. split.
 + move=> l hl hrho. case: ifP=> //= _. admit.
 split=> //=.
 + admit.
 (* leakage *)
 by rewrite hrip.
(* XReg *)
move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
move=> ws hxregty. rewrite /value_equiv. split=> //=.
+ move=> l hl hrho. 
  have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). 
  + by case: (e_xreg env r)=> //=.
  rewrite henv /= in hxregty. move: hxregty. move=> /andP [] hle hws.
  rewrite /le_all in hle. rewrite /is_le in hle'. have l_mem' := l_mem hl hle.
  move: (hle' (e_xreg env r).1 l l_mem')=> hle1. rewrite hrho /= in hle1. 
  apply Public_only_less_than_Public in hle1.
  move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hle1)=> {hxreg} hxreg. 
  rewrite /of_val /= /truncate_word /=. case: ifP=> //= hsz. 
  have hxreg' := zero_extend_small_size hws hxreg. by rewrite hxreg'.
split=> //=.
move=> hsty. have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). + by case: (e_xreg env r)=> //=.
rewrite henv /= in hxregty. move: hxregty. move=> /andP [] hle hws.
rewrite /le_all in hle. apply l_subset in hle; subst. case: hle=> hle1 hle2.
rewrite /is_le in hle'. move: (hle' (e_xreg env r).1 public hle1)=> hle1'. 
rewrite hpub /= in hle1'. apply Public_only_less_than_Public in hle1'.
move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hle1')=> {hxreg} hxreg. 
rewrite /truncate_word /=. case: ifP=> //= hsz. 
have hxreg' := zero_extend_small_size hws hxreg. by rewrite hxreg'.
Admitted.

Lemma type_prev_args : forall c env a S ad pt ty sty s1 s2 rho v1 leak1 v2 leak2,
wt_args_in wt_cond c env a S ad pt ty sty ->
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
eval_args_in_leak s1.(asm_m) a ad ty = ok (v1, leak1) ->
eval_args_in_leak s2.(asm_m) a ad ty = ok (v2, leak2) ->
(forall l, Sl.mem l S -> values_equiv v1 v2 (rho l) ty) /\
 values_equiv v1 v2 sty ty /\ 
 leak1 = leak2.
Proof.
move=> c env a S ad. elim: ad.
(* empty case *)
+ move=> ptis tys st s1 s2 rho v1 leak1 v2 leak2=> //=.
  case: ptis=> //=. case: tys=> //=. 
  move=> _ hequiv hvalid. rewrite /eval_args_in /=. by move=> [] <- <- [] <- <- /=.
move=> ad ads hin pt ty sty [] m1 fn1 code1 ip1 [] m2 fn2 code2 ip2 rho v1 leak1 v2 leak2.
move=> hwt hequiv hvalid heval heval'. have hequivcopy := hequiv. 
case: hequiv=> /= hcode hip hrip hmemequiv; subst.
case: hmemequiv=> /= hreg hregx hxreg hflag hmem.
rewrite /eval_args_in_leak /= in heval heval'.
case: ty hwt heval heval'=> //=.
case: pt=> //=. 
move=> pti ptis t ts /andP [] hwt hwts /=. 
t_xrbindP=> ys -[y yl] heval ys' hevals h1 h2 h3 ys1 -[y' yl'] heval' ys1' hevals' h4 h5 h6 /=; subst.
split.
+ move=> l hml.  
  have hvalid' := hvalid. 
  case: hvalid=> hpub [] hsec hl. 
  have /= Hwt := type_prev_arg hwt hequivcopy hvalid'.  
  move: (Hwt y yl y' yl' heval heval')=> [] hv hleak. split=> //=.
  + by move: (hv l hml).
  rewrite /eval_args_in_leak /= in hin. 
  move: (hin ptis ts sty {| asm_m := m1; asm_f := fn1; asm_c := code2; asm_ip := ip2 |}
       {| asm_m := m2; asm_f := fn2; asm_c := code2; asm_ip := ip2 |} rho)=> {hin} hin.
  rewrite hevals /= hevals' /= in hin.
  move: (hin (unzip1 ys') (flatten (unzip2 ys')) (unzip1 ys1') (flatten (unzip2 ys1')) hwts hequivcopy hvalid' erefl erefl)=>
  {} [] hvs hleaks. by move: (hvs l hml).
(* leakage *)
have hvalid' := hvalid. rewrite /valid_valuations in hvalid'.
case: hvalid=> hpub [] hsec hl. 
have /= Hwt := type_prev_arg hwt hequivcopy hvalid'.  
move: (Hwt y yl y' yl' heval heval')=> [] hv [] hv' ->.
rewrite /eval_args_in_leak /= in hin. 
move: (hin ptis ts sty {| asm_m := m1; asm_f := fn1; asm_c := code2; asm_ip := ip2 |}
       {| asm_m := m2; asm_f := fn2; asm_c := code2; asm_ip := ip2 |} rho)=> {hin} hin.
rewrite hevals /= hevals' /= in hin.
by move: (hin (unzip1 ys') (flatten (unzip2 ys')) (unzip1 ys1') (flatten (unzip2 ys1')) hwts hequivcopy hvalid' erefl erefl)
=> {} [] hval [] hvalsty ->.
Qed.

Lemma type_prev_dest : forall c pts msb args a pti l ty env env' s1 s2 rho m1 m2 ps1 ps2 v1 v2,
ty_dest c pts msb args a pti l ty env = ok env' ->
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
value_equiv v1 v2 (rho l) ty ->
mem_write_val_leak msb args (a, ty) v1 s1.(asm_m) = ok (m1, ps1) ->
mem_write_val_leak msb args (a, ty) v2 s2.(asm_m) = ok (m2, ps2) ->
mem_equiv rho m1 m2 env' /\ ps1 = ps2.
Proof. 
move=> c pts msb args a pti l ty env env' [] 
m1 fn' code1 ip1 [] m2 fn'' code2 ip2 rho m1' m2' ps1 ps2 v1 v2.
move=> hwt hequiv hvalid hvalequiv hmw hmw'. 
case: hequiv=> /= hcode hpc hrip hmemequiv. case: hmemequiv=> /= hreg hregx hxreg hflag hmem.
case: hvalid=> [] hpub [] hsec hl'.
inversion hmw; subst; inversion hmw'; subst. rewrite /mem_write_val_leak in H0 H1.
move: H0. t_xrbindP=> v' /= hv' H0. move: H1. t_xrbindP=> v'' /= hv'' H1.
rewrite /mem_write_ty in H0 H1.
case: a hwt hmw hmw' v' hv' H0 v'' hv'' H1=> //=.
(* Implicit *)
+ move=> i hwt hmw hmw' v' hv' H0 v'' hv'' H1. 
  case: ty hvalequiv hwt hmw hmw' v' hv' H0 v'' hv'' H1=> //=.
  (* a: flag ty : sbool *)
  + move=> hvalequiv hwt hmw hmw' v' hv' H0 v'' hv'' H1. 
    case: i hwt hmw hmw' H0 H1=> //=. move=> f [] <- hmw hmw' [] <- <- [] <- <-. split=> //=.
    rewrite /mem_write_val /= in hmw hmw'. case: v1 hvalequiv hv' hmw=> //=.
    (* v1 is some b *)
    + case: v2 hv'' hmw'=> //=.
      (* v2 is some b' *)
      + move=> b [] <- [] hm2' hl2 b' hvalequiv [] <- [] hm1' hl1. 
        constructor; auto.
        move=> f' l' hflagty hrho' /=. rewrite /RflagMap.set /= !ffunE.
        case: eqP. 
        (* f' = f *)
        + move=> hf; subst. rewrite /set_flag /= in hrho'. rewrite /FinMap.set /= !ffunE in hrho'.
          move: hrho'. case: ifP=> //=. 
          + move=> /eqP hfeq hrho'. rewrite /value_equiv /of_val /to_bool /= in hvalequiv. 
            by move: (hvalequiv hrho')=> [] ->.
          by move=> /eqP []. 
        (* f != f' *)
        move=> hfneq. rewrite -hflagty in hrho'.
        have heq: e_flag env f' = e_flag (set_flag env f l) f'.
        + rewrite /set_flag /= /FinMap.set /= !ffunE. case: ifP=> //=.
          move=> /eqP hfeq; subst. by case: hfneq.
        by move: (hflag f' (e_flag (set_flag env f l) f') heq hrho').
      (* v2 is none *)  
      move=> t he. case: t he=> //= he [] <- [] hm2' hl2 b hvalequiv [] <- [] hm1' hl1.
      constructor; auto. move=> f' l' hflagty hrho' /=. rewrite /value_equiv in hvalequiv.
      rewrite -hflagty /= in hrho'. move: hrho'. rewrite /RflagMap.set /FinMap.set /= !ffunE.
      case: ifP=> //=.
      (* f = f' *)
      + move=> /eqP hfeq hrho; subst. move: (hvalequiv hrho)=> {hvalequiv} hvalequiv.
        rewrite /of_val /to_bool in hvalequiv. by case: (b) hvalequiv=> //=.
      (* f != f' *)
      move=> /eqP hfneq hrho. rewrite /set_flag /= in hflagty. rewrite /FinMap.set /= !ffunE in hflagty.
      move: hflagty. case: ifP=> //=.
      + move=> /eqP hfeq. by case: hfneq.
      move=> /eqP _ hflagty. by move: (hflag f' (e_flag env f') erefl hrho).
   (* v1 is none *)
   case: v2 hmw' hv''=> //=.
   (* v2 is some b *) 
   + move=> b [] hm2' hl2 [] <- t. case: t=> //= e hvalequiv [] <- [] hm1' hl1.
     constructor; auto.
     move=> f' l' hflagty hrho'. rewrite /RflagMap.set /= !ffunE.
     case: eqP. 
     (* f' = f *)
     + move=> hf; subst. rewrite /set_flag /= in hrho'. rewrite /FinMap.set /= !ffunE in hrho'.
       move: hrho'. case: ifP=> //=. 
       + move=> /eqP hfeq hrho'. rewrite /value_equiv /of_val /to_bool /= in hvalequiv. 
         move: (hvalequiv hrho')=> {} hvalequiv. by case: hvalequiv.
       (* f != f' *)
       by move=> /eqP []. 
    (* f != f' *)
    move=> hfneq. rewrite -hflagty in hrho'.
    have heq: e_flag env f' = e_flag (set_flag env f l) f'.
    + rewrite /set_flag /= /FinMap.set /= !ffunE. case: ifP=> //=.
      move=> /eqP hfeq; subst. by case: hfneq.
    by move: (hflag f' (e_flag (set_flag env f l) f') heq hrho').
  (* v2 is none *)
  move=> t. case: t=> //= e [] hm2' hl2 [] <- t. case: t=> //= e' hvalequiv [] <- [] hm1' hl1.
  constructor; auto.
  move=> f' l' hflagty hrho /=. move: hflagty.
  rewrite /set_flag /= /FinMap.set /= !ffunE. case: ifP=> //=. 
  move=> /eqP hneq hflagty.
  by move: (hflag f' l' hflagty hrho).  
 (* ty : sword *)
 move=> wsz hvalequiv hwt hmw hmw' v' hv'. case: i hwt hmw hmw'=> //=.
 move=> r [] <- hmw hmw' [] <- <- v'' hv'' [] <- <- {hmw} {hmw'}. split=> //=.
 constructor; auto.
 move=> r' l' ws. 
 rewrite /mem_write_reg /set_reg /set_size /= /FinMap.set /= !ffunE. case: ifP=> //=.
 (* r = r' *)
 + move=> /eqP hr. case: msb.
   (* msb clear *)
   + move=> [] hl hws hrho. rewrite /value_equiv hl in hvalequiv.
     move: (hvalequiv hrho). rewrite /of_val. move=> {} hvalequiv. rewrite hv' hv'' in hvalequiv.
     case: hvalequiv=> ->. by rewrite !word_extend_CLEAR.
   (* msb merge *)
   move=> [] hl hws hrho; subst. rewrite /value_equiv in hvalequiv.
   move: (hvalequiv hrho). rewrite /of_val. move=> {} hvalequiv. rewrite hv' hv'' in hvalequiv.
   case: hvalequiv=> ->. rewrite /min /=. case: ifP=> //=.
   (* wsz <= regsize *)
   + move=> hsz /=. have hveq: word_uincl v'' v''. + by auto. 
     have := word_uincl_word_extend MSB_MERGE (asm_reg m1 r) hsz hveq. rewrite /word_uincl /=.
     move=> /andP [] _ /eqP <-. 
     have := word_uincl_word_extend MSB_MERGE (asm_reg m2 r) hsz hveq. rewrite /word_uincl /=.
     by move=> /andP [] _ /eqP <-.
   move=> hsz. rewrite !word_extend_big; auto. + unfold not. move=> hsz'. rewrite hsz' /= in hsz. by case: hsz. 
   + unfold not. move=> hsz'. rewrite hsz' /= in hsz. by case: hsz. 
 (* r != r' *)
 move=> /eqP hneq hregty hrho. by move: (hreg r' l' ws hregty hrho)=> ->.
(* Explicit *)
move=> adrk n o. case: (onth args n)=> //= a. rewrite /mem_write_bool /= /mem_write_word /=.
case: a=> //=.
(* reg *)
+ rewrite /value_equiv in hvalequiv. case: ty hvalequiv=> //=. case: (onth args n)=> //= a w hvalequiv. case: a=> //=.
  + move=> ct. by case: (check_oreg o (Condt ct)).
  + move=> ws s. by case: (check_oreg o (Imm s)).
  + move=> r r'. case: (check_oreg o (Reg r))=> //=.
    move=> [] <-  _ _ v' hv' [] <- <- v'' hv'' [] <- <-. split=> //=.
    constructor; auto.
    move=> r'' l'' ws hregty hrho. rewrite /mem_write_reg /set_reg /= /FinMap.set !ffunE /=.
    case: ifP=> //=.
    (* r'' = r' *)
    + move=> /eqP hreq /=; subst. rewrite /mem_write_reg /set_reg /= /FinMap.set !ffunE /= in hregty.
      move: hregty. case: ifP=> //=.
      (* r' == r *)
      + move=> /eqP hr; subst. case: msb=> //=.
        (* msb clear *)
        + move=> [] hl hws; subst. move: (hvalequiv hrho). 
          rewrite /of_val. rewrite hv' hv''. move=> [] ->. by rewrite !word_extend_CLEAR.
        (* msb merge *)
        rewrite /min. move=> [] hl hws; subst. move: (hvalequiv hrho). 
        rewrite /of_val. rewrite hv' hv''. move=> [] ->. case: ifP=> //= hsz.
        + have hveq: word_uincl v'' v''. + by auto.
          have := word_uincl_word_extend MSB_MERGE (asm_reg m1 r') hsz hveq. rewrite /word_uincl /=.
          move=> /andP [] _ /eqP <-. 
          have := word_uincl_word_extend MSB_MERGE (asm_reg m2 r') hsz hveq. rewrite /word_uincl /=.
          by move=> /andP [] _ /eqP <-.
        rewrite !word_extend_big; auto. + unfold not. move=> hsz'. rewrite hsz' /= in hsz. by case: hsz. 
        + unfold not. move=> hsz'. rewrite hsz' /= in hsz. by case: hsz.
      (* r' != r *)
      move=> /eqP hneq henv'. move: (hreg r l'' ws henv' hrho)=> hz.
      case: msb=> //=.
      (* msb clear *)
      + admit.
      (* msb merge *)
      admit.
    (* r' != r'' *)
    move=> /eqP hr. rewrite /mem_write_reg /set_reg /= /FinMap.set !ffunE /= in hregty.
    move: hregty. case: ifP=> //=.
    (* r'' = r & r'' = r' *)
    + move=> /eqP hr'' [] hl'' <-; subst. case: msb=> //=.
      (* msb clear *)
      + admit.
      (* msb merge *)
      admit.
  (* r'' != r != r' *)
  move=> /eqP hneq henv'. by move: (hreg r'' l'' ws henv' hrho).
Admitted.

(*find_label lbl code2 = ok pc
find_label lbl (asm_fd_body fundef) = ok pc''*)

(* Type preserves state equivalence *) 
Lemma type_prev_state_equivalence : forall Env env env' rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code wt_cond fn sec_ty_op c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env ->
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1_leak P s1 l1 s1' ->
asmsem1_leak P s2 l2 s2' ->
oseq.onth Env s1'.(asm_ip) = Some env' ->
state_equiv rho s1' s2' env'.
Proof.
move=> Env env env' rho [] /= m1 fn1 code1 pc1 [] m2 fn2 code2 pc2 c P Pt_info pts s1' s2' l1 l2 hwt hpcenv hvalid hequiv.
have hequivcopy := hequiv. move: hequiv.
move=> [] /= hcode hpc hrip hmemequiv. 
case: hmemequiv=> /= hreg hregx hxreg hflag hmem hstep1 hstep2 hpcenv'; subst.
rewrite /wt_code /= in hwt.
move: (hwt pc2)=> /= hwtpc2. 
have hpc : pc2 < size code2. + admit. 
move: (hwtpc2 hpc)=> {hwtpc2} hwtpc2.
move: env env' hpcenv hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
case: hwtpc2.
(* AsmOp *)
+ move=> o args env env' dpt apt env1 hpci hpcenv hpcenv' /= hn hargs htydests hle.
  rewrite hpcenv /=. move=> env1' env2' [] h; subst. 
  move=> henv' hreg hregx hxreg hflag hmem hequivcopy.
  inversion hstep1; inversion hstep2; subst. rewrite /fetch_and_eval_leak hpci /= in H0 H1.
  move: H0. t_xrbindP=> -[m leak] heval /= hs1' hleak. 
  move: H1. t_xrbindP=> -[m' leak'] heval' /= hs2' hleak'.
  rewrite /st_update_next /= in hs1' hs2'. rewrite -hs1' -hs2' /=; subst. 
  rewrite /= hpcenv' in henv'. case: henv'=> h; subst. 
  rewrite /eval_op in heval heval'. 
  constructor; auto; rewrite /=; auto.
  (* rip *)
  + admit. admit. 
(* Align *)
+ move=> env env' hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval_leak /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto. constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv' => /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
  case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* LABEL lbl *)
+ move=> env env' lbl hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval_leak /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto. constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
    case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hrip' hmemequiv'. 
  case: hmemequiv'=> /= hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* JMP (fn', lbl) *)
+ move=> env env' fn' lbl pc hpci hpcenv /eqP hfn.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval_leak /= hpci /= in H0 H1; subst.
  case: (get_fundef (asm_funcs P) fn') H0 H1=> //= fundef /= H0 H1; subst.
  move: H0. t_xrbindP=> pc' hlb' /= hs1' hleak; subst. move: H1. t_xrbindP=> pc'' hlb'' /= hs2' hleak'; subst.
  rewrite hlb' in hlb''. case: hlb''=> h; subst. 
  move=> hlbl hpcenv' hle env1 env2. rewrite hpcenv. move=> [] h; subst.   
  move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  constructor; auto; subst. constructor; subst.
  + admit.
  + admit.
  + admit.
  + admit.
  admit. 
(* JCC lbl ct *)
move=> env envf envt lbl ip ct hpci hpcenv hwct hlbl henvf henvt [hlef hlet] env1 env2.
rewrite hpcenv. move=> [] h; subst. move=> hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
inversion hstep1; inversion hstep2. rewrite /fetch_and_eval_leak /= hpci /= in H0 H1; subst.
rewrite /eval_Jcc_leak /= in H0 H1. move: H0. t_xrbindP=> b hevalm pc hb hs1' hleak; subst.
move: H1. t_xrbindP=> b' hevalm' pc' hb' hs2' hleak'; subst. rewrite /= in hpcenv'. 
admit.
Admitted. 

(* Type preserves constant-time *) 
Lemma type_prev_leakage : forall Env env rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code wt_cond fn sec_ty_op c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env -> 
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1_leak P s1 l1 s1' ->
asmsem1_leak P s2 l2 s2' ->
l1 = l2.
Proof.
Admitted.

