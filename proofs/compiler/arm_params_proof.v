From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  stack_alloc
  stack_alloc_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering
  arm_lowering_proof.
Require Export arm_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context {syscall_state : Type} {sc_sem : syscall_sem syscall_state} {call_conv : calling_convention}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Context
  (P' : sprog)
  (P'_globs : p_globs P' = [::]).

Lemma addiP s1 e i x tag ofs w s2 :
  (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
  -> psem.sem_i P' w s1 (addi x tag e ofs) s2.
Proof.
  move=> he hx.
  apply psem.Eopn.
  rewrite /sem_sopn /=.
  rewrite P'_globs.
  rewrite /exec_sopn /=.
  move: he.
  t_xrbindP=> _ -> /= -> /=.
  rewrite zero_extend_u.
  by rewrite hx.
Qed.

(*
Definition arm_hsaparams is_regx : h_stack_alloc_params (ap_sap arm_params is_regx).
Proof.
  constructor.
  exact: arm_mov_ofsP.
Defined.
*)
End STACK_ALLOC.

Lemma arm_mov_ofsP (P': sprog) s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x tag vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /arm_mov_ofs.
  move=> [<-].
  by apply addiP.
Qed.

Definition arm_hsaparams is_regx : h_stack_alloc_params (ap_sap arm_params is_regx) :=
  {|
    mov_ofsP := arm_mov_ofsP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Context
  (lp : lprog)
  (s : estate)
  (sp_rsp : Ident.ident)
  (ii : instr_info)
  (fn : funname)
  (pc : nat).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp xH.
Let vm := evm s.

Lemma arm_spec_lip_allocate_stack_frame ts sz :
  let args := lip_allocate_stack_frame arm_liparams (VarI vrsp xH) sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_free_stack_frame ts sz :
  let args := lip_free_stack_frame arm_liparams (VarI vrsp xH) sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts - wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  rewrite wrepr_opp.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_ensure_rsp_alignment ws ts' :
  let al := align_word ws ts' in
  let args := lip_ensure_rsp_alignment arm_liparams vrspi ws in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  get_var (evm s) vrsp = ok (Vword ts')
  -> wf_vm (evm s)
  -> exists vm',
      [/\ eval_instr lp i (of_estate s fn pc)
          = ok (of_estate (with_vm s vm') fn pc.+1)
        , vm' = (evm s).[vrsp <- ok (pword_of_word al)]%vmap
              [\vflags]
        , forall x,
            Sv.In x vflags
            -> ~ is_ok (vm'.[x]%vmap)
            -> (evm s).[x]%vmap = vm'.[x]%vmap
        & wf_vm vm'
      ].
Proof.
  move=> /= hvrsp hwm1.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /=.
  rewrite hvrsp /=.
  rewrite zero_extend_u zero_extend_wrepr; last done.
  rewrite pword_of_wordE.
  rewrite /with_vm /=.
  eexists; split=> //.
  + move=> x hin. rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x) => //.
    by move=> ?; subst x.
  by apply wf_vm_set.
Qed.

Lemma arm_spec_lip_lassign (s1 s2 : estate) x e ws ws' (w : word ws) (w' : word ws') :
  let args := lip_lassign arm_liparams x ws e in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  sem_pexpr [::] s1 e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lval [::] x (Vword w) s1 = ok s2
  -> eval_instr lp i (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> /= hsem htruncate hwrite.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite hsem {hsem} /=.

  (* TODO_ARM: Constraint: ws is U32 *)
  have ? : ws = U32. exact: TODO_ARM_PROOF. subst ws.

  (* TODO_ARM: Constraint: x is a register or memory location *)
  case: x hwrite
    => /= [? ? | x | al x off | ? ? ? ? | ? ? ? ? ?] hwrite.
  1,4,5: exact: TODO_ARM_PROOF.

  (* TODO_ARM: Constraint: if x is a register, e is a register or
     memory location *)
  - case: e => [||| y ||| al y off ||||] /=.
    1,2,3,5,6,8,9,10,11: exact: TODO_ARM_PROOF.

  all: rewrite /exec_sopn /=.
  all: rewrite htruncate {htruncate} /=.
  all: by rewrite hwrite {hwrite} /=.
Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := arm_spec_lip_free_stack_frame;
    spec_lip_ensure_rsp_alignment := arm_spec_lip_ensure_rsp_alignment;
    spec_lip_lassign := arm_spec_lip_lassign;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R12.
  rewrite /=.
  change "r12"%string with (to_string R12).
  exact: to_stringK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Lemma arm_lower_callP
  (eft : eqType)
  (pT : progT eft)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (_ : lop_fvars_correct arm_loparams fv (p_funcs p))
  (f : funname)
  scs mem scs' mem'
  (va vr : seq value) :
  psem.sem_call p ev scs mem f va scs' mem' vr
  -> let lprog :=
       lowering.lower_prog
         (lop_lower_i arm_loparams)
         options
         warning
         fv
         is_var_in_memory
         p
     in
     psem.sem_call lprog ev scs mem f va scs' mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition arm_hloparams : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Lemma condt_of_rflagP rf r :
  eval_cond (get_rf rf) (condt_of_rflag r) = to_bool (of_rbool (rf r)).
Proof.
  rewrite -get_rf_to_bool_of_rbool. by case: r.
Qed.

Lemma not_condtP c rf b :
  eval_cond rf c = ok b
  -> eval_cond rf (not_condt c) = ok (negb b).
Proof.
  case: c => /=.

  (* These conditions corresponds to a single flag. *)
  all: try by move ->.

  (* These correspond to a combination of flags.
     Introduce them and case on their values. *)
  all: t_xrbindP.
  all: repeat
         match goal with
           [ |- forall (_ : bool), _ -> _ ] => move=> [] ->
         end.
  all: by move=> <-.
Qed.

Lemma arm_eval_assemble_cond ii m rf e c v :
  eqflags m rf
  -> agp_assemble_cond arm_agparams ii e = ok c
  -> sem_pexpr [::] m e = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  rewrite /=.
  elim: e c v => [||| x |||| op1 e hind |||] //= c v eqf. 

  - t_xrbindP=> r ok_r <- ok_v.
    have := gxgetflag_ex eqf ok_r ok_v.
    change arm_sem.eval_cond with eval_cond.
    rewrite condt_of_rflagP => hincl.
    eexists; last exact: hincl.
    exact: value_of_bool_to_bool_of_rbool.

  case: op1 => //.
  t_xrbindP=> c' ok_c' <- ve ok_ve.
  have hv' := hind _ _ eqf ok_c' ok_ve.
  rewrite /sem_sop1 /=.
  t_xrbindP=> b ok_b <-.
  have := value_of_bool_uincl ok_b hv'.
  change arm_sem.eval_cond with eval_cond.
  move=> /not_condtP ->.
  by eexists; first by reflexivity.
Qed.

(* TODO_ARM: Is there a way of avoiding importing here? *)
Import arch_sem.

Lemma arm_assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op arm_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof. by case: op. Qed.

Definition arm_hagparams : h_asm_gen_params (ap_agp arm_params) :=
  {|
    hagp_eval_assemble_cond := arm_eval_assemble_cond;
    hagp_assemble_extra_op := arm_assemble_extra_op;
  |}.

End ASM_GEN.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition arm_is_move_opP op vx v :
  ap_is_move_op arm_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => //.
  move=> [[]] //.
  move=> [] //.
  move=> [] //.
  move=> [[] [] [?|]] // _.
  rewrite /exec_sopn /=.
  t_xrbindP=> w w'.
  move=> hvx.
  have [ws' [w'' [-> /truncate_wordP [hws' ->]]]] := to_wordI hvx.
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /=.
  move=> [<-] <-.
  apply List.Forall2_cons; last done.
  exact: word_uincl_zero_ext hws'.
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params : h_architecture_params arm_params :=
  {|
    hap_hsap := arm_hsaparams;
    hap_hlip := arm_hliparams;
    ok_lip_tmp := arm_ok_lip_tmp;
    hap_hlop := arm_hloparams;
    hap_hagp := arm_hagparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
