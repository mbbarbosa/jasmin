(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export warray_ word sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : forall (t:stype), is_sarr t = false -> value.
Arguments Vundef _ _ : clear implicits.

Lemma Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
  exists en: n = n', eq_rect n (λ s, WArray.array s) t n' en = t'.
Proof.
  case: e => ?; subst n'; exists erefl.
  exact: (Eqdep_dec.inj_pair2_eq_dec _ Pos.eq_dec).
Qed.

Corollary Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof.
  by move=> /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec en erefl).
Qed.

Lemma Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  exists e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w'.
Proof. by case: e => ?; subst sz' => [[<-]]; exists erefl. Qed.

Notation undef_b := (Vundef sbool erefl).
Notation undef_i := (Vundef sint erefl).
Notation undef_w ws := (Vundef (sword ws) erefl).

Definition values := seq value.

Definition is_defined v := if v is Vundef _ _ then false else true.

Lemma undef_x_vundef t h : Vundef t h =
  match t with
  | sbool => undef_b
  | sint => undef_i
  | sword ws => undef_w ws
  | _ => Vundef t h
  end.
Proof.
  by case: t h => [| | // | ?] ?; f_equal; exact: Eqdep_dec.UIP_refl_bool.
Qed.

(* ** Type of values
  * -------------------------------------------------------------------- *)

Definition type_of_val v :=
  match v with
  | Vbool _ => sbool
  | Vint  _ => sint
  | Varr n _ => sarr n
  | Vword s _ => sword s
  | Vundef t _ => vundef_type t
  end.

Lemma type_of_valI v t : type_of_val v = t ->
  match t with
  | sbool => v = undef_b \/ exists b: bool, v = b
  | sint => v = undef_i \/ exists i: Z, v = i
  | sarr len => exists a, v = @Varr len a
  | sword ws => (exists ws', v = undef_w ws') \/ exists w, v = @Vword ws w
  end.
Proof.
  by case: v; last case; move=> > <- //=; eauto; rewrite undef_x_vundef; eauto.
Qed.

Definition check_ty_val (ty:stype) (v:value) :=
  subtype ty (type_of_val v).

Definition is_word v := is_sword (type_of_val v).

Lemma is_wordI v : is_word v → subtype sword8 (type_of_val v).
Proof. by case: v => // [> | [] > //] _; exact: wsize_le_U8. Qed.

(* ** Test for extension of values
  * -------------------------------------------------------------------- *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t _, _ => compat_type t (type_of_val v2)
  | _, _ => False
  end.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Varr n1 t1 =>
    exists n2 t2, v2 = @Varr n2 t2 /\ WArray.uincl t1 t2
  | Vword sz1 w1 => exists sz2 w2, v2 = @Vword sz2 w2 /\ word_uincl w1 w2
  | Vundef t _ => compat_type t (type_of_val v2)
  | _ => v2 = v1
  end.
Proof. by case: v1 => >; case: v2 => > //=; eauto=> ->. Qed.

Lemma value_uincl_refl v: value_uincl v v.
Proof. by case: v => //= *; exact: compat_type_undef. Qed.

Hint Resolve value_uincl_refl : core.

Lemma value_uincl_subtype v1 v2 :
  value_uincl v1 v2 ->
  subtype (type_of_val v1) (type_of_val v2).
Proof.
case: v1 v2 => [ b | i | n t | s w | ty /= /negP h]; try by case.
+ by case => //= n' t' [] /ZleP.
+ by case => //= s' w' /andP[].
by move => /= v2; apply compat_subtype_undef.
Qed.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 -> value_uincl v2 v3 -> value_uincl v1 v3.
Proof.
  case: v1 => > /value_uinclE; try by move=> -> /value_uinclE ->.
  + by move=> [? [? [-> /WArray.uincl_trans h]]] /value_uinclE [? [? [-> /h]]].
  + by move=> [? [? [-> /word_uincl_trans h]]] /value_uinclE [? [? [-> /h]]].
  by move=> /compat_type_trans h /value_uincl_subtype /subtype_compat /h.
Qed.

Lemma value_uincl_compat_type v1 v1' v2 v2':
  value_uincl v1 v1' -> value_uincl v2 v2' ->
  compat_type (type_of_val v1) (type_of_val v2) ->
  compat_type (type_of_val v1') (type_of_val v2').
Proof.
  move=> /value_uincl_subtype /subtype_compat +
    /value_uincl_subtype /subtype_compat /[swap].
  by rewrite compat_typeC => /compat_type_trans h/h; exact: compat_type_trans.
Qed.

Lemma check_ty_val_uincl v1 x v2 :
  check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
Proof.
  rewrite /check_ty_val => h /value_uincl_subtype.
  by apply: subtype_trans.
Qed.

(* ** Conversions between values and sem_t
  * -------------------------------------------------------------------- *)

Definition to_bool v :=
  match v with
  | Vbool b => ok b
  | Vundef sbool _ => undef_error
  | _ => type_error
  end.

Lemma to_boolI x b : to_bool x = ok b → x = b.
Proof. by case: x => //= => [? [->] | []]. Qed.

Lemma to_bool_undef v : to_bool v = undef_error -> v = undef_b.
Proof. by case: v => //= - [] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Definition to_int v :=
  match v with
  | Vint i => ok i
  | Vundef sint _ => undef_error
  | _ => type_error
  end.

Lemma to_intI v n: to_int v = ok n → v = n.
Proof. by case: v => //= [? [<-] | [] ]. Qed.

Lemma to_int_undef v : to_int v = undef_error -> v = undef_i.
Proof. by case: v => //= -[] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Definition to_arr len v : exec (sem_t (sarr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | _ => type_error
  end.

Lemma to_arrI n v t : to_arr n v = ok t ->
  exists n' (t':WArray.array n'), v = Varr t' /\ WArray.cast n t' = ok t.
Proof. by case: v => //= n' t'; eexists; eauto. Qed.

Lemma to_arr_undef p v : to_arr p v <> undef_error.
Proof. by case: v => //= ??; rewrite /WArray.cast; case: ifP. Qed.

Definition to_word s v : exec (word s) :=
  match v with
  | Vword s' w => truncate_word s w
  | Vundef (sword s') _ => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _ => type_error
  end.


Notation to_pointer := (to_word Uptr).

Lemma to_wordI sz v w : to_word sz v = ok w ->
  exists sz' (w': word sz'), v = Vword w' /\ truncate_word sz w' = ok w.
Proof. by case: v => //=; eauto; case => //. Qed.

Lemma to_wordI' sz v w : to_word sz v = ok w -> exists sz' (w': word sz'),
  [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof.
  move=> /to_wordI[sz' [w' [? /truncate_wordP[??]]]]; eexists _, _.
  by constructor; eauto.
Qed.

Lemma to_word_undef s v :
  to_word s v = undef_error -> exists ws, v = undef_w ws.
Proof.
  case: v => //= [> /truncate_word_errP |] [] // ??.
  by rewrite undef_x_vundef; eauto.
Qed.

(* ----------------------------------------------------------------------- *)

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool => to_bool
  | sint => to_int
  | sarr n => to_arr n
  | sword s => to_word s
  end.

Lemma of_val_typeE t v v' : of_val t v = ok v' ->
  match t, v' with
  | sarr len, vt => exists len' (a: WArray.array len'),
    v = Varr a /\ WArray.cast len a = ok vt
  | sword ws, vt => exists ws' (w: word ws'),
    v = Vword w /\ truncate_word ws w = ok vt
  | sbool, vt => v = vt
  | sint, vt => v = vt
  end.
Proof.
  case: t v' => /= >.
  + exact: to_boolI.
  + exact: to_intI.
  + exact: to_arrI.
  exact: to_wordI.
Qed.

Lemma of_valE t v v' : of_val t v = ok v' ->
  match v with
  | Vbool b => exists h: t = sbool, eq_rect _ _ v' _ h = b
  | Vint i => exists h: t = sint, eq_rect _ _ v' _ h = i
  | Varr len a => exists len' (h: t = sarr len') (a': WArray.array len'),
    WArray.cast len' a = ok a' /\ eq_rect _ _ v' _ h = a'
  | Vword ws w => exists ws' (h: t = sword ws') w',
    truncate_word ws' w = ok w' /\ eq_rect _ _ v' _ h = w'
  | Vundef t h => False
  end.
Proof.
  by case: t v' => > /of_val_typeE; try (simpl=> ->; exists erefl; eauto);
    simpl=> > [? [? [-> ]]]; eexists; exists erefl; eauto.
Qed.

Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
Proof.
  case: t sv => > /of_val_typeE; try by move=> ->.
  + by case=> ? [? [-> /WArray.cast_len /ZleP]].
  by case=> ? [? [-> /truncate_wordP[]]]. 
Qed.

Lemma of_value_uincl ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match v' with
  | Varr len a => exists len' (h: ty = sarr len') a',
    of_val (sarr len') v' = ok a' /\ WArray.uincl (eq_rect _ _ vt _ h) a'
  | _ => of_val ty v' = ok vt
  end.
Proof.
  case: v => > /value_uinclE + /of_valE //;
    try (by move=> -> [? ]; subst=> /= ->);
    move: vt => + [? [? [-> +]]] [s [x [? []]]]; subst=> /= _ ++ ->.
  + move=> /WArray.uincl_cast h/h [? [??]]; exists s, erefl; eauto.
  exact: word_uincl_truncate.
Qed.

(* can be use to shorten proofs drastically, see psem/vuincl_sem_sop1 *)
Lemma of_value_uincl_te ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match ty as ty return sem_t ty -> Prop with
  | sarr n => fun vt =>
    exists2 vt', of_val (sarr n) v' = ok vt' & WArray.uincl vt vt'
  | _ => fun _ => of_val ty v' = ok vt
  end vt.
Proof.
  case: v => > /value_uinclE + /of_valE //;
    try (by move=> -> [? ]; subst=> /= ->);
    move: vt => + [? [? [-> +]]] [? [? [? []]]]; subst=> /= _ ++ ->.
  + by move=> /WArray.uincl_cast h/h [a [??]]; exists a.
  exact: word_uincl_truncate.
Qed.

(* ----------------------------------------------------------------------- *)

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool => Vbool
  | sint => Vint
  | sarr n  => @Varr n
  | sword s => @Vword s
  end.

Lemma to_val_inj t (v1 v2: sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof. by case: t v1 v2 => /= > => [[]|[]| /Varr_inj1 |[]]. Qed.

Lemma to_valI t (x: sem_t t) v : to_val x = v ->
  match v with
  | Vbool b => exists h: t = sbool, eq_rect _ _ x _ h = b
  | Vint i => exists h: t = sint, eq_rect _ _ x _ h = i
  | Varr len a => exists h: t = sarr len, eq_rect _ _ x _ h = a
  | Vword ws w => exists h: t = sword ws, eq_rect _ _ x _ h = w
  | Vundef _ _ => False
  end.
Proof. by case: t x => /= > <-; exists erefl. Qed.

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Definition oto_val t : sem_ot t -> value :=
  match t return sem_ot t -> value with
  | sbool => fun ob => if ob is Some b then Vbool b else undef_b
  | x => @to_val x
  end.

Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
Proof. by case: t s => //= -[]. Qed.

Definition val_uincl (t1 t2:stype) (v1:sem_t t1) (v2:sem_t t2) :=
  value_uincl (to_val v1) (to_val v2).

Lemma val_uincl_alt t1 t2 : @val_uincl t1 t2 =
  match t1, t2 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr _, sarr _ => WArray.uincl
  | sword s1, sword s2 => @word_uincl s1 s2
  | t1', t2' => if boolP (t1' == t2') is AltTrue h
    then eq_rect _ (fun x => sem_t t1' -> sem_t x -> Prop) eq _ (eqP h)
    else fun _ _ => False
  end.
Proof.
  by case: t1; case: t2 => >; rewrite /val_uincl //=;
    case: {-}_/ boolP => // h >;
    rewrite -(FunctionalExtensionality.eta_expansion (@eq _))
      (Eqdep_dec.UIP_dec stype_eq_dec (eqP h)).
Qed.

Lemma val_uinclEl t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t1 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr len => fun v1 v2 => exists len' (h: t2 = sarr len'),
    WArray.uincl v1 (eq_rect _ _ v2 _ h)
  | sword ws => fun v1 v2 => exists ws' (h: t2 = sword ws'),
    word_uincl v1 (eq_rect _ _ v2 _ h)
  | t => fun v1 v2 => exists h: t2 = t, v1 = eq_rect _ _ v2 _ h
  end v1 v2.
Proof.
  by case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
    rewrite /val_uincl /=; eexists; exists erefl.
Qed.

Lemma val_uinclE t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t2 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr len => fun v1 v2 => exists len' (h: t1 = sarr len'),
    WArray.uincl (eq_rect _ _ v1 _ h) v2
  | sword ws => fun v1 v2 => exists ws' (h: t1 = sword ws'),
    word_uincl (eq_rect _ _ v1 _ h) v2
  | t => fun v1 v2 => exists h: t1 = t, v2 = eq_rect _ _ v1 _ h
  end v1 v2.
Proof.
  by case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
    rewrite /val_uincl /=; eexists; exists erefl.
Qed.

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.
Hint Resolve val_uincl_refl : core.

Lemma val_uincl_of_val ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  exists2 vt', of_val ty v' = ok vt' & val_uincl vt vt'.
Proof.
  case: v => > /value_uinclE + /of_valE //;
    try (by move=> -> [? ]; subst => /= ->; eauto);
    move: vt => + [? [? [-> +]]] [s [x [? []]]]; subst=> /= _ ++ ->.
  + move=> /WArray.uincl_cast h/h [? [-> ?]]; eauto.
  move=> /word_uincl_truncate h/h{h} ->; eauto.
Qed.

(* ** Values implicit downcast (upcast is explicit because of signedness)
  * -------------------------------------------------------------------- *)

Definition truncate_val (ty: stype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

Lemma truncate_val_typeE ty v vt :
  truncate_val ty v = ok vt ->
  match ty with
  | sbool => exists2 b: bool, v = b & vt = b
  | sint => exists2 i: Z, v = i & vt = i
  | sarr len => exists a len' (a' : WArray.array len'),
    [/\ WArray.cast len a' = ok a, v = Varr a' & vt = Varr a]
  | sword ws => exists w ws' (w': word ws'),
    [/\ truncate_word ws w' = ok w, v = Vword w' & vt = Vword w]
  end.
Proof.
  rewrite /truncate_val; t_xrbindP; case: v => > /of_valE; case=> ?;
    try (by subst=> /= -> <-; eauto); case=> ? [? []]; subst=> /= hv -> <-.
  + eexists; eexists; eexists; constructor=> //; move: hv.
    by rewrite /WArray.cast; case: ifP => /ZleP.
  by eexists; eexists; eexists; constructor; auto.
Qed.

Lemma truncate_valE ty v vt :
  truncate_val ty v = ok vt ->
  match v with
  | Vbool b => ty = sbool /\ vt = b
  | Vint i => ty = sint /\ vt = i
  | Varr len a => exists len' a',
    [/\ ty = sarr len', WArray.cast len' a = ok a' & vt = Varr a']
  | Vword ws w => exists ws' w',
    [/\ ty = sword ws', truncate_word ws' w = ok w' & vt = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  by case: ty => > /truncate_val_typeE
    => [ [] | [] | [? [? [? []]]] | [? [? [? []]]] ] ? -> -> //;
    eexists; eexists; split; auto.
Qed.

Lemma truncate_valI ty v vt :
  truncate_val ty v = ok vt ->
  match vt with
  | Vbool b => ty = sbool /\ v = b
  | Vint i => ty = sint /\ v = i
  | Varr len a => exists len' (a': WArray.array len'),
    [/\ ty = sarr len, WArray.cast len a' = ok a & v = Varr a']
  | Vword ws w => exists ws' (w': word ws'),
    [/\ ty = sword ws, truncate_word ws w' = ok w & v = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  by case: ty => > /truncate_val_typeE
    => [ [] | [] | [? [? [? []]]] | [? [? [? []]]] ] ? -> -> //;
    eexists; eexists; split; auto.
Qed.

Lemma truncate_val_subtype ty v v' :
  truncate_val ty v = ok v' →
  subtype ty (type_of_val v).
Proof.
  by case: v => > /truncate_valE
    => [[]|[]|[?[?[+/WArray.cast_len/ZleP?]]]|[?[?[+/truncate_wordP[??]]]]|//]
    => ->.
Qed.

Lemma truncate_val_has_type ty v v' :
  truncate_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  by case: v' => > /truncate_valI
    => [[]|[]|[?[?[+/WArray.cast_len/ZleP?]]]|[?[?[+/truncate_wordP[??]]]]|//]
    => ->.
Qed.

(* ----------------------------------------------------------------------- *)

Lemma value_uincl_truncate ty x y x' :
  value_uincl x y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
  case: x => > /value_uinclE+ /truncate_valE => [ + [] | + []
    | [? [? [+ /WArray.uincl_cast h]]] [? [? [+ /h{h} [? [h hui]]]]]
    | [? [? [+ /word_uincl_truncate h]]] [? [? [+ /h{h} h]]] |//]
    => -> -> ->.
  1,2: by eexists.
  all: by rewrite /truncate_val /= h /=; eexists=> // /=.
Qed.

Lemma truncate_value_uincl t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  rewrite /truncate_val; case: t; t_xrbindP=> > /=.
  + by move=> /to_boolI -> <-.
  + by move=> /to_intI -> <-.
  + by move=> /to_arrI [n' [t' [-> h <-]]] /=; exact: WArray.cast_uincl.
  by move=> /to_wordI [? [? [-> ? <-]]] /=; exact: truncate_word_uincl.
Qed.

Lemma mapM2_truncate_value_uincl tyin vargs1 vargs1' :
  mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
  List.Forall2 value_uincl vargs1' vargs1.
Proof.
  move=> htr.
  have {htr} := mapM2_Forall3 htr.
  elim {vargs1 vargs1'} => //.
  move=> _ v1 v1' _ vargs1 vargs1' /truncate_value_uincl huincl _ ih.
  by constructor.
Qed.

Lemma mapM2_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
  List.Forall2 value_uincl vs1' vs2' ->
  exists2 vs2, mapM2 ErrType truncate_val tys vs2' = ok vs2 &
    List.Forall2 value_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have [v2 -> hv2 /=]:= value_uincl_truncate hv htr.
  by have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eauto.
Qed.

(* ----------------------------------------------------------------------- *)

Fixpoint list_ltuple (ts:list stype) : sem_tuple ts -> values :=
  match ts return sem_tuple ts -> values with
  | [::] => fun (u:unit) => [::]
  | t :: ts =>
    let rec := @list_ltuple ts in
    match ts return (sem_tuple ts -> values) -> sem_tuple (t::ts) -> values with
    | [::] => fun _ x => [:: oto_val x]
    | t1 :: ts' =>
      fun rec (p : sem_ot t * sem_tuple (t1 :: ts')) =>
       oto_val p.1 :: rec p.2
    end rec
  end.

Lemma type_of_val_ltuple tout (p : sem_tuple tout) :
  List.map type_of_val (list_ltuple p) = tout.
Proof.
  elim: tout p => //= t1 [|t2 tout] /=.
  + by rewrite /sem_tuple /= => _ x;rewrite type_of_oto_val.
  by move=> hrec [] x xs /=; rewrite type_of_oto_val hrec.
Qed.

(* ----------------------------------------------------------------------- *)

Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T :=
  match ts return sem_prod ts (exec T) → values → exec T with
  | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values),
    if vs is v :: vs
    then Let v := of_val t v in app_sopn (o v) vs
    else type_error
  end.

Arguments app_sopn {T} ts _ _.

Definition app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) vs :=
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_sarr ts -> List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v -> app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [/value_uinclE hv hvs].
  t_xrbindP; case: t o ht => [ | | // | sz ] o _ + /of_val_typeE;
    try by simpl=> ??; subst; subst=> /(Hrec _ _ _ hts hvs).
  simpl=> ? [? [? [? /word_uincl_truncate h]]]; subst.
  by move: hv => [? [? [? /h]]]; subst => /= -> /(Hrec _ _ _ hts hvs).
Qed.

Lemma vuincl_app_sopn_v_eq tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
  all is_not_sarr tin -> forall vs vs' v, List.Forall2 value_uincl vs vs' ->
  app_sopn_v semi vs = ok v -> app_sopn_v semi vs' = ok v.
Proof.
  rewrite /app_sopn_v => hall vs vs' v hu; t_xrbindP => v' h1 h2.
  by rewrite (vuincl_sopn hall hu h1) /= h2.
Qed.

Lemma vuincl_copy_eq ws p :
  let sz := Z.to_pos (arr_size ws p) in
  forall vs vs' v,
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs = ok v ->
  @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs' = ok v.
Proof.
  move=> sz _ _ v [// | v1 v2 [_ /value_uinclE hu /List_Forall2_inv_l -> |]];
    rewrite /app_sopn_v /=; t_xrbindP=> // ??.
  move: hu => + /to_arrI[? [? [? /WArray.uincl_cast h]]] /WArray.uincl_copy H ?.
  by subst=> [[? [? [-> /= /h{h}[? [-> /= /H ->]]]]]].
Qed.

Lemma vuincl_app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
  all is_not_sarr tin ->
  forall vs vs' v, List.Forall2 value_uincl vs vs' ->
  app_sopn_v semi vs = ok v ->
  exists2 v' : values, app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v'.
Proof.
  move=> /vuincl_app_sopn_v_eq h ?? v /h{h}h/h{h}?.
  by exists v => //; exact: List_Forall2_refl.
Qed.

Lemma vuincl_copy ws p :
  let sz := Z.to_pos (arr_size ws p) in
  forall vs vs' v,
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs = ok v ->
  exists2 v' : values, @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs' = ok v' & List.Forall2 value_uincl v v'.
Proof.
  move=> ??? v /vuincl_copy_eq h/h{h}?.
  by exists v => //; exact: List_Forall2_refl.
Qed.

Section FORALL.
  Context  (T:Type) (P:T -> Prop).

  Fixpoint mk_forall (l:seq stype) : sem_prod l (exec T) -> Prop := 
    match l as l0 return sem_prod l0 (exec T) -> Prop with 
    | [::] => fun o => forall t, o = ok t -> P t
    | t::l => fun o => forall (x:sem_t t), @mk_forall l (o x)
    end.

  Lemma mk_forallP l f vargs t : @mk_forall l f -> app_sopn l f vargs = ok t -> P t.
  Proof.
    elim: l vargs f => [ | a l hrec] [ | v vs] //= f hall; first by apply hall.
    by t_xrbindP => w _;apply: hrec.
  Qed.

  Context (P2:T -> T -> Prop).

  Fixpoint mk_forall_ex (l:seq stype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop := 
    match l as l0 return sem_prod l0 (exec T) -> sem_prod l0 (exec T) -> Prop with 
    | [::] => fun o1 o2 => forall t, o1 = ok t -> exists2 t', o2 = ok t' & P2 t t' 
    | t::l => fun o1 o2 => forall (x:sem_t t), @mk_forall_ex l (o1 x) (o2 x)
    end.
  
  Lemma mk_forall_exP l f1 f2 vargs t : @mk_forall_ex l f1 f2 -> app_sopn l f1 vargs = ok t -> 
    exists2 t', app_sopn l f2 vargs = ok t' & P2 t t'.
  Proof.
    elim: l vargs f1 f2 => [ | a l hrec] [ | v vs] //= f1 f2 hall; first by apply hall.
    by t_xrbindP => w ->; apply/hrec.
  Qed.

  Fixpoint mk_forall2 (l:seq stype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop := 
    match l as l0 return sem_prod l0 (exec T) -> sem_prod l0 (exec T) -> Prop with 
    | [::] => fun o1 o2 => forall t1 t2, o1 = ok t1 -> o2 = ok t2 -> P2 t1 t2
    | t::l => fun o1 o2 => forall (x:sem_t t), @mk_forall2 l (o1 x) (o2 x)
    end.
  
  Lemma mk_forall2P l f1 f2 vargs t1 t2 : @mk_forall2 l f1 f2 -> app_sopn l f1 vargs = ok t1 -> app_sopn l f2 vargs = ok t2 -> P2 t1 t2.
  Proof.
    elim: l vargs f1 f2 => [ | a l hrec] [ | v vs] //= f1 f2 hall; first by apply hall.
    by t_xrbindP => w -> happ1 ? [<-]; apply: hrec happ1.
  Qed.

End FORALL.
