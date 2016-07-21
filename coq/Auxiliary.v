
(** 

 Ahrens, Lumsdaine, Voevodsky 2015

Auxiliary background lemmas for the Ahrens/Lumsdaine/Voevodsky “Systems” project.  
Possibly some should be upstreamed to “UniMath” eventually.

*)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.

Require Import Systems.UnicodeNotations.

(** Redeclare this notation, along with a new scope. *)
Notation "ff ;; gg" := (compose ff gg)
  (at level 50, left associativity, format "ff  ;;  gg")
  : mor_scope.
Delimit Scope mor_scope with mor.
Bind Scope mor_scope with precategory_morphisms.
Open Scope mor_scope.


Lemma is_iso_comp_is_iso {C : precategory} {a b c : ob C}
  (f : C⟦a, b⟧) (g : C⟦b, c⟧) 
  : is_iso f -> is_iso g -> is_iso (f ;; g).
Proof.
  intros Hf Hg.
  apply (is_iso_comp_of_isos (isopair f Hf) (isopair g Hg)).
Defined.

Lemma functor_is_iso_is_iso {C C' : precategory} (F : functor C C')
    {a b : ob C} (f : C ⟦a,b⟧) (fH : is_iso f) : is_isomorphism (#F f).
Proof.
  apply (functor_on_iso_is_iso _ _ F _ _ (isopair f fH)).
Defined.


(** * Categorical equivalence *)

Section fix_stuff.

Variables A B C : precategory.
Hypothesis hsA : has_homsets A.
Hypothesis hsB : has_homsets B.
Hypothesis hsC : has_homsets C.
Variable F : functor A B.
Variable F' : functor B C.

Section adj_comp.

Hypothesis adF : is_left_adjoint F.
Hypothesis adF' : is_left_adjoint F'.

Let η : functor_precategory A A hsA ⟦ _ , _ ⟧ := unit_from_left_adjoint adF.
Let η' : functor_precategory _ _  hsB ⟦ _ , _ ⟧ := unit_from_left_adjoint adF'.
Let ε : functor_precategory _ _ hsB ⟦ _ , _ ⟧ := counit_from_left_adjoint adF.
Let ε' : functor_precategory _ _ hsC ⟦ _ , _ ⟧ := counit_from_left_adjoint adF'.
Let G := right_adjoint adF.
Let G' := right_adjoint adF'.

Let X := # (pre_composition_functor _ _ _ hsB hsB F) η'.
Let XR := # (post_composition_functor _ _ _ _ hsA G) X.
Let X' := # (pre_composition_functor _ _ _ hsB hsB G') ε.
Let XR' := # (post_composition_functor _ _ _ _ hsC F') X'. 


Definition unit_comp : (functor_precategory A A hsA) 
   ⟦ functor_identity A,
     functor_composite (functor_composite F F') (functor_composite G' G) ⟧.
Proof.
  apply (η ;;  XR).
Defined.

Definition counit_comp : (functor_precategory C C hsC) 
    ⟦functor_composite (functor_composite G' G)
       (functor_composite F F'), 
     functor_identity C⟧.
Proof.
  apply (XR' ;; ε').
Defined.

Lemma form_adjunction_comp : 
 form_adjunction (functor_composite F F') (functor_composite G' G) unit_comp
    counit_comp.
Proof.
  admit.
Admitted.


Definition comp_adjunction : is_left_adjoint (functor_composite F F').
Proof.
  exists (functor_composite G' G).
  exists (unit_comp ,, counit_comp).
  apply form_adjunction_comp.
Defined.

End adj_comp.

Section eqv_comp.

Hypothesis HF : adj_equivalence_of_precats F.
Hypothesis HF' : adj_equivalence_of_precats F'.

Definition left_adj_from_adj_equiv (X Y : precategory) (K : functor X Y)
         (HK : adj_equivalence_of_precats K) : is_left_adjoint K := pr1 HK.
Coercion left_adj_from_adj_equiv : adj_equivalence_of_precats >-> is_left_adjoint.


Let η : functor_precategory A A hsA ⟦ _ , _ ⟧ := unit_from_left_adjoint HF.
Let η' : functor_precategory _ _  hsB ⟦ _ , _ ⟧ := unit_from_left_adjoint HF'.
Let ε : functor_precategory _ _ hsB ⟦ _ , _ ⟧ := counit_from_left_adjoint HF.
Let ε' : functor_precategory _ _ hsC ⟦ _ , _ ⟧ := counit_from_left_adjoint HF'.
Let G := right_adjoint HF.
Let G' := right_adjoint HF'.
Let X := # (pre_composition_functor _ _ _ hsB hsB F) η'.
Let XR := # (post_composition_functor _ _ _ _ hsA G) X.
Let X' := # (pre_composition_functor _ _ _ hsB hsB G') ε.
Let XR' := # (post_composition_functor _ _ _ _ hsC F') X'. 



Definition comp_adj_equivalence_of_precats 
  : adj_equivalence_of_precats (functor_composite F F').
Proof.
  exists (comp_adjunction HF HF').
  mkpair.
  - apply (@is_functor_iso_pointwise_if_iso _ _ hsA).
    set (slsl := is_iso_comp_is_iso η XR). 
    apply slsl; clear slsl.
    + apply functor_iso_if_pointwise_iso. 
      apply (pr1 (pr2 HF)).
    + apply functor_iso_if_pointwise_iso.
      intro a. simpl.
      apply functor_is_iso_is_iso.
      apply (pr1 (pr2 HF')).
  - apply (@is_functor_iso_pointwise_if_iso _ _ hsC _ _ (XR';; ε')).
    set (slsl := is_iso_comp_is_iso XR' ε'). 
    apply slsl.
    + apply functor_iso_if_pointwise_iso.
      intro a. simpl.
      apply functor_is_iso_is_iso.
      apply (pr2 (pr2 HF)).
    + apply functor_iso_if_pointwise_iso.
      apply (pr2 (pr2 HF')).
Defined.

End eqv_comp.

End fix_stuff.



(** * Lemmas about transport, etc *)

Lemma idtoiso_transportf_family_of_morphisms (D : precategory)
      (A : UU) (B : A -> UU)
      (F : Π a, B a -> D)
      (d d' : D) (deq : d = d')
      (R : Π a (b : B a), D⟦ F a b, d⟧)
     
: transportf (λ x, Π a b, D⟦ F a b, x⟧)
             deq R =
  λ a b, R a b ;; idtoiso deq.
Proof.
  destruct deq.
  apply funextsec.
  intro. apply funextsec. intro.
  apply pathsinv0.
  apply id_right.
Qed.


Lemma pr1_transportf (A : UU) (B : A -> UU) (P : Π a, B a -> UU)
   (a a' : A) (e : a = a') (xs : Σ b : B a, P _ b):
   pr1 (transportf (fun x => Σ b : B x, P _ b) e xs) = 
     transportf (fun x => B x) e (pr1 xs).
Proof.
  destruct e; apply idpath.
Defined.

Lemma transportf_forall {A B} (C : A -> B -> Type)
  {x0 x1 : A} (e : x0 = x1) (f : forall y:B, C x0 y)
  : transportf (fun x => forall y, C x y) e f
  = fun y => transportf (fun x => C x y) e (f y).
Proof.
  destruct e; apply idpath.
Defined.

Lemma maponpaths_apply {A B} {f0 f1 : A -> B} (e : f0 = f1) (x : A)
  : maponpaths (fun f => f x) e
  = toforallpaths _ _ _ e x.
Proof.
  destruct e; apply idpath.
Defined.

Lemma maponpaths_eq_idpath
  : Π (T1 T2 : UU) (f : T1 -> T2) (t1 : T1) (e : t1 = t1)
       (H : e = idpath _ ), maponpaths f e = idpath _ .
Proof.
  intros.
  exact (maponpaths (maponpaths f) H).
Defined.

(** Useful lemma for binary functions, generalising e.g. [cancel_postcomposition]. 

TODO: look carefully for this in the library *)
Definition maponpaths_2 {X Y Z : Type} (f : X -> Y -> Z) {x x'} (e : x = x') y
  : f x y = f x' y
:= maponpaths (fun x => f x y) e.

Lemma transportf_comp_lemma (X : UU) (B : X -> UU) {A A' A'': X} (e : A = A'') (e' : A' = A'')
  (x : B A) (x' : B A')
  : transportf _ (e @ !e') x = x'
  -> transportf _ e x = transportf _ e' x'.
Proof.
  intro H.
  eapply pathscomp0. Focus 2.
    apply maponpaths. exact H.
  eapply pathscomp0. Focus 2.
    symmetry. apply transport_f_f.
  apply (maponpaths (fun p => transportf _ p x)).
  apply pathsinv0.
  eapply pathscomp0.
  - apply @pathsinv0, path_assoc. 
  - eapply pathscomp0. 
    apply maponpaths.
    apply pathsinv0l.
    apply pathscomp0rid.
Defined.

Lemma transportf_comp_lemma_hset (X : UU) (B : X -> UU) (A : X) (e : A = A)
  {x x' : B A} (hs : isaset X)
  : x = x'
  -> transportf _ e x = x'.
Proof.
  intros ex.
  apply @pathscomp0 with (transportf _ (idpath _) x).
    apply (maponpaths (fun p => transportf _ p x)).
    apply hs.
  exact ex.
Qed.

Lemma transportf_ext (X : UU) (B : X -> UU) (A A' : X) (e e' : A = A') p :
  e = e' -> transportf _ e p = transportf B e' p.
Proof.
  intro H; induction H; apply idpath.
Defined.

(** * Lemmas/definitions on (pre)categories *)

Definition preShv C := functor_precategory C^op HSET has_homsets_HSET.

(* TODO: perhaps rename e.g. [yoneda_eq]? *)
Definition yy {C : precategory} {hsC : has_homsets C}
  {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ yoneda _ hsC c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Arguments yy {_ _ _ _}.

Lemma yy_natural {C : precategory} {hsC : has_homsets C}
  (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # (yoneda _ hsC) f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

Lemma idtoiso_concat_pr (C : precategory) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso p ;; idtoiso q = idtoiso (p @ q).
Proof.
  apply pathsinv0.
  apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _ )).
Defined.

Lemma idtoiso_eq_idpath (C : precategory) (a : C) (e : a = a)
    (H : e = idpath _ )
  : identity a = idtoiso e.
Proof.
  rewrite H.
  apply idpath.
Qed.

Lemma cancel_postcomposition {C : precategory} {a b c : C} (f f' : a ⇒ b) (g : b ⇒ c)
: f = f' -> f ;; g = f' ;; g.
Proof.
  intro H. apply (maponpaths (fun f => f ;; g) H).
Defined.

Lemma idtoiso_postcompose_idtoiso_pre {C : precategory} {a b c : C} (g : a ⇒ b) (f : a ⇒ c)
              (p : b = c) :
  g = f ;; idtoiso (!p) -> g ;; idtoiso p = f.
Proof.
  induction p. simpl.
  rewrite id_right.
  induction 1.
  apply id_right.
Qed.


(** ** Lemmas on pullbacks *)

Section on_pullbacks.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variables a b c d : C.
  Variables (f : a ⇒ b) (g : a ⇒ c) (k : b ⇒ d) (h : c ⇒ d).

(*
      f
   a----b
 g |    | k
   |    |
   c----d
     h 
    
 *)

  Variable sqr_comm : f ;; k = g ;; h.
  Variable Pb : limits.pullbacks.isPullback k h f g sqr_comm.


  Lemma square_morphism_equal k' (e : k' = k) : f ;; k' = g ;; h.
  Proof.
    rewrite e. assumption.
  Defined.
  Lemma isPb_morphism_equal k' (e : k' = k) : 
        isPullback k' h f g (square_morphism_equal _ e).
  Proof.
    match goal with |[|- isPullback _ _ _ _ ?HH] => generalize HH end.
    rewrite e.
    intro.
    apply Pb.
  Defined.


  Local Definition Pbb : Pullback k h.
  Proof.
    unshelve refine (mk_Pullback _ _ _ _ _ _ _ ).
      - apply a.
      - apply f.
      - apply g.
      - apply sqr_comm.
      - apply Pb.
  Defined.
  
  Definition map_into_Pb {e : C} (x : e ⇒ b) (y : e ⇒ c)
  :  x ;; k = y ;; h → e ⇒ a.
  Proof.
    intro H.
    unshelve refine (PullbackArrow Pbb _ _ _ _ ).
    - apply x.
    - apply y.
    - apply H.
  Defined.
      
  Definition Pb_map_commutes_1 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; f = x.
  Proof.
    assert (P:=PullbackArrow_PullbackPr1 Pbb).
    apply P.
  Qed.

  Definition Pb_map_commutes_2 {e : C} (x : e ⇒ b) (y : e ⇒ c) H
  : map_into_Pb x y H ;; g = y.
  Proof.
    assert (P:=PullbackArrow_PullbackPr2 Pbb).
    apply P.
  Qed.

  Lemma map_into_Pb_unique (e : C) (x y : e ⇒ a)
  : x ;; f = y ;; f → x ;; g = y ;; g → x = y.
  Proof.
    intros H H'.
    set (T:=@map_into_Pb _ (x ;; f)(y ;; g)).
    assert  (TH : x ;; f ;; k = y ;; g ;; h).
    { rewrite H. repeat rewrite <- assoc. rewrite sqr_comm. apply idpath. }
    pathvia (T TH).
    apply PullbackArrowUnique. apply idpath. assumption.
    apply pathsinv0. apply PullbackArrowUnique. apply pathsinv0; assumption.
    apply idpath.
  Qed.

  Lemma postcomp_pb_with_iso (y : C) (r : y ⇒ d) (i : iso b y) (Hi : i ;; r = k) :
    Σ H : f ;; i ;; r = g ;; h, isPullback _ _ _ _ H.
  Proof.
    unshelve refine (tpair _ _ _ ).
    { eapply pathscomp0 ; [|apply sqr_comm].
      eapply pathscomp0. eapply pathsinv0; apply assoc.
      apply maponpaths. apply Hi.
    }
    apply (mk_isPullback _ ).    
    intros e s t HH.
    unshelve refine (tpair _ _ _ ).
    - unshelve refine (tpair _ _ _ ).
      set (T:= @map_into_Pb e).
      set (T':= T (s ;; inv_from_iso i) t).
      apply T'. { rewrite <- HH. rewrite <- assoc. apply maponpaths.
                  apply iso_inv_on_right. apply pathsinv0; assumption. }
                simpl.
      split.
      + assert (T1:= @Pb_map_commutes_1).
        eapply pathscomp0. apply assoc.
        rewrite T1.
        rewrite <- assoc.
        rewrite iso_after_iso_inv.
        apply id_right.
      + apply Pb_map_commutes_2.
    - intro t0.
      apply subtypeEquality.
      + intro. apply isapropdirprod; apply hs.
      + simpl.
        destruct t0 as [w [Ht1 Ht2]]; simpl in *.
        apply PullbackArrowUnique.
        * apply iso_inv_on_left.
          rewrite <- Ht1. apply assoc.
        * assumption.
Defined.    
 
End on_pullbacks.

Arguments map_into_Pb {_ _ _ _ _ _ _ _ _ } _ _ {_} _ _ _ .
Arguments map_into_Pb_unique {_ _ _ _ _ _ _ _ _} _ _ {_} _ _ _ _   .

Section Pullbacks_hSet.

(* TODO: does this already exist?

  If we had the standard pullback of hsets defined, this could be maybe better stated as the fact that P is a pullback if the map from P to the standard pullback is an iso. *)
Lemma isPullback_HSET {P A B C : HSET}
  (p1 : P ⇒ A) (p2 : P ⇒ B) (f : A ⇒ C) (g : B ⇒ C) (ep : p1 ;; f = p2 ;; g) 
  : (Π a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b)
  -> isPullback _ _ _ _ ep.
Proof.
  intros H X h k ehk.
  set (H_existence := fun a b e => pr1 (H a b e)).
  set (H_uniqueness := fun a b e x x' => base_paths _ _ (proofirrelevancecontr (H a b e) x x')).
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros hk hk'.
    apply subtypeEquality. { intro. apply isapropdirprod; apply setproperty. }
    destruct hk as [hk [eh ek]], hk' as [hk' [eh' ek']]; simpl.
    apply funextsec; intro x.
    refine (H_uniqueness (h x) (k x) _ (_,,_) (_,,_)).
    apply (toforallpaths _ _ _ ehk).
    split. apply (toforallpaths _ _ _ eh). apply (toforallpaths _ _ _ ek).
    split. apply (toforallpaths _ _ _ eh'). apply (toforallpaths _ _ _ ek').
  - mkpair. 
    + intros x. refine (pr1 (H_existence (h x) (k x) _)). apply (toforallpaths _ _ _ ehk).
    + simpl.
      split; apply funextsec; intro x.
      apply (pr1 (pr2 (H_existence _ _ _))). apply (pr2 (pr2 (H_existence _ _ _))).
Qed.


(* TODO: unify with [isPullback_HSET]? *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 ;; f = p2 ;; g)
    (pb : isPullback f g p1 p2 ep)
  : (Π a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (mk_Pullback _ _ _ _ _ _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypeEquality; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    refine (@toforallpaths unitset _ (fun _ => ab) (fun _ => ab') _ tt).
    refine (MorphismsIntoPullbackEqual pb _ _ _ _ );
    apply funextsec; intros []; cbn;
    (eapply @pathscomp0; [ eassumption | apply pathsinv0; eassumption]).
  - simple refine (_,,_).
    refine (_ tt).
    refine (PullbackArrow Pb (unitset : HSET)
      (fun _ => a) (fun _ => b) _).
    apply funextsec; intro; exact e.
    simpl; split.
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr1 Pb unitset).
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr2 Pb unitset).
Defined.

Lemma pullback_HSET_elements_unique {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    {ep : p1 ;; f = p2 ;; g}
    (pb : isPullback f g p1 p2 ep)
    (ab ab' : P : hSet)
    (e1 : p1 ab = p1 ab') (e2 : p2 ab = p2 ab')
  : ab = ab'.
Proof.
  set (temp := proofirrelevancecontr 
    (pullback_HSET_univprop_elements _ pb (p1 ab') (p2 ab')
        (toforallpaths _ _ _ ep ab'))).
  refine (maponpaths pr1 (temp (ab,, _) (ab',, _))).
  - split; assumption.
  - split; apply idpath.
Qed.


(* TODO: upstream this and the following lemma, and unify them with the converse implication about pullbacks. *)
Lemma square_commutes_preShv_to_pointwise {C : precategory} (hsC : has_homsets C)
    {X Y Z W : preShv C}
    {f : Y ⇒ X} {g : Z ⇒ X} {p1 : W ⇒ Y} {p2 : W ⇒ Z}
    (e : p1 ;; f = p2 ;; g)
    (c : C)
  : ((p1 : nat_trans _ _) c) ;; ((f : nat_trans _ _) c)
  = ((p2 : nat_trans _ _) c) ;; ((g : nat_trans _ _) c).
Proof.
  apply (nat_trans_eq_pointwise e).
Qed.

(* TODO: unify with the converse implication. *)
Lemma isPullback_preShv_to_pointwise {C : precategory} (hsC : has_homsets C)
    {X Y Z W : preShv C}
    {f : Y ⇒ X} {g : Z ⇒ X} {p1 : W ⇒ Y} {p2 : W ⇒ Z}
    {e : p1 ;; f = p2 ;; g} (pb : isPullback _ _ _ _ e)
    (c : C)
  : isPullback ((f : nat_trans _ _) c) ((g : nat_trans _ _) c)
      ((p1 : nat_trans _ _) c) ((p2 : nat_trans _ _) c)
      (square_commutes_preShv_to_pointwise hsC e c).
Proof.

  set (XR := isLimFunctor_is_pointwise_Lim C^op HSET has_homsets_HSET
            graphs.pullbacks.pushout_graph).
  set (XT1 := graphs.pullbacks.pullback_diagram _ f g).
  specialize (XR XT1).
  transparent assert
       (XH : (Π a : C^op,
        LimCone
          (colimits.diagram_pointwise C^op HSET has_homsets_HSET
             pullbacks.pushout_graph XT1 a))).

    { intro. apply LimConeHSET.  }
    specialize (XR XH).
    specialize (XR W). 

    set (XT := graphs.pullbacks.PullbCone _ _ _ _ p1 p2 e).
    specialize (XR XT).
    transparent assert (XTT : (isLimCone XT1 W XT)).
    { apply @graphs.pullbacks.equiv_isPullback_1.
      apply functor_category_has_homsets.
      assumption.
    }
    specialize (XR XTT c).

    
    intros S h k H.
    specialize (XR S).
    simpl in XR.
    transparent assert (
        HC :  (cone
              (colimits.diagram_pointwise C^op HSET has_homsets_HSET
                                               pushout_graph (pullback_diagram (preShv C) f g) c) S)).
    { use mk_cone.
      intro v.
      destruct v.
      - apply h.
      - simpl. apply (h ;; (pr1 f c)).
      - apply k.
      - intros u v e0; induction u; induction v; try induction e0.
        + apply idpath.
        + apply pathsinv0. apply H.
    }

    specialize (XR HC).
    mkpair.
  - exists (pr1 (iscontrpr1 XR)).
    cbn.
    split.
    + apply (pr2 (pr1 XR) One).
    + apply (pr2 (pr1 XR) Three).
  - intro t.
    apply subtypeEquality.
    + intro. apply isapropdirprod; apply has_homsets_HSET.
    + simpl.
      apply path_to_ctr.
      destruct t as [t [H1 H2]].
      intro v; destruct v; simpl.
      * apply H1.
      * rewrite  (assoc HSET).
        apply (@cancel_postcomposition HSET).
        apply H1.
      * apply H2.
Qed.      


End Pullbacks_hSet.

(**
will be an instance of a general lemma to be proved
   in UniMath
*)
Definition isaprop_Pullback (C : precategory) (H : is_category C)
           (a b c : C) (f : b ⇒ a) (g : c ⇒ a)
: isaprop (Pullback f g).
Proof.
  unfold Pullback.
  apply invproofirrelevance.
  unfold Pullback.
  intros Pb Pb'.
  apply subtypeEquality.
  - intro; apply isofhleveltotal2.
    + destruct H as [H1 H2]. apply H2.
    + intros; apply isaprop_isPullback.
  - apply (total2_paths  (isotoid _ H (iso_from_Pullback_to_Pullback Pb Pb' ))). 
    rewrite transportf_dirprod, transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    rewrite transportf_isotoid.
    rewrite inv_from_iso_iso_from_Pullback.
    destruct Pb as [Cone bla];
    destruct Pb' as [Cone' bla'];
    simpl in *.
    destruct Cone as [p [h k]];
    destruct Cone' as [p' [h' k']];
    simpl in *. 
    unfold from_Pullback_to_Pullback;
    rewrite PullbackArrow_PullbackPr2, PullbackArrow_PullbackPr1.
    apply idpath.
Qed.


Section bla.


(*   a'   b'
      f  /h
   a----b  b'
   |    |
 g |    | k
   |    |
   c----d
     j 

   and pb square a' b' c d, and h iso
    
   task: construct iso from a to a'

 *)
  
  Variable CC : precategory.
  Variables A B C D A' B' : CC.
  Variables (f : A ⇒ B) (g : A ⇒ C) (k : B ⇒ D) (j : C ⇒ D) (H : f ;; k = g ;; j)
            (pb : isPullback _ _ _ _ H).
  Variables (f' : A' ⇒ B') (g' : A' ⇒ C) (r : B' ⇒ D) (h : iso B B').
  Variable (H' : f' ;; r = g' ;; j).
  Variable (pb' : isPullback _ _ _ _ H').
  Variable (T : h ;; r = k).

  Definition map_to_2nd_pb : A ⇒ A'.
  Proof.
    unshelve refine (map_into_Pb H' pb' _ _ _  ).
    - exact (f ;; h).
    - exact g.
    - eapply pathscomp0. Focus 2. apply H.
      eapply pathscomp0. apply (!assoc _ _ _ _ _ _ _ _ ).
      apply maponpaths. apply T.
  Defined.

  Definition map_to_1st_pb : A' ⇒ A.
  Proof.
    unshelve refine (map_into_Pb H pb _ _ _ ).
    - exact (f';; inv_from_iso h).
    - exact g'.
    - eapply pathscomp0; [| apply H'].
      eapply pathscomp0; [ apply (!assoc _ _ _ _ _ _ _ _) |].
      apply maponpaths. apply iso_inv_on_right.
      apply (!T).
  Defined.

  Lemma inv1 : map_to_2nd_pb ;; map_to_1st_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H pb).
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      apply pathsinv0.
      apply iso_inv_on_left.
      unfold map_to_2nd_pb.
      match goal with |[ |- map_into_Pb ?H1 ?pb1 ?x1 ?y1 ?R1 ;; _ = _ ] => assert
           (T1:=@Pb_map_commutes_1 _ _ _ _ _ _ _ _ _ H' pb' _ x1 y1 R1) end.
      apply T1.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_2nd_pb.
      apply Pb_map_commutes_2.
Qed.

   Lemma inv2 : map_to_1st_pb ;; map_to_2nd_pb = identity _ .
  Proof.
    apply (map_into_Pb_unique  H' pb').
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_1.
      rewrite assoc.
      unfold map_to_1st_pb.
      rewrite Pb_map_commutes_1.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    - rewrite id_left.
      rewrite <- assoc.
      unfold map_to_2nd_pb.
      rewrite Pb_map_commutes_2.
      unfold map_to_1st_pb.
      apply Pb_map_commutes_2.
Qed.

Definition iso_to_second_pb : iso A A'.
Proof.
  exists map_to_2nd_pb.
  simple refine (is_iso_qinv _ map_to_1st_pb _ ).
  split.
  - apply inv1.
  - apply inv2.
Defined.

End bla.
  

Arguments map_into_Pb {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_1 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .
Arguments Pb_map_commutes_2 {_ _ _ _ _} _ _ _ _ _ _ {_} _ _ _ .

(** * Some tactics *)

Tactic Notation "etrans" := eapply pathscomp0.
Tactic Notation "rew_trans_@" := repeat (etrans ; [ apply transport_f_f |]).
Tactic Notation "sym" := apply pathsinv0.
Tactic Notation "assoc" := apply @pathsinv0, path_assoc.
Tactic Notation "cancel_postcomposition" := apply cancel_postcomposition.
