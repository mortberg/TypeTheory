Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

(* Require Import UniMath.MoreFoundations.Tactics. *)

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section upstream.

Lemma transportf_to_transportb (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) :
  px = transportb P e py -> transportf P e px = py.
Proof.
intros H.
rewrite H.
apply transportfbinv.
Qed.

Lemma transportb_to_transportf (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) :
  transportf P e px = py -> px = transportb P e py.
Proof.
intros H.
now rewrite <- H, transportbfinv.
Qed.

Lemma transportf_PreShv (C : precategory) (F : PreShv C) (x y z : C)
  (e : x = y) (f : C⟦x,z⟧) (u : pr1 (pr1 F z)) : 
  transportf (λ x, pr1 (pr1 F x)) e (# (pr1 F) f u) =
  # (pr1 F) (transportf (@precategory_morphisms C^op z) e f) u.
Proof.
now induction e.
Qed.

Lemma pr1_pair_path_in2 (X : UU) (P : X → UU) (x : X) (p q : P x) (e : p = q) :
  maponpaths pr1 (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

End upstream.

Section prelims.

Context {C : precategory} (hsC : has_homsets C) {Γ : PreShv C}.

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 3).

(* Any f : J → I and ρ : Γ I defines a morphism from (J,,# Γ ρ) to (I,,ρ) in ∫ Γ *)
Definition mor_to_el_mor {I J : C} (f : J --> I) (ρ : pr1 Γ I : hSet) :
  ∫ Γ ⟦ make_ob J (# (pr1 Γ) f ρ), make_ob I ρ ⟧ := 
  make_mor (J,,# (pr1 Γ) f ρ) (I,,ρ) f (idpath (# (pr1 Γ) f ρ)).

Lemma make_ob_eq {I : C} {x y} (e : x = y) :
  make_ob I x = @make_ob C Γ I y.
Proof.
apply pair_path_in2, e.
Defined.

Lemma transportf_make_ob {A : Γ ⊢} {I : C} {x y} (e : x = y)
  (u : pr1 (pr1 A (make_ob I x))) :
    transportf (λ x, pr1 (pr1 A (make_ob I x))) e u =
    transportf (λ x, pr1 (pr1 A x)) (make_ob_eq e) u.
Proof.
now induction e.
Qed.

Lemma make_ob_identity_eq {I : C} (ρ : pr1 (pr1 Γ I)) :
  make_ob I (# (pr1 Γ) (identity I) ρ) = make_ob I ρ.
Proof.
exact (make_ob_eq (eqtohomot (functor_id Γ I) ρ)).
Defined.

Lemma mor_to_el_mor_id {I : C} (ρ : pr1 (pr1 Γ I)) :
  mor_to_el_mor (identity I) ρ =
  transportb (λ X, ∫ Γ⟦X, make_ob I ρ⟧) (make_ob_eq (eqtohomot (functor_id Γ I) ρ)) (identity _).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl.
etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (make_ob_identity_eq _))|].
assert (H : maponpaths pr1 (make_ob_identity_eq ρ) = idpath _).
{ apply pr1_pair_path_in2. }
now rewrite H, idpath_transportf.
Qed.

Lemma mor_to_el_mor_comp_eq {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
 make_ob _ (# (pr1 Γ) (f · g) ρ) = make_ob _ (# (pr1 Γ) g (# (pr1 Γ) f ρ)).
Proof.
exact (make_ob_eq (eqtohomot (functor_comp Γ f g) ρ)).
Defined.

Lemma mor_to_el_mor_comp {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  mor_to_el_mor (f · g) ρ =
  transportb (λ X, ∫ Γ⟦X,_⟧) (mor_to_el_mor_comp_eq ρ f g)
             (mor_to_el_mor g (# (pr1 Γ) f ρ) · mor_to_el_mor f ρ).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl.
etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (mor_to_el_mor_comp_eq ρ f g))|].
assert (H : maponpaths pr1 (mor_to_el_mor_comp_eq ρ f g) = idpath _).
{ apply pr1_pair_path_in2. }
now rewrite H, idpath_transportf.
Qed.

End prelims.

Section types.

Context {C : precategory} (hsC : has_homsets C).

(* Γ ⊢ A is interpreted as a presheaf of ∫ Γ. In Coq this is written A : Γ ⊢ *)
Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).

Local Notation "'1'" := (nat_trans_id _).

(* The substitution functor *)
Definition subst_functor {Γ Δ : PreShv C} (σ : Δ --> Γ) :
  functor (PreShv (∫ Γ)) (PreShv (∫ Δ)).
Proof.
use pre_composition_functor.
- apply has_homsets_opp, has_homsets_cat_of_elems, hsC.
- apply functor_opp, (cat_of_elems_on_nat_trans σ).
Defined.

Lemma is_left_adjoint_subst_functor {Γ Δ : PreShv C} (σ : Δ --> Γ) :
  is_left_adjoint (subst_functor σ).
Proof.
use (RightKanExtension_from_limits _ _ _ LimsHSET). (* apply is slow here... *)
Defined.

(* The right adjoint to substitution *)
Definition π {Γ Δ : PreShv C} (σ : Δ --> Γ) :=
   right_adjoint (is_left_adjoint_subst_functor σ).

(* TODO: define the left adjoints as well? *)

(* Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Definition subst_type {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ :=
  subst_functor σ A.

Notation "A ⦃ s ⦄" := (subst_type A s) (at level 40, format "A ⦃ s ⦄").

Lemma subst_type_id (Γ : PreShv C) (A : Γ ⊢) : A⦃1⦄ = A.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros [c1 c2]; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
Qed.

Lemma subst_type_comp (Γ Δ Θ : PreShv C)
  (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) : A⦃σ1 · σ2⦄ = A⦃σ2⦄⦃σ1⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros [c1 c2]; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
Qed.

(* Context extension: given a context Γ and a type Γ ⊢ A define Γ.A *)
Definition ctx_ext {Γ : PreShv C} (A : Γ ⊢) : PreShv C.
Proof.
use mk_functor.
- mkpair.
  + simpl; intros I.
    use total2_hSet.
    * apply (pr1 Γ I).
    * intros ρ.
      apply (pr1 A (make_ob I ρ)).
  + intros I J f ρu.
    exists (# (pr1 Γ) f (pr1 ρu)).
    apply (# (pr1 A) (mor_to_el_mor f (pr1 ρu)) (pr2 ρu)).
- split.
  + intros I; apply funextfun; intros [ρ u].
    use total2_paths_f.
    * exact (eqtohomot (functor_id Γ I) ρ).
    * etrans; [use transportf_make_ob|].
      etrans; [apply (transportf_PreShv (∫ Γ) A)|]; cbn.
      now rewrite (mor_to_el_mor_id ρ), transportfbinv, (functor_id A).
   + intros I J K f g; apply funextfun; intros [ρ u].
     use total2_paths_f.
     * exact (eqtohomot (functor_comp Γ f g) ρ).
     * etrans; [use transportf_make_ob|].
       etrans; [apply (transportf_PreShv (∫ Γ) A)|].
       rewrite (mor_to_el_mor_comp _ f g), transportfbinv.
       generalize u; simpl in *.
       apply eqtohomot, (functor_comp A (mor_to_el_mor f ρ)  (mor_to_el_mor g (# (pr1 Γ) f ρ))).
Defined.

(* It would be nice to use the notation Γ.A here, but it doesn't seem to work *)
Local Notation "Γ ⋆ A" := (@ctx_ext Γ A) (at level 30).

(* Context projection *)
Definition p {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A --> Γ.
Proof.
use mk_nat_trans.
- intros I X.
  apply (pr1 X).
- now intros I J f; apply funextsec.
Defined.

(* Γ ⊢ a : A are interpreted as sections s : Γ --> Γ.A to p *)
Definition TermIn {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ s : Γ --> Γ ⋆ A, s · p = 1.

(* Direct definition of Γ ⊢ a : A *)
Definition TermInDirect {Γ : PreShv C} (A : Γ ⊢) : UU.
Proof.
use total2.
- apply (∏ (I : C) (ρ : pr1 (pr1 Γ I)), pr1 (pr1 A (make_ob I ρ))).
- intros a.
  apply (∏ (I J : C) (f : J --> I) (ρ : pr1 (pr1 Γ I)),
           # (pr1 A) (mor_to_el_mor f ρ) (a I ρ) = a J (# (pr1 Γ) f ρ)).
Defined.

Local Notation "Γ ⊢ A" := (@TermInDirect Γ A) (at level 50).

Lemma TermInDirect_to_TermIn {Γ : PreShv C} (A : Γ ⊢) : TermInDirect A → TermIn A.
Proof.
intros [a p].
mkpair.
+ use mk_nat_trans.
  - intros I ρ.
    apply (ρ,,a I ρ).
  - intros I J f.
    apply funextfun; intro ρ; apply pair_path_in2.
    now rewrite p.
+ abstract (apply (nat_trans_eq has_homsets_HSET);
            now intros I; simpl; apply funextfun).
Defined.

(* TODO: prove this *)
(* Lemma TermIn_to_TermInDirect {Γ : PreShv C} (A : Γ ⊢) : Γ ⊢ A → TermInDirect A. *)
(* Proof. *)
(* intros [a p]. *)
(* mkpair. *)
(* - intros I ρ. *)
(*   apply (transportf (λ x, pr1 (pr1 A (make_ob I x))) (eqtohomot (nat_trans_eq_pointwise p I) ρ) (pr2 (pr1 a I ρ))). *)
(* - intros I J f ρ. *)
(*   generalize (fiber_paths (!(eqtohomot (nat_trans_ax a I J f) ρ))). *)
(*   intros e. *)
(*   set (e' := (functtransportf pr1 (λ x, pr1 (pr1 (pr1 A) (make_ob J x))) (! eqtohomot (nat_trans_ax a I J f) ρ)(# (pr1 A) (mor_to_el_mor f (pr1 (pr1 a I ρ))) (pr2 (pr1 a I ρ))))). *)
(*   set (e'' := pathscomp0 e' e). *)
(*   etrans. *)
(*   Focus 2. *)
(*   eapply maponpaths, e''. *)
(*   apply pathsinv0. *)
(*   apply (transportf_to_transportb _ (λ x, pr1 ((pr1 A) (make_ob J x)))). *)
(*   clear e e' e''. *)
(*   unfold transportb. *)
(*   apply pathsinv0. *)
(*   etrans. *)
(*   apply transportf_make_ob. *)
(*   etrans. *)
(*   apply (transportf_PreShv (∫ Γ) A). *)
(* admit. *)
(* Admitted. *)

Definition q {Γ : PreShv C} (A : Γ ⊢) : Γ ⋆ A ⊢ A⦃p⦄.
Proof.
(* apply TermInDirect_to_TermIn. *)
mkpair.
+ intros I ρ.
  apply (pr2 ρ).
+ abstract (intros I J f ρ; cbn; apply map_on_two_paths; trivial;
            now apply cat_of_elems_mor_eq).
Defined.

(* Below is a direct definition that is very slow *)
(* Definition q {Γ : PreShv C} (A : Γ ⊢) : Γ ⋆ A ⊢ A⦃p⦄. *)
(* Proof. *)
(* mkpair. *)
(* - use mk_nat_trans. *)
(*   + intros I ρ. *)
(*     exists ρ. *)
(*     apply (pr2 ρ). *)
(*   + abstract (intros I J f; apply funextsec; intro ρ; *)
(*               apply pair_path_in2; cbn;  *)
(*               apply map_on_two_paths; trivial; *)
(*               now apply cat_of_elems_mor_eq). *)
(* (* This abstract is VERY slow *) *)
(* - abstract (apply (nat_trans_eq has_homsets_HSET); intros I; simpl; *)
(*             apply funextsec; intro ρ; apply idpath). *)
(* Defined. *)


(* Given Γ ⊢ a : A and a substitution σ : Δ → Γ we get Δ ⊢ aσ : Aσ *)
Definition subst_term {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) : Δ ⊢ A⦃σ⦄.
Proof.
(* mkpair. *)
(* + cbn in *. *)
(*   use mk_nat_trans. *)
(* - simpl; intros I ρ. *)
(*   mkpair. *)
(*   apply ρ. *)
(*   induction a as [a pa]. *)
(*   cbn in *. *)
(*   set (pr2 (pr1 a I (σ I ρ))). *)
(*   cbn in *. *)
(*   set (e := eqtohomot (nat_trans_eq_pointwise pa I) (σ I ρ)). *)
(*   cbn in e. *)
(*   set (x := pr2 (a _ (σ I ρ))). *)
(*   cbn in x. *)
(*   apply (transportf (λ x, pr1 ((pr1 A) (make_ob I x))) e x). *)
(* - intros I J f. *)
(*   cbn in *. *)
  (* apply funextsec; intro ρ. *)
  (* apply pair_path_in2; cbn. *)
  (* cbn. *)

(* apply TermInDirect_to_TermIn. *)
mkpair.
- intros I ρ.
  simpl in *.
  apply (pr1 a _ (pr1 σ I ρ)).
- intros I J f ρ.  
  cbn in *.
  generalize (pr2 a I J f (σ _ ρ)).
  set (H := eqtohomot (nat_trans_ax σ I J f) ρ).
  cbn in *.
  intros H2.
  match goal with |- ?XX = ?YY => set (X := XX); set (Y := YY) end.
  cbn in *.
  set (W := # (pr1 A) (mor_to_el_mor f (σ I ρ)) (pr1 a I (σ I ρ))).
  pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) H W).
  { unfold X, W, H.
  apply pathsinv0.
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq.
  cbn in *.
  match goal with |- get_mor (transportf _ ?XXX _) = _ => set (XX := XXX) end.
  unfold mor_to_el_mor, make_mor.
  rewrite transportf_total2.
  cbn.
  assert (transportf (λ x : ∑ c : C, pr1 (Γ c), C ⟦ pr1 x, I ⟧) XX f =
          transportf (λ x, C ⟦ x, I ⟧) (maponpaths pr1 XX) f).
  induction XX.
  trivial.
  etrans.
  apply X0.
  assert (HHH : maponpaths pr1 XX = idpath _).
  apply pr1_pair_path_in2.
  rewrite HHH.
  now rewrite idpath_transportf.
  }
  set (W2 := pr1 a J (# (pr1 Γ) f (σ I ρ))).
  apply pathsinv0.
  pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) H W2).
  { unfold  Y, H, W2.
    apply pathsinv0.
    Check (pr1 a J (# (pr1 Γ) f (σ I ρ))).
    admit. }
  now apply maponpaths.
Admitted.

Definition subst_pair {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A.
Proof.
use mk_nat_trans.
- simpl; intros I ρ.
  mkpair.
  + apply (pr1 σ _ ρ).
  + apply (pr1 a I ρ).
- intros I J f.
  apply funextsec; intro ρ; cbn in *.
  use total2_paths2_f.
  apply (eqtohomot (nat_trans_ax σ I J f) ρ).
  set (H:=pr2 a I J f ρ).
  cbn in H.
  etrans.
  eapply maponpaths.
  apply (!H).
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
    apply cat_of_elems_mor_eq.
  cbn.
  rewrite transportf_total2.
  cbn.
  match goal with |- transportf _ ?XXX _ = _ => set (XX := XXX) end.
  assert (transportf (λ x : ∑ c : C, pr1 (Γ c), C ⟦ pr1 x, I ⟧) XX f =
          transportf (λ x, C ⟦ x, I ⟧) (maponpaths pr1 XX) f).
  induction XX.
  trivial.
  etrans.
  apply X.
  assert (HHH : maponpaths pr1 XX = idpath _).
  apply pr1_pair_path_in2.
  rewrite HHH.
  now rewrite idpath_transportf.
Defined.

Lemma test {Γ : PreShv C} {A : Γ ⊢} : subst_pair p (q A) = 1.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intros I.
apply funextsec; intro ρ; cbn.
apply pathsinv0, tppr.
Qed.





              
End types.

Section Glue.

Variables (C : precategory) (hsC : has_homsets C).
Variables (Γ Δ : PreShv C) (σ : nat_trans (pr1 Δ) (pr1 Γ)).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 3).

Variables (A : Γ ⊢) (T : Δ ⊢).

Let Aσ : Δ ⊢ := subst_type hsC A σ.

Variables (w : nat_trans (pr1 T) (pr1 Aσ)).

(* This should be proved more directly for efficiency *)
Lemma PullbacksPreShv : Pullbacks [(∫ Γ)^op, HSET, has_homsets_HSET].
Proof.
apply Pullbacks_from_Lims, LimsFunctorCategory, LimsHSET.
Defined.

(* Definition Glue' : Γ ⊢. *)
(* Proof. *)
(* set (πAσ := π hsC σ Aσ : PreShv (∫ Γ)). *)
(* set (πT := π hsC σ T : PreShv (∫ Γ)). *)
(* transparent assert (f1 : (_⟦πT,πAσ⟧)). *)
(*   apply (φ_adj _ _ (is_left_adjoint_subst_functor hsC σ)). *)
(*   apply (nat_trans_comp (counit_from_left_adjoint (is_left_adjoint_subst_functor hsC σ) T) w). *)
(* transparent assert (f2 : (_⟦A,πAσ⟧)). *)
(*   apply (φ_adj _ _ _ (is_left_adjoint_subst_functor hsC σ) (identity _)). *)
(* apply (PullbackObject _ (PullbacksPreShv _ _ _ f1 f2)). *)
(* Defined. *)

End Glue.

Section cubical.

Variables (C : precategory) (hsC : has_homsets C) (F : functor C C).

Local Notation "'Id'" := (functor_identity C).

Variable (p_F : nat_trans F Id).
Variable (e0 e1 : nat_trans Id F).

Variable (Γ : PreShv C).

Definition Γplus : PreShv C.
Proof.
mkpair.
- mkpair.
  + intro I.
    apply (pr1 Γ (F I)).
  + simpl; intros I J f.
    apply (# (pr1 Γ) (# F f)).
- split.
  + now intros I; simpl; rewrite (functor_id F), (functor_id Γ).
  + intros I J K f g; simpl in *.
    unfold compose; simpl.
    rewrite (functor_comp F).
    apply (functor_comp Γ).
Defined.

Local Notation "'Γ+'" := Γplus.

Definition p' : nat_trans (pr1 Γ) (pr1 Γ+).
mkpair.
- simpl; intro I; apply (# (pr1 Γ)  (p_F I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax p_F).
Defined.

Definition f0 : nat_trans (pr1 Γ+) (pr1 Γ).
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e0 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e0).
Defined.

Definition f1 : nat_trans (pr1 Γ+) (pr1 Γ).
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e1 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e1).
Defined.

(* Local Notation "'[0]'" := f0. *)
(* Local Notation "'[1]'" := f1. *)

(* Hypothesis (Hpe0 : e0 • p_F = nat_trans_id Id). *)
(* Hypothesis (Hpe1 : e1 • p_F = nat_trans_id Id). *)

(* Lemma pf0 : p • [0] = identity Γ. *)
(* Proof. *)
(* apply (nat_trans_eq has_homsets_HSET). *)
(* simpl; intro I. *)
(* assert (H := nat_trans_eq_pointwise Hpe0 I). *)
(* simpl in H. *)
(* rewrite <- (functor_id Γ). *)
(* eapply pathscomp0. *)
(* eapply pathsinv0. *)
(* eapply (functor_comp Γ). *)
(* unfold compose; simpl. *)
(* now rewrite H. *)
(* Qed. *)

(* Lemma pf1 : p • [1] = identity Γ. *)
(* Proof. *)
(* apply (nat_trans_eq has_homsets_HSET). *)
(* simpl; intro I. *)
(* assert (H := nat_trans_eq_pointwise Hpe1 I). *)
(* simpl in H. *)
(* rewrite <- (functor_id Γ). *)
(* eapply pathscomp0. *)
(* eapply pathsinv0. *)
(* eapply (functor_comp Γ). *)
(* unfold compose; simpl. *)
(* now rewrite H. *)
(* Qed. *)

(* Section alternative_version. *)
(* Hypothesis (Hpe0 : p_F • e0 = nat_trans_id F). *)
(* Hypothesis (Hpe1 : p_F • e1 = nat_trans_id F). *)

(* Lemma pf0 : [0] • p = nat_trans_id Γ+. *)
(* Proof. *)
(* apply (nat_trans_eq has_homsets_HSET). *)
(* simpl; intro I. *)
(* assert (H := nat_trans_eq_pointwise Hpe0 I). *)
(* simpl in H. *)
(* assert (H1 : # Γ (e0 I) ;; # Γ (p_F I) = # Γ (identity (F I))). *)
(* rewrite <- H. *)
(* apply pathsinv0. *)
(* apply (functor_comp Γ). *)
(* rewrite (functor_id Γ) in H1. *)
(* apply H1. *)
(* Qed. *)

(* Lemma pf1 : [1] • p = nat_trans_id Γ+. *)
(* Proof. *)
(* apply (nat_trans_eq has_homsets_HSET). *)
(* simpl; intro I. *)
(* assert (H := nat_trans_eq_pointwise Hpe1 I). *)
(* simpl in H. *)
(* assert (H1 : # Γ (e1 I) ;; # Γ (p_F I) = # Γ (identity (F I))). *)
(* rewrite <- H. *)
(* apply pathsinv0. *)
(* apply (functor_comp Γ). *)
(* rewrite (functor_id Γ) in H1. *)
(* apply H1. *)
(* Qed. *)
(* End alternative_version. *)

End cubical.
