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

(* Lemma test1 (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) : *)
(*   px = transportb P e py -> transportf P e px = py. *)
(* Proof. *)
(* intros H. *)
(* rewrite H. *)
(* apply transportfbinv. *)
(* Qed. *)

(* Lemma test2 (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) : *)
(*   transportf P e px = py -> px = transportb P e py. *)
(* Proof. *)
(* intros H. *)
(* now rewrite <- H, transportbfinv. *)
(* Qed. *)

(* Very important lemma that was a pain to figure out how to state *)
Lemma transportf_PreShv (C : precategory) (F : PreShv C) (x y z : C)
  (e : x = y) (f : C⟦x,z⟧) (u : pr1 (pr1 F z)) : 
  transportf (λ x, pr1 (pr1 F x)) e (# (pr1 F) f u) =
  # (pr1 F) (transportf (@precategory_morphisms C^op z) e f) u.
Proof.
now induction e.
Qed.

Section cat_of_elems_theory.

Context {C : precategory} (hsC : has_homsets C).

Definition nat_trans_cat_of_elems {Γ Δ : PreShv C} (α : Γ --> Δ) :
  functor (∫ Γ) (∫ Δ) := cat_of_elems_on_nat_trans α.

Definition subst_functor {Γ Δ : PreShv C} (α : Γ --> Δ) :
  functor (PreShv (∫ Δ)) (PreShv (∫ Γ)).
Proof.
use pre_composition_functor.
- apply has_homsets_opp, has_homsets_cat_of_elems, hsC.
- now apply functor_opp, nat_trans_cat_of_elems.
Defined.

Lemma is_left_adjoint_subst_functor {Γ Δ : PreShv C} (α : Γ --> Δ) :
  is_left_adjoint (subst_functor α).
Proof.
use (RightKanExtension_from_limits _ _ _ LimsHSET). (* apply is slow here... *)
Defined.

(* This name is maybe not very good *)
Definition π {F G : PreShv C} (α : nat_trans (pr1 F) (pr1 G)) :=
   right_adjoint (is_left_adjoint_subst_functor α).

End cat_of_elems_theory.

Section types.

Context {C : precategory} (hsC : has_homsets C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 3).

(* Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Definition subst_type {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ :=
  subst_functor hsC σ A.

Local Notation "'1'" := (nat_trans_id _).
Notation "A ⦃ s ⦄" := (subst_type A s) (at level 50, format "A ⦃ s ⦄").

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

Definition special_mor {Γ : PreShv C} {I J : C} (f : C^op⟦I,J⟧) (ρ : pr1 (pr1 Γ I)) :
  ∫ Γ ⟦ make_ob J (# (pr1 Γ) f ρ), make_ob I ρ ⟧ := 
  make_mor (J,, # (pr1 Γ) f ρ) (I,, ρ) f (idpath (# (pr1 Γ) f ρ)).

Lemma make_ob_eq {Γ : PreShv C} (I : C) {x y} (e : x = y) :
  make_ob I x = @make_ob C Γ I y.
Proof.
apply pair_path_in2, e.
(* use total2_paths_f. *)
(* - apply (idpath I). *)
(* - exact e. *)
Defined.

(* upstream *)
Lemma key_lemma (X : UU) (P : X → UU) (x : X) (p q : P x) (e : p = q) :
  maponpaths pr1 (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

Lemma transportf_make_ob {Γ : PreShv C} {A : Γ ⊢} (I : C) {x y} (e : x = y)
  (u : pr1 (pr1 A (make_ob I x))) :
    transportf (λ x, pr1 (pr1 A (make_ob I x))) e u =
    transportf (λ x, pr1 (pr1 A x)) (make_ob_eq I e) u.
Proof.
now induction e.
Qed.

Lemma temp {Γ : PreShv C} {I : C} (ρ : pr1 (pr1 Γ I)) :
  make_ob I (# (pr1 Γ) (identity I) ρ) = make_ob I ρ.
Proof.
exact (make_ob_eq I (eqtohomot (functor_id Γ I) ρ)).
Defined.

Lemma special_mor_id {Γ : PreShv C} {I : C} (ρ : pr1 (pr1 Γ I)) :
  transportf (λ X, ∫ Γ⟦X, make_ob I ρ⟧) (temp ρ) (special_mor (identity I) ρ) =
  identity (make_ob I ρ).
Proof.
apply cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; cbn.
cbn in *.
unfold temp.
unfold make_ob_eq.
unfold pair_path_in2.
unfold maponpaths.
match goal with |-transportf ?XX (paths_rect _ _ _ _ _ ?YY) ?ZZ = _ => set (X := XX); set (Y := YY); set (Z := ZZ) end.
cbn in *.
now induction Y.
Qed.

Lemma temp_idpath  {Γ : PreShv C} {I : C} (ρ : pr1 (pr1 Γ I)) : maponpaths pr1 (temp ρ) = idpath _.
Proof.
apply key_lemma.
Qed.

Lemma special_mor_id' {Γ : PreShv C} {I : C} (ρ : pr1 (pr1 Γ I)) :
  special_mor (identity I) ρ = transportb (λ X, ∫ Γ⟦X, make_ob I ρ⟧) (temp ρ) (identity (make_ob I ρ)).
Proof.
now rewrite <- special_mor_id, transportbfinv.
Qed.

Lemma temp2 {Γ : PreShv C} {I J K : C^op} (ρ : pr1 (pr1 Γ I))
  (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
 make_ob _ (# (pr1 Γ) (f · g) ρ) = make_ob _ (# (pr1 Γ) g (# (pr1 Γ) f ρ)).
Proof.
exact (make_ob_eq K (eqtohomot (functor_comp Γ f g) ρ)).
Defined.

Lemma temp2_idpath {Γ : PreShv C} {I J K : C^op} (ρ : pr1 (pr1 Γ I))
  (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
    maponpaths pr1 (temp2 ρ f g) = idpath _.
Proof.
apply key_lemma.
Qed.

Lemma special_mor_comp {Γ : PreShv C} {I J K : C^op} (ρ : pr1 (pr1 Γ I))
  (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
    transportf (λ X, ∫ Γ⟦X, make_ob _ ρ⟧) (temp2 ρ f g) (special_mor (f · g) ρ) =
    special_mor g (# (pr1 Γ) f ρ) · special_mor f ρ.
Proof.
apply cat_of_elems_mor_eq.
simpl.
rewrite transportf_total2.
simpl.
match goal with |-transportf ?XX ?YY ?ZZ = _ => set (X := XX); set (Y := YY); set (Z := ZZ) end.
etrans.
apply (functtransportf pr1 (λ x, C⟦x,I⟧) Y).
assert (maponpaths pr1 Y = idpath _).
cbn.
apply temp2_idpath.
rewrite X0.
now rewrite idpath_transportf.
(* apply transport_source_precompose. *)
Qed.

Lemma special_mor_comp' {Γ : PreShv C} {I J K : C^op} (ρ : pr1 (pr1 Γ I))
  (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
   special_mor (f · g) ρ =
   transportb (λ X, ∫ Γ⟦X, make_ob _ ρ⟧) (temp2 ρ f g) (special_mor g (# (pr1 Γ) f ρ) · special_mor f ρ).
Proof.
now rewrite <- special_mor_comp, transportbfinv.
Qed.


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
    apply (# (pr1 A) (special_mor f (pr1 ρu)) (pr2 ρu)).
- split.
  + intros I; apply funextfun; intros [ρ u].
    use total2_paths_f.
    * exact (eqtohomot (functor_id Γ I) ρ).
    * etrans; [use transportf_make_ob|].
      etrans; [apply (transportf_PreShv (∫ Γ) A)|]; cbn.
      now rewrite (special_mor_id' ρ), transportfbinv, (functor_id A).
   + intros I J K f g; apply funextfun; intros [ρ u].
     use total2_paths_f.
     * exact (eqtohomot (functor_comp Γ f g) ρ).
     * etrans; [use transportf_make_ob|].
       etrans; [apply (transportf_PreShv (∫ Γ) A)|].
       rewrite (special_mor_comp' _ f g), transportfbinv.
       generalize u.
       apply eqtohomot, (functor_comp A (special_mor f ρ)  (special_mor g (# (pr1 Γ) f ρ))).
Defined.

Local Notation "Γ ⋆ A" := (@ctx_ext Γ A) (at level 3).

Definition p {Γ : PreShv C} (A : Γ ⊢) : (Γ ⋆ A) --> Γ.
Proof.
use mk_nat_trans.
- intros I X.
  apply (pr1 X).
- now intros I J f; apply funextsec.
Defined.

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
