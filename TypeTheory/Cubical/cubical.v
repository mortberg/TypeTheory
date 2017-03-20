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
