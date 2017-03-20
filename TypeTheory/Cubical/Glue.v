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

Require Import TypeTheory.Cubical.PresheafSemantics.

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

