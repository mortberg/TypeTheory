Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

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

(* Section temp. *)

(* Variable (C D : precategory). *)

(* Lemma temp (F : functor C D) (a b : C) (f g : C⟦a,b⟧) (e : f = g) *)
(*   (P : C⟦a,b⟧ → UU) (p : P f) : UU. *)
(* Search transportf "mor". *)
(* Check (# F (transportf P e p)). *)

(* Check (# F ). *)

(*   # F (transportf _ _ X) = *)
(*   transportf P e (# F X). *)


 
(*   transportf X Y (# (pr1 A) Z u) = *)
(*   # (pr1 A) (transportf (λ XXX : Γ I, ∑ f : C ⟦ I, I ⟧, XXX = # Γ f ρ) Y Z) u *)


(* transportf : ∏ (X : UU) (P : X → UU) (x x' : X), x = x' → P x → P x' *)




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

Definition TypeIn (Γ : PreShv C) : UU := PreShv (∫ Γ).

Local Notation "Γ ⊢" := (TypeIn Γ) (at level 3).

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

Definition ctx_ext {Γ : PreShv C} (A : Γ ⊢) : PreShv C.
Proof.
simpl in *.
use mk_functor.
- mkpair.
  + simpl; intros I.
    use total2_hSet.
    * apply (Γ I).
    * intros ρ.
      apply (pr1 A (make_ob I ρ)).
  + simpl; intros I J f [ρ u].
    exists (# Γ f ρ).
    apply (# (pr1 A) (make_mor (J,,_) (I,,_) f (idpath _)) u).
- split.
  + intros I.
    apply funextfun; intros [ρ u].
cbn.
use total2_paths2_f.
exact (eqtohomot (functor_id Γ I) ρ).
Search transportf "functor".
match goal with |-transportf ?XX ?YY (# _ ?ZZ _) = _ => set (X := XX); set (Y := YY); set (Z := ZZ) end.
Check (∫ Γ ⟦ I,, # Γ (identity I) ρ, I,, ρ ⟧).
assert (HZ : transportf (fun XXX : pr1 (pr1 Γ I) => ∫ Γ ⟦ I,, XXX, I,, ρ ⟧) Y Z = identity (make_ob I ρ)).
cbn.
apply subtypeEquality.
intros x.
apply setproperty.
simpl.
cbn.
unfold Y, Z.
clear Y; clear Z; clear X.
unfold make_mor.
Search "transportf" "idpath".
rewrite transportf_total2.
simpl.
match goal with |-transportf ?XX ?YY ?ZZ = _ => set (X := XX); set (Y := YY); set (Z := ZZ) end.
cbn in *.
induction Y.
cbn.
apply idpath.
assert (moo : transportf X Y (# (pr1 A) Z u) =
              # (pr1 A) (transportf (λ XXX, ∫ Γ ⟦ I,, XXX, I,, ρ ⟧) Y Z) u).
unfold X.

Search (transportf (fun _ => _ _) _ _ = _ _).

admit.
etrans.
apply moo.
assert (# (pr1 A) (transportf (λ XXX , ∫ Γ ⟦ I,, XXX, I,, ρ ⟧) Y Z) = idfun _).
cbn in *.
admit.
admit.
+ admit.
Admitted.

End types.

Section Glue.

Local Notation "Γ ⊢" := (TypeIn Γ) (at level 3).

Variables (C : precategory) (hsC : has_homsets C).
Variables (Γ Δ : PreShv C) (σ : nat_trans (pr1 Δ) (pr1 Γ)).

Variables (A : Γ ⊢) (T : Δ ⊢).

Let Aσ : Δ ⊢ := subst_type hsC A σ.

Variables (w : nat_trans (pr1 T) (pr1 Aσ)).

(* This should be proved more directly for efficiency *)
Lemma PullbacksPreShv : Pullbacks [(∫ Γ)^op, HSET, has_homsets_HSET].
Proof.
apply Pullbacks_from_Lims, LimsFunctorCategory, LimsHSET.
Defined.

Definition Glue' : Γ ⊢.
Proof.
set (πAσ := π hsC σ Aσ : PreShv (∫ Γ)).
set (πT := π hsC σ T : PreShv (∫ Γ)).
transparent assert (f1 : (_⟦πT,πAσ⟧)).
  apply (φ_adj _ _ _ (is_left_adjoint_subst_functor hsC σ)).
  apply (nat_trans_comp (counit_from_left_adjoint (is_left_adjoint_subst_functor hsC σ) T) w).
transparent assert (f2 : (_⟦A,πAσ⟧)).
  apply (φ_adj _ _ _ (is_left_adjoint_subst_functor hsC σ) (identity _)).
apply (PullbackObject _ (PullbacksPreShv _ _ _ f1 f2)).
Defined.

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

Definition p : nat_trans (pr1 Γ) (pr1 Γ+).
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

Local Notation "'[0]'" := f0.
Local Notation "'[1]'" := f1.

Hypothesis (Hpe0 : e0 • p_F = nat_trans_id Id).
Hypothesis (Hpe1 : e1 • p_F = nat_trans_id Id).

Lemma pf0 : p • [0] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe0 I).
simpl in H.
rewrite <- (functor_id Γ).
eapply pathscomp0.
eapply pathsinv0.
eapply (functor_comp Γ).
unfold compose; simpl.
now rewrite H.
Qed.

Lemma pf1 : p • [1] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intro I.
assert (H := nat_trans_eq_pointwise Hpe1 I).
simpl in H.
rewrite <- (functor_id Γ).
eapply pathscomp0.
eapply pathsinv0.
eapply (functor_comp Γ).
unfold compose; simpl.
now rewrite H.
Qed.

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
