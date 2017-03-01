Require Import UniMath.Foundations.Basics.PartB.
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "'PSh' C" := (* (functor (opp_precat C) HSET) (at level 3). *)
  [C^op,HSET,has_homsets_HSET] (at level 3).
Arguments nat_trans_comp {_ _ _ _ _} _ _.
Local Notation "α • β" := (nat_trans_comp α β) (at level 50, format "α  •  β", left associativity).

(** Subobject classifier in a presheaf *)
Section omega_psh.

Context {C : precategory}.

Definition sieve_def (c : C) : UU.
Proof.
  use total2.
  - apply (Π (x : C) (f : C⟦x,c⟧), hProp).
  - intros S.
    apply (Π (x : C) (f : C⟦x,c⟧), S x f → Π (y : C) (f' : C⟦y,x⟧), S y (f' ;; f)).
Defined.

Lemma isaset_sieve (c : C) : isaset (sieve_def c).
Proof.
use isaset_total2.
- repeat (apply impred_isaset; intro); apply isasethProp.
- intros S; simpl; repeat (apply impred_isaset; intro); apply isasetaprop, propproperty.
Qed.

Definition sieve (c : C) : HSET := (sieve_def c,,isaset_sieve c).

Definition omega_psh : PSh C.
Proof.
use mk_functor.
- mkpair.
  + apply sieve.
  + simpl; intros a b f [S hS].
    mkpair.
    * intros y g.
      apply (S y (g ;; f)).
    * abstract (intros y g H z h; simpl; rewrite <- assoc; apply hS, H).
- split.
  + intros x; apply funextfun; intros [S hS]; simpl.
    apply subtypeEquality; simpl.
    * intros X; repeat (apply impred; intro); apply propproperty.
    * now repeat (apply funextsec; intro); rewrite id_right.
  + intros x y z f g; apply funextfun; intros [S hS]; simpl.
    apply subtypeEquality; simpl.
    * intros X; repeat (apply impred; intro); apply propproperty.
    * now repeat (apply funextsec; intro); rewrite <- assoc.
Defined.

End omega_psh.

(** Category of elements of a presheaf *)
Section cat_of_elems_def.

Context {C : precategory} (hsC : has_homsets C) (F : PSh C).

Definition cat_of_elems_ob_mor : precategory_ob_mor.
Proof.
exists (Σ (c : C), pr1 F c : hSet).
intros a b.
apply (Σ (f : C⟦pr1 a,pr1 b⟧), # (pr1 F) f (pr2 b) = pr2 a).
Defined.

Definition cat_of_elems_data : precategory_data.
Proof.
exists cat_of_elems_ob_mor.
split.
+ intros a.
  exists (identity _).
  abstract (now rewrite (functor_id F)).
+ intros a b c f g.
  exists (pr1 f ;; pr1 g).
  abstract (eapply pathscomp0;
      [apply (toforallpaths _ _ _ (functor_comp F _ _ _ (pr1 g) (pr1 f)) (pr2 c))|];
      eapply pathscomp0; [|apply (pr2 f)]; cbn;
      apply maponpaths, (pr2 g)).
Defined.

Lemma eq_mor_cat_of_elems (a b : cat_of_elems_data) (f g : _ ⟦a,b⟧) :
  pr1 f = pr1 g → f = g.
Proof.
now apply subtypeEquality; intros x; apply setproperty.
Qed.

Definition cat_of_elems : precategory.
Proof.
exists cat_of_elems_data.
abstract (repeat split; intros;
          apply subtypeEquality; try (intro; apply setproperty); simpl;
            [ apply id_left | apply id_right | apply assoc]).
Defined.

Lemma has_homsets_cat_of_elems : has_homsets cat_of_elems.
Proof.
intros a b.
apply isaset_total2.
+ now apply has_homsets_opp, hsC.
+ now intros f; apply isasetaprop, setproperty.
Qed.

End cat_of_elems_def.

Local Notation "∫ F" := (cat_of_elems F) (at level 3).

Section cat_of_elems_theory.

Context {C : precategory} (hsC : has_homsets C).

Definition nat_trans_cat_of_elems
  {F G : PSh C} (α : nat_trans (pr1 F) (pr1 G)) : functor (∫ F) (∫ G).
Proof.
mkpair.
- mkpair.
  + intros X; apply (pr1 X,, α (pr1 X) (pr2 X)).
  + intros a b f.
    exists (pr1 f).
    abstract (
      eapply pathscomp0;
        [ eapply pathsinv0,
                 (toforallpaths _ _ _ (nat_trans_ax α _ _ (pr1 f)) (pr2 b)) |];
      unfold compose; simpl; apply maponpaths, (pr2 f)).
- abstract (now split; intros ?; intros; apply eq_mor_cat_of_elems).
Defined.

(* Lemma nat_trans_cat_of_elems_id *)
(*   {F : PSh C} : nat_trans_cat_of_elems (nat_trans_id (pr1 F)) = functor_identity _. *)

Definition subst_functor {F G : PSh C} (α : nat_trans (pr1 F) (pr1 G)) :
  functor (PSh (∫ G)) (PSh (∫ F)).
Proof.
apply (pre_composition_functor _ _ _ (has_homsets_opp (has_homsets_cat_of_elems hsC G))).
now apply functor_opp, nat_trans_cat_of_elems.
Defined.

Lemma is_left_adjoint_subst_functor {F G : PSh C} (α : nat_trans (pr1 F) (pr1 G)) :
  is_left_adjoint (subst_functor α).
Proof.
use (RightKanExtension_from_limits _ _ _ LimsHSET). (* apply is slow here... *)
Defined.

(* This name is maybe not very good *)
Definition π {F G : PSh C} (α : nat_trans (pr1 F) (pr1 G)) :=
   right_adjoint (is_left_adjoint_subst_functor α).

End cat_of_elems_theory.

Section types.

Context {C : precategory} (hsC : has_homsets C).

Definition TypeIn (Γ : PSh C) : UU := PSh (∫ Γ).

Local Notation "Γ ⊢" := (TypeIn Γ) (at level 3).

(* Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Lemma subst_type {Γ Δ : PSh C} (A : Γ ⊢) (σ : nat_trans (pr1 Δ) (pr1 Γ)) : Δ ⊢.
Proof.
apply (subst_functor hsC σ A).
Defined.

Lemma subst_type_id (Γ : PSh C) (A : Γ ⊢) :
  subst_type A (nat_trans_id (pr1 Γ)) = A.
Proof.
apply functor_eq.
apply has_homsets_HSET.
simpl.
assert (foo : pr1 (functor_composite_data
    (functor_opp_data (nat_trans_cat_of_elems (nat_trans_id (pr1 Γ)))) (pr1 A)) =
  pr1 (pr1 A)).
cbn.
apply funextfun; intro a.
apply maponpaths.
apply pathsinv0.
apply tppr.
apply (total2_paths foo).
cbn.


End types.

Section Glue.

Local Notation "Γ ⊢" := (TypeIn Γ) (at level 3).

Variables (C : precategory) (hsC : has_homsets C).
Variables (Γ Δ : PSh C) (σ : nat_trans (pr1 Δ) (pr1 Γ)).

Variables (A : Γ ⊢) (T : Δ ⊢).

Let Aσ : Δ ⊢ := subst_type hsC A σ.

Variables (w : nat_trans (pr1 T) (pr1 Aσ)).

(* This should be proved more directly for efficiency *)
Lemma PullbacksPSh : Pullbacks [(∫ Γ)^op, HSET, has_homsets_HSET].
Proof.
apply Pullbacks_from_Lims, LimsFunctorCategory, LimsHSET.
Defined.

Definition Glue' : Γ ⊢.
Proof.
set (πAσ := π hsC σ Aσ : PSh (∫ Γ)).
set (πT := π hsC σ T : PSh (∫ Γ)).
transparent assert (f1 : (_⟦πT,πAσ⟧)).
  apply (φ_adj _ _ _ (is_left_adjoint_subst_functor hsC σ)).
  apply (nat_trans_comp (counit_from_left_adjoint (is_left_adjoint_subst_functor hsC σ) T) w).
transparent assert (f2 : (_⟦A,πAσ⟧)).
  apply (φ_adj _ _ _ (is_left_adjoint_subst_functor hsC σ) (identity _)).
apply (PullbackObject _ (PullbacksPSh _ _ _ f1 f2)).
Defined.

End Glue.

Section cubical.

Variables (C : precategory) (hsC : has_homsets C) (F : functor C C).

Local Notation "'Id'" := (functor_identity C).

Variable (p_F : nat_trans F Id).
Variable (e0 e1 : nat_trans Id F).

Variable (Γ : PSh C).

Definition Γplus : PSh C.
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
