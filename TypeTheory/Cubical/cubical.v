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
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.LatticeObject.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.
Require Import UniMath.CategoryTheory.Monics.

Require Import TypeTheory.Cubical.PresheafSemantics.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section cubical.

Context {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).
Local Notation "c '⊗' d" := (BinProductObject _ (BinProducts_PreShv c d)) (at level 30) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 90) : cat.
Local Notation "1" := Terminal_PreShv.

(* Why is the formatting not working for this notation: *)
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (format "C ⟦ a , b ⟧", at level 50) : cat.

Let Ω : bounded_latticeob BinProducts_PreShv 1 Ω_PreShv := @Ω_PreShv_bounded_lattice C.

(* Assume that we have a sublattice of Ω *)
Context (FF : PreShv C) (i : FF --> Ω_PreShv) (Hi : isMonic i).
Context (meet_FF : FF ⊗ FF --> FF) (join_FF : FF ⊗ FF --> FF).
Context (bot_FF : 1 --> FF) (top_FF : 1 --> FF).
Context (Hmeet_FF : meet_FF · i = (i ×× i) · meet_mor Ω).
Context (Hjoin_FF : join_FF · i = (i ×× i) · join_mor Ω).
Context (Hbot_FF : bot_FF · i = bot_mor Ω).
Context (Htop_FF : top_FF · i = top_mor Ω).

Definition FF_lattice : bounded_latticeob BinProducts_PreShv 1 FF :=
  sub_bounded_latticeob BinProducts_PreShv Terminal_PreShv Hi Ω Hmeet_FF Hjoin_FF Hbot_FF Htop_FF.

(* Extract the top of the lattice *)
Definition FF1 {I} : pr1 (pr1 FF I) := pr1 top_FF I tt.
(* Local Notation "'1_FF'" := FF1. *)

(* Context restriction: Γ, φ |- *)
Definition ctx_restrict (Γ : PreShv C) (φ : Γ --> FF) : PreShv C.
Proof.
use mk_functor.
- mkpair.
  + simpl; intros I.
    exists (∑ ρ : pr1 ((pr1 Γ) I), pr1 φ I ρ = FF1).
    abstract (apply isaset_total2; [ apply setproperty | intros ρ; apply isasetaprop, setproperty ]).
  + simpl; intros I J f ρ.
    mkpair.
    * apply (# (pr1 Γ) f (pr1 ρ)).
    * abstract (
        etrans; [apply (eqtohomot (nat_trans_ax φ _ _ f) (pr1 ρ))|]; cbn;
        etrans; [apply maponpaths, (pr2 ρ)|];
        now apply (!eqtohomot (nat_trans_ax top_FF _ _ f) tt)).
- split.
  + intros I; apply funextsec; simpl; intro ρ.
    apply subtypeEquality; [ intros x; apply setproperty |]; simpl.
    now rewrite (functor_id Γ).
  + intros I J K f g; apply funextsec; simpl; intro ρ.
    apply subtypeEquality; [ intros x; apply setproperty |]; simpl.
    now rewrite (functor_comp Γ).
Defined.

Local Notation "Γ , φ" := (ctx_restrict Γ φ) (at level 30, format "Γ , φ").

Definition ι {Γ : PreShv C} (φ : Γ --> FF) : Γ,φ --> Γ.
Proof.
use mk_nat_trans.
- simpl; intros I.
  apply pr1.
- intros I J f; apply idpath.
Defined.

Lemma isMonic_ι (Γ : PreShv C) (φ : Γ --> FF) : isMonic (ι φ).
Proof.
intros Δ σ1 σ2 H.
apply (nat_trans_eq has_homsets_HSET); intro I.
apply funextsec; intro ρ.
apply subtypeEquality; [ intros x; apply setproperty |]; simpl.
apply (eqtohomot (nat_trans_eq_pointwise H I) ρ).
Qed.


(* Now assume that we have a cylinder functor on C *)

Local Notation "'Id'" := (functor_identity _).

Context (F : C ⟶ C).

Notation "_×I" := (F).
Arguments nat_trans_comp {_ _ _ _ _} _ _.

Context (p_F : _×I ⟹ Id) (e0 e1 : Id ⟹ _×I).
Context (Hpe0 : nat_trans_comp e0 p_F = nat_trans_id Id).
Context (Hpe1 : nat_trans_comp e1 p_F = nat_trans_id Id).

Definition ctx_plus (Γ : PreShv C) : PreShv C.
Proof.
use mk_functor.
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
    now apply (functor_comp Γ).
Defined.

Local Notation "Γ +" := (ctx_plus Γ) (at level 20).

Definition deg (Γ : PreShv C) : Γ --> Γ+.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (p_F I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax p_F).
Defined.

Definition face0 (Γ : PreShv C) : Γ+ --> Γ.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e0 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e0).
Defined.

Definition face1 (Γ : PreShv C) : Γ+ --> Γ.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e1 I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e1).
Defined.

Local Notation "'[0]'" := (face0 _).
Local Notation "'[1]'" := (face1 _).

Lemma deg_face0 (Γ : PreShv C) : nat_trans_comp (deg Γ) [0] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe0 I)|].
Qed.

Lemma deg_face1 (Γ : PreShv C) : nat_trans_comp (deg Γ) [1] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe1 I)|].
Qed.


End cubical.