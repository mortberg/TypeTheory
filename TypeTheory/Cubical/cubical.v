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
Require Import UniMath.CategoryTheory.yoneda.

Require Import TypeTheory.Cubical.PresheafSemantics.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section cubical.

Context {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).
Local Notation "c '⊗' d" := (BinProductObject _ (@BinProducts_PreShv C c d)) (at level 30) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ (BinProducts_PreShv _ _) (BinProducts_PreShv _ _) f g) (at level 90) : cat.
Local Notation "1" := Terminal_PreShv.

(* Why is the formatting not working for this notation: *)
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (format "C ⟦ a , b ⟧", at level 50) : cat.

Definition binprod_delta x : x --> x ⊗ x :=
  BinProductArrow _ _ (identity x) (identity x).
Local Notation "'δ'" := (binprod_delta _).

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

Definition meet_mor {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ --> FF :=
  δ · (φ ×× ψ) · meet_FF.

Definition join_mor {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ --> FF :=
  δ · (φ ×× ψ) · join_FF.

Local Notation "φ ∧ ψ" := (meet_mor φ ψ) (at level 80, right associativity).
Local Notation "φ ∨ ψ" := (join_mor φ ψ) (at level 85, right associativity).

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

Definition ι {Γ : PreShv C} {φ : Γ --> FF} : Γ,φ --> Γ.
Proof.
use mk_nat_trans.
- simpl; intros I.
  apply pr1.
- intros I J f; apply idpath.
Defined.

Lemma isMonic_ι (Γ : PreShv C) (φ : Γ --> FF) : isMonic (@ι _ φ).
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

Notation "I +" := (F I) (at level 20).
Arguments nat_trans_comp {_ _ _ _ _} _ _.

Context (p_F : F ⟹ Id) (e₀ e₁ : Id ⟹ F).
Context (Hpe₀ : nat_trans_comp e₀ p_F = nat_trans_id Id).
Context (Hpe₁ : nat_trans_comp e₁ p_F = nat_trans_id Id).

(* We can compose F with a context, not sure if this is useful *)
Definition F_ctx (Γ : PreShv C) : PreShv C :=
  functor_opp F ∙ Γ.

Definition deg (Γ : PreShv C) : Γ --> F_ctx Γ.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (p_F I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax p_F).
Defined.

Definition face₀ (Γ : PreShv C) : F_ctx Γ --> Γ.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e₀ I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e₀).
Defined.

Definition face₁ (Γ : PreShv C) : F_ctx Γ --> Γ.
Proof.
mkpair.
- simpl; intro I; apply (# (pr1 Γ) (e₁ I)).
- intros I J f; simpl in *; rewrite <- !(functor_comp Γ).
  now apply maponpaths, pathsinv0, (nat_trans_ax e₁).
Defined.

Local Notation "'[0]'" := (face₀ _).
Local Notation "'[1]'" := (face₁ _).

Lemma deg_face₀ (Γ : PreShv C) : nat_trans_comp (deg Γ) [0] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₀ I)|].
Qed.

Lemma deg_face₁ (Γ : PreShv C) : nat_trans_comp (deg Γ) [1] = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₁ I)|].
Qed.



Let yo := yoneda C hsC.

(* e₀ defines a natural map from yo(I) to yo(I+) *)
Definition e₀_PreShv (I : C) : yo I --> yo (I +).
Proof.
use mk_nat_trans.
+ intros J f.
  exact (f · e₀ I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Definition e₁_PreShv (I : C) : yo I --> yo (I +).
Proof.
use mk_nat_trans.
+ intros J f.
  exact (f · e₁ I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Definition true : 1 --> FF.
Proof.
use mk_nat_trans.
+ intros I _.
  exact (@FF1 I).
+ intros I J f; cbn.
  apply funextsec; intros _.
  apply (eqtohomot (nat_trans_ax top_FF I J f) tt).
Defined.

(* TODO: define the notion "f classifies g" *)
Context (δ₀ : ∏ (I : C), yo (I +) --> FF).
Context (δ₁ : ∏ (I : C), yo (I +) --> FF).
Context (Hδ₀ : ∏ (I : C), e₀_PreShv I · δ₀ I = TerminalArrow _ · true).
Context (Hδ₁ : ∏ (I : C), e₁_PreShv I · δ₁ I = TerminalArrow _ · true).
(* TODO: The Hδ₀ square should be a pullback square *)

Definition yo_p {I : C} : yo (I+) --> yo I := # yo (p_F I).

(* TODO: generalize the rest so that it works in both directions *)

(* Open boxes *)
Definition box (I : C) (φ : yo I --> FF) : PreShv C :=
  yo (I+), ((δ₀ I) ∨ (yo_p · φ)).

(* This should follow from Hδ₁ *)
Lemma asdf (I : C) (φ : yo I --> FF) : (e₁_PreShv I · (δ₀ I ∨ yo_p · φ) = φ).
Admitted.

Definition subst_restriction {Γ Δ : PreShv C} (σ : Δ --> Γ) (φ : Γ --> FF) : Δ,(σ · φ) --> Γ,φ.
Admitted.

Definition box_subst {I J : C} (f : J --> I) (φ : yo I --> FF) : box J (# yo f · φ) --> box I φ.
Admitted.

Definition moo (Γ : PreShv C) (I : C) (φ : yo I --> FF) : yo(I),φ --> box I φ.
Proof.
use (_ · subst_restriction (e₁_PreShv I) (δ₀ I ∨ yo_p · φ)).
apply (transportf (λ x, yo I, x --> yo I,(e₁_PreShv I · (δ₀ I ∨ yo_p · φ))) (asdf I φ) (identity _)).
Defined.

Lemma boo (Γ : PreShv C) (I : C) (φ : yo I --> FF) (ρ : yo (I+) --> Γ) :
  moo Γ _ φ · ι · ρ = ι · (e₁_PreShv I · ρ).
Admitted.

(* Composition operation *)
Definition comp_op {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) : UU :=
    yo I ⊢ A⦃e₁_PreShv I · ρ⦄.

(* TODO: simplify *)
Definition comp_op_face {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ρ⦄⦃ι⦄} (c : comp_op ρ φ u) : UU.
Proof.
set (c' := subst_term hsC (@ι _ φ) c).
set (x1 := subst_term hsC (moo Γ I φ) u).
rewrite <- subst_type_comp in c'.
rewrite <- !subst_type_comp in x1.
apply (c' = transportf (λ x, yo I,φ ⊢ A⦃x⦄) (boo Γ I φ ρ) x1).
Defined.

(* Uniformity *)
Definition comp_op_uniform {Γ : PreShv C} {A : Γ ⊢}
  {I : C} (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (c : ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), comp_op ρ φ u) : UU.
Proof.
assert (J : C). admit.
assert (f : J --> I). admit.
set (fplus := # F f).
set (yo_fplus := # yo fplus).
set (yo_f := # yo f).
set (x1 := subst_term hsC yo_f (c I ρ φ u)).
set (ρ' := yo_fplus · ρ).
set (φ' := yo_f · φ).
set (u' := subst_term hsC (box_subst f φ) u).
assert (u'' : box J φ' ⊢ (A⦃ρ'⦄)⦃ι⦄).
rewrite <-! subst_type_comp in u'.
rewrite <-subst_type_comp.
assert (H : box_subst f φ · ι · ρ = ι · ρ').
admit.
apply (transportf (λ x, box J φ' ⊢ A⦃x⦄) H u').
set (x2 := c J ρ' φ' u'').
unfold comp_op in *.
rewrite <- subst_type_comp in x1.
assert (H2 : e₁_PreShv J · ρ' = yo_f · (e₁_PreShv I · ρ)).
admit.
apply (x1 = transportf (λ x, yo J ⊢ A⦃x⦄) H2 x2).
Admitted.

Definition comp_struct {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (f : ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), comp_op ρ φ u),
  ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄),
     comp_op_face (f _ ρ φ u) × comp_op_uniform ρ φ u f.
(* Proof. *)
(* use total2. *)
(* - apply (∏ (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), comp_op ρ φ u). *)
(* - intros c. *)
(*   apply (∏ (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), comp_op_law1 (c ρ φ u)). *)
(* Defined. *)

(* Filling operation *)
Definition fill_op {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) : UU :=
    yo (I+) ⊢ A⦃ρ⦄.

(* TODO: simplify *)
Definition fill_op_law1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ρ⦄⦃ι⦄} (f : fill_op ρ φ u) : UU :=
    subst_term hsC (@ι _ (δ₀ I ∨ yo_p · φ)) f = u.

Definition fill_struct {Γ : PreShv C} (A : Γ ⊢) (I : C) : UU :=
  ∏ (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄),
  ∑ (f : fill_op ρ φ u), fill_op_law1 f.
(* Proof. *)
(* use total2. *)
(* - apply (∏ (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), fill_op ρ φ u). *)
(* - intros f. *)
(*   apply (∏ (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), fill_op_law1 (f ρ φ u)). *)
(* (* TODO: add uniformity *) *)
(* Defined. *)

Definition fill_op_from_comp_op {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (c : comp_op ρ φ u) : fill_op ρ φ u.
Proof.
unfold comp_op in c.
unfold fill_op.
Admitted.

End cubical.