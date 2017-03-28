Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

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

Lemma nat_trans_eq {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_nat_trans, hs.
Defined.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section lattice_prelim.

Context {C : precategory} (BPC : BinProducts C) (TC : Terminal C).
Context {L : C} (l : bounded_latticeob BPC TC L).

Local Notation "c '⊗' d" := (BinProductObject C (BPC c d)) (at level 75) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ _ _ f g) (at level 80) : cat.
Local Notation "1" := (identity _) : cat.

Let π1 {x y} : C⟦x ⊗ y,x⟧ := BinProductPr1 _ (BPC x y).
Let π2 {x y} : C⟦x ⊗ y,y⟧ := BinProductPr2 _ (BPC x y).

(* Definition binprod_assoc (x y z : C) : C⟦(x ⊗ y) ⊗ z,x ⊗ (y ⊗ z)⟧ := *)
(*   BinProductArrow _ _ (π1 · π1) (BinProductArrow _ _ (π1 · π2) π2). *)
Let α {x y z} : C⟦(x ⊗ y) ⊗ z,x ⊗ (y ⊗ z)⟧ := binprod_assoc x y z.

(* Definition binprod_delta (x : C) : C⟦x,x ⊗ x⟧ := *)
(*   BinProductArrow _ _ (identity x) (identity x). *)
Let δ {x} : C⟦x,x ⊗ x⟧ := binprod_delta x.

(* Definition binprod_swap (x y : C) : C⟦x ⊗ y,y ⊗ x⟧ := *)
(*   BinProductArrow _ _ (BinProductPr2 _ _) (BinProductPr1 _ _). *)
Let τ {x y} : C⟦x ⊗ y,y ⊗ x⟧ := binprod_swap x y.

Let ι {x : C} : C⟦x,TC ⊗ x⟧ :=
  BinProductArrow _ _ (TerminalArrow _) (identity x).

Lemma join_mor_top_mor : ι · (top_mor l ×× identity _) · join_mor l = ι · π1 · top_mor l.
Proof.
set (H1 := islunit_join_mor_bot_mor _ _ l).
unfold islunit_cat in H1.
set (H2 := join_mor_absorb_meet_mor _ l).
set (H3 := meet_mor_absorb_join_mor _ l).
unfold isabsorb_cat in *.
rewrite <- H1.
Admitted.

(* Lemma join_mor_top_mor : Lmax l (Ltop l) x = Ltop l. *)
(* Proof. *)
(* intros x. *)
(* now rewrite <- (islunit_Lmin_Ltop x), Lmax_absorb. *)
(* Qed. *)

(* Lemma Lmin_Lbot (x : X) : Lmin l (Lbot l) x = Lbot l. *)
(* Proof. *)
(* intros x. *)
(* now rewrite <- (islunit_Lmax_Lbot x), Lmin_absorb. *)
(* Qed. *)

End lattice_prelim.

Section cubical.

Context {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).
Local Notation "c '⊗' d" := (BinProductObject _ (@BinProducts_PreShv C c d)) (at level 30) : cat.
Local Notation "f '××' g" := (BinProductOfArrows _ (BinProducts_PreShv _ _) (BinProducts_PreShv _ _) f g) (at level 90) : cat.
Local Notation "1" := Terminal_PreShv.

Lemma subst_term_comp' {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ)
  {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term _ σ1 (subst_term hsC σ2 a) =
  transportf (λ x, Θ ⊢ x) (subst_type_comp _ σ1 σ2 A) (subst_term _ (σ1 · σ2) a).
Proof.
apply pathsinv0.
apply transportf_to_transportb.
apply subst_term_comp.
Qed.

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

Lemma comp_join {Γ Δ : PreShv C} (f : Γ --> Δ) (g h : Δ --> FF) :
  f · (g ∨ h) = (f · g ∨ f · h).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro I.
now apply funextsec.
Qed.

(* These equations are standard equations for lattices *)
Lemma eqn1 (I : C) (x : pr1 (pr1 FF I)) :
  pr1 join_FF I (dirprodpair (pr1 bot_FF I tt) x) = x.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (islunit_join_mor_bot_mor _ _ FF_lattice) I) x).
Qed.

Lemma eqn2 (I : C) (x : pr1 (pr1 FF I)) :
  pr1 meet_FF I (dirprodpair (pr1 top_FF I tt) x) = x.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (islunit_meet_mor_top_mor _ _ FF_lattice) I) x).
Qed.

Lemma eqn3 (I : C) (x : pr1 ((pr1 FF) I)) (y : pr1 ((pr1 FF) I)) :
  pr1 join_FF I (dirprodpair x (pr1 meet_FF I (dirprodpair x y))) = x.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (join_mor_absorb_meet_mor _ FF_lattice) I) (dirprodpair x y)).
Qed.

Lemma key_eqn (I : C) (x : pr1 ((pr1 FF) I)) : pr1 join_FF I (dirprodpair FF1 x) = FF1.
Proof.
now rewrite <- (eqn2 _ x), eqn3.
Qed.

Lemma foo (Γ : PreShv C) (φ : Γ --> FF) : (TerminalArrow Γ · top_FF ∨ φ) = TerminalArrow Γ · top_FF.
Proof.
apply (nat_trans_eq has_homsets_HSET); intro I.
apply funextsec; intro ρ.
apply key_eqn.
Qed.

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

Definition join_subst {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ,φ --> Γ,(φ ∨ ψ).
Proof.
use mk_nat_trans.
- intros I ρ.
  exists (pr1 ρ).
  cbn.
  etrans; [apply maponpaths, (pathsdirprod (pr2 ρ) (idpath _))|].
  exact (eqtohomot (nat_trans_eq_pointwise (join_mor_top_mor _ _ FF_lattice) I) (pr1 ψ I (pr1 ρ))).
- intros I J f.
  apply funextsec; intro ρ.
  now apply subtypeEquality; [intros x; apply setproperty|].
Defined.

(* Now assume that we have a cylinder functor on C *)

Local Notation "'Id'" := (functor_identity _).

Context (F : C ⟶ C).

Notation "I +" := (F I) (at level 20).
Arguments nat_trans_comp {_ _ _ _ _} _ _.

(* We assume a cylinder functor F *)
Context (p_F : F ⟹ Id) (e₀ e₁ : Id ⟹ F).
Context (Hpe₀ : nat_trans_comp e₀ p_F = nat_trans_id Id).
Context (Hpe₁ : nat_trans_comp e₁ p_F = nat_trans_id Id).

(* We also assume a conjunction map *)
Context (m : F ∙ F ⟹ F).
Context (He₁m : nat_trans_comp (post_whisker e₁ F) m = nat_trans_id F).
Context (He₁m' : nat_trans_comp (pre_whisker F e₁) m = nat_trans_id F).
Context (He₀m : nat_trans_comp (post_whisker e₀ F) m = nat_trans_comp p_F e₀).
Context (He₀m' : nat_trans_comp (pre_whisker F e₀) m = nat_trans_comp p_F e₀).

Goal ∏ (I : C), UU.
intros.
generalize (nat_trans_eq_pointwise He₁m I).
generalize (nat_trans_eq_pointwise He₁m' I).
generalize (nat_trans_eq_pointwise He₀m I).
generalize (nat_trans_eq_pointwise He₀m' I).
generalize (nat_trans_eq_pointwise Hpe₀ I).
cbn.
Abort.

Lemma isMonic_e₀ I : isMonic (e₀ I).
Proof.
intros J f g H.
set (H1 := nat_trans_ax e₀ J I f).
set (H2 := nat_trans_ax p_F J I f).
set (H3 := nat_trans_eq_pointwise Hpe₀ I).
set (H4 := nat_trans_eq_pointwise Hpe₀ J).
cbn in *.
rewrite H1 in H.
generalize (cancel_postcomposition _ _ (p_F I) H); cbn.
now rewrite <-!assoc, H2, H3, assoc, H4, id_left, id_right.
Qed.

Lemma isMonic_e₁ I : isMonic (e₁ I).
Proof.
intros J f g H.
set (H1 := nat_trans_ax e₁ J I f).
set (H2 := nat_trans_ax p_F J I f).
set (H3 := nat_trans_eq_pointwise Hpe₁ I).
set (H4 := nat_trans_eq_pointwise Hpe₁ J).
cbn in *.
rewrite H1 in H.
generalize (cancel_postcomposition _ _ (p_F I) H); cbn.
now rewrite <-!assoc, H2, H3, assoc, H4, id_left, id_right.
Qed.

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

Lemma deg_face₀ (Γ : PreShv C) : nat_trans_comp (deg Γ) (face₀ Γ) = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₀ I)|].
Qed.

Lemma deg_face₁ (Γ : PreShv C) : nat_trans_comp (deg Γ) (face₁ Γ) = identity Γ.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intro I.
rewrite <- (functor_id Γ).
etrans; [eapply pathsinv0, (functor_comp Γ)|].
now etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₁ I)|].
Qed.


(* Now we define composition and fill structures *)
Let yo := yoneda C hsC.

Definition p_PreShv (I : C) : yo (I+) --> yo I := # yo (p_F I).

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

Definition m_PreShv (I : C) : yo ((I +) +) --> yo (I+).
Proof.
use mk_nat_trans.
+ intros J f.
  exact (f · m I).
+ intros J K f.
  now apply funextsec; intro x; cbn; rewrite assoc.
Defined.

Lemma isMonic_e₀_PreShv I : isMonic (e₀_PreShv I).
Proof.
intros Γ σ τ H.
apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ.
generalize (eqtohomot (nat_trans_eq_pointwise H J) ρ).
now apply isMonic_e₀.
Qed.

Lemma isMonic_e₁_PreShv I : isMonic (e₁_PreShv I).
Proof.
intros Γ σ τ H.
apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ.
generalize (eqtohomot (nat_trans_eq_pointwise H J) ρ).
now apply isMonic_e₁.
Qed.

Lemma e₀_p_PreShv I : e₀_PreShv I · p_PreShv I = identity (yo I).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
set (H := nat_trans_eq_pointwise Hpe₀ I); cbn in H.
now rewrite H, id_right.
Qed.

Lemma e₁_p_PreShv I : e₁_PreShv I · p_PreShv I = identity (yo I).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
set (H := nat_trans_eq_pointwise Hpe₁ I); cbn in H.
now rewrite H, id_right.
Qed.

(* TODO: define equations for m *)

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
Context (Hδ₀_pb : ∏ I, isPullback _ _ _ _ (Hδ₀ I)).
Context (Hδ₁_pb : ∏ I, isPullback _ _ _ _ (Hδ₁ I)).

(* TODO: generalize the rest so that it works in both directions *)

(* Open boxes *)
(* TODO: move up *)
Definition b {I : C} (φ : yo I --> FF) : yo (I +) --> FF :=
 (p_PreShv I · φ) ∨ (δ₀ I).

Definition box (I : C) (φ : yo I --> FF) : PreShv C :=
  yo (I+), b φ.

Definition subst_restriction {Γ Δ : PreShv C} (σ : Δ --> Γ) (φ : Γ --> FF) :
  Δ,(σ · φ) --> Γ,φ.
Proof.
use mk_nat_trans.
+ intros I u.
  apply (pr1 σ I (pr1 u),,pr2 u).
+ abstract (intros I J f; apply funextsec; intro ρ;
  apply subtypeEquality; [intros x; apply setproperty|]; simpl;
  apply (eqtohomot (nat_trans_ax σ I J f) (pr1 ρ))).
Defined.

Definition u_subst {I : C} (φ : yo I --> FF) : yo I,φ --> box I φ.
Proof.
assert (σ1 : yo(I),φ --> yo(I), (e₁_PreShv I · (p_PreShv I · φ))).
{ use mk_nat_trans.
  + intros J ρ.
    exists (pr1 ρ).
    abstract (rewrite <- (pr2 ρ); cbn; unfold yoneda_morphisms_data;
    apply maponpaths; rewrite <-assoc;
    etrans; [apply maponpaths, (nat_trans_eq_pointwise Hpe₁ I)|];
    apply id_right).
  + abstract (intros J K f; apply funextsec; intro ρ;
    now apply subtypeEquality; [intro x; apply setproperty|]).
  (* This is a direction definition of this substitution, but reasoning about it is a nightmare: *)
  (* rewrite assoc, e₁_p_PreShv, id_left. *)
  (* apply identity. *)
}
set (σ2 := subst_restriction (e₁_PreShv I) (p_PreShv I · φ)).
exact (σ1 · σ2 · join_subst _ _).
Defined.

Definition box_subst_prf {I J : C} (f : J --> I) (φ : yo I --> FF) (K : C)
  (ρ' : pr1 (box J (# yo f · φ)) K : hSet) :
  pr1 (# yo (# F f) · (p_PreShv I · φ ∨ δ₀ I)) K (pr1 ρ') = FF1.
Proof.
rewrite comp_join.
  assert (h1 : # yo (# F f) · (p_PreShv I · φ) = p_PreShv J · (# yo f · φ)).
  { rewrite !assoc.
    apply cancel_postcomposition, (nat_trans_eq has_homsets_HSET); intros L.
    apply funextsec; intro ρ''; cbn; unfold yoneda_morphisms_data.
    rewrite <-!assoc; apply maponpaths, (nat_trans_ax p_F). }
  rewrite h1.
  assert (h2 : # yo (# F f) · δ₀ I = δ₀ J).
  { admit. } (* I think this follows from uniqueness *)
  rewrite h2.
  apply (pr2 ρ').
Admitted.

Definition box_subst {I J : C} (f : J --> I) (φ : yo I --> FF) :
  box J (# yo f · φ) --> box I φ.
Proof.
set (ψ := (p_PreShv I · φ ∨ δ₀ I) : yo (I+) --> FF).
use (_ · subst_restriction (# yo (# F f)) ψ).
use mk_nat_trans.
- intros K ρ'.
  exists (pr1 ρ').
  apply box_subst_prf.
- intros K L g.
  apply funextsec; intro ρ''.
  apply subtypeEquality; trivial; intros x; apply setproperty.
Defined.

(* Fibration approach *)
Section try3.

Definition fill_op {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v) : UU := yo (I+) --> X.

(* fill_op makes both triangles commute *)
Definition fill_op_comm {X Y α I φ} {u : box I φ --> X} {v : yo (I+) --> Y}
  {H : u · α = ι · v} (fill : fill_op H) : UU :=
    (u = ι · fill) × (fill · α = v).

Local Notation "a --> b" := (precategory_morphisms a b).

Lemma fill_op_uniform_prf {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v)
  {J} (f : J --> I)  : box_subst f φ · u · α = ι · (# yo (# F f) · v).
Proof.
rewrite <- assoc, H.
apply (nat_trans_eq has_homsets_HSET); intros K.
now apply funextsec.
Qed.

Definition fill_op_uniform {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v)
  (fill : ∏ {X Y} {α : X --> Y} I φ (u : box I φ --> X) v (H : u · α = ι · v), fill_op H)
  {J} (f : J --> I) : UU :=
    # yo (# F f) · fill I φ u v H =
    fill J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v) (fill_op_uniform_prf H f).


Definition comp_op {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v) : UU := yo (I) --> X.

Definition comp_op_comm {X Y α I φ} {u : box I φ --> X} {v : yo (I+) --> Y}
  (H : u · α = ι · v) (comp : comp_op H) : UU :=
     (ι · comp = u_subst φ · u) × (comp · α = e₁_PreShv I · v).

Definition comp_op_uniform {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v)
  (comp : ∏ {X Y} {α : X --> Y} I φ (u : box I φ --> X) v (H : u · α = ι · v), comp_op H)
  {J} (f : J --> I) : UU :=
    # yo f · comp I φ u v H = 
    comp J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v) (fill_op_uniform_prf H f).

(* This is weird, it should take a fill_op parametrized by all arguments *)
Definition comp_op_from_fill_op {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v) (f : fill_op H) : comp_op H := 
    e₁_PreShv I · f.


Lemma comp_op_from_fill_op_comm {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v) (f : fill_op H) 
  (Hf : fill_op_comm f) : comp_op_comm _ (comp_op_from_fill_op _ f).
Proof.
unfold comp_op_from_fill_op, comp_op_comm.
rewrite (pr1 Hf), <- (pr2 Hf).
split; apply (nat_trans_eq (has_homsets_HSET)); intros J;
now apply funextsec; intro ρ'.
Qed.

Lemma comp_op_from_fill_op_uniform {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v)
  (fill : ∏ (X Y : PreShv C) {α : X --> Y} {I : C} {φ : yo I --> FF} (u : box I φ --> X)
            (v : yo (I+) --> Y) (H : u · α = ι · v), fill_op H)
  {J} (f : J --> I) (Hf : fill_op_uniform H fill f) : 
    comp_op_uniform H (λ (X Y : PreShv C) (α : X --> Y) 
                         (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y)
                         (H : u · α = ι · v), comp_op_from_fill_op H (fill X Y u v H)) f.
Proof.
unfold comp_op_from_fill_op, comp_op_uniform.
unfold fill_op_uniform in Hf.
rewrite <-Hf.
apply (nat_trans_eq (has_homsets_HSET)); intros K.
apply funextsec; intro ρ'; cbn.
apply maponpaths; unfold yoneda_morphisms_data.
rewrite <- !assoc.
now apply maponpaths, (nat_trans_ax e₁).
Qed.

Definition box_subst' {I J : C} (f : yo J --> yo I) (φ : yo I --> FF) :
  box J (f · φ) --> box I φ.
Admitted.

Definition fill_op_from_comp_op
  (comp : ∏ {X Y} {α : X --> Y} I φ (u : box I φ --> X) v (H : u · α = ι · v), comp_op H)
  {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v) : fill_op H.
Proof.
unfold comp_op in *.
unfold fill_op in *.
assert (Hbb : b (b φ) = m_PreShv I · b φ).
admit.
assert (b' : box (I +) (b φ) --> X).
unfold box.
rewrite Hbb.
admit.
Check (box_subst (m I)).

Check box_subst.
apply (@comp X Y α (I +) (b φ) b' (m_PreShv I · v)).
Admitted.

End try3.

(* Attempt to transport along substitutions instead, didn't make things better *)
Section try2.

(* Maybe we can define a version of subst_term that takes 
   
σ1 : Δ --> Γ
a : Δ ⊢ A⦃σ1⦄
σ2 : Θ --> Δ

and gives

a⦃σ2⦄ : Θ ⊢ A⦃σ2 · σ1⦄

and always start with a : Γ ⊢ A⦃1⦄

This way all of the transports will be on λ x, Γ ⊢ A⦃x⦄ instead

*)
Definition subst_term' {Γ Δ Θ : PreShv C} {σ1 : Δ --> Γ} (σ2 : Θ --> Δ)
  {A : Γ ⊢} (a : Δ ⊢ A⦃σ1⦄) : Θ ⊢ A⦃σ2 · σ1⦄ :=
 transportf (λ x, Θ ⊢ x) (!subst_type_comp hsC σ2 σ1 A) (subst_term hsC σ2 a).

(* Composition operation *)
Definition comp_op2 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄) : UU :=
    yo I ⊢ A⦃e₁_PreShv I · ρ⦄.

Definition comp_op_face {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ι · ρ⦄}
  (c : comp_op2 ρ φ u) : UU.
Proof.
set (x1 := subst_term' (@ι _ φ) c).
set (x2 := subst_term' (u_subst φ) u).
assert (eq : u_subst φ · (ι · ρ) = ι · (e₁_PreShv I · ρ)).
{ now apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec. }
(* Maybe we can split the equality? *)
(* use total2. *)
(* apply (pr1 x1 = pr1 x2). *)
(* intros H. *)
(* Check (pr2 (transportf (λ x, yo I,φ ⊢ A⦃x⦄) eq x2)). *)
(* Check (pr2 x1 = pr2 (transportf (λ x, yo I,φ ⊢ A⦃x⦄) eq x2)). *)
apply (x1 = transportf (λ x, yo I,φ ⊢ A⦃x⦄) eq x2).
Defined.

Definition comp_struct {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (c : ∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), comp_op2 ρ φ u),
  (∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄),
     comp_op_face (c _ ρ φ u)).
  (* × *)
  (* (∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) J (f : J --> I), *)
  (*    comp_op_uniform ρ φ u c J f). *)


(* Filling operation *)
Definition fill_op2 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄) : UU :=
    yo (I+) ⊢ A⦃ρ⦄.

Definition fill_op_face {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ι · ρ⦄} (f : fill_op2 ρ φ u) : UU :=
    subst_term' (@ι _ (p_PreShv I · φ ∨ δ₀ I)) f = u.

Definition fill_struct {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (f : ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), fill_op2 ρ φ u),
  ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄),
     fill_op_face (f _ ρ φ u).


Definition comp_op_from_fill_op2 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄)
  (f : fill_op2 ρ φ u) : comp_op2 ρ φ u := subst_term' (e₁_PreShv I) f.

Lemma transportf_subst_TypeIn (Γ Δ : PreShv C) (σ1 σ2 : Δ --> Γ) (eq : σ1 = σ2)
  (A : Γ ⊢) (I : C) (ρ : pr1 (pr1 Δ I)) (x : pr1 (pr1 (A⦃σ1⦄) (make_ob I ρ))) : 
  transportf (λ x, pr1 (pr1 ((pr1 (A⦃x⦄))) (make_ob I ρ))) eq x =
  transportf (λ x, pr1 (pr1 A (make_ob I x))) (eqtohomot (eqtohomot (base_paths _ _ eq) I) ρ) x.
Proof.
now induction eq.
Qed.

(* Lemma transportf_TypeIn {Γ : PreShv C} (I : C) (ρ : pr1 (pr1 Γ I)) (A B : Γ ⊢) (e : A = B) *)
(*   (x : pr1 ((pr1 A) (make_ob I ρ))) : *)
(*   transportf (λ x0 : Γ ⊢, pr1 ((pr1 x0) (make_ob I ρ))) e x = *)
(*   transportf (λ x0 : hSet, pr1 x0) (eqtohomot (base_paths _ _ (base_paths _ _ e)) (make_ob I ρ)) x. *)

Require Import TypeTheory.Auxiliary.Auxiliary.

Definition comp_struct_from_fill_struct {Γ : PreShv C} {A : Γ ⊢} :
  fill_struct A → comp_struct A.
Proof.
intros [f1 f2].
mkpair.
- intros I ρ φ u.
  apply (comp_op_from_fill_op2 ρ φ u (f1 I ρ φ u)).
- intros I ρ φ u.
unfold comp_op_face, comp_op_from_fill_op.
apply pathsinv0, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro J; apply funextsec; intro ρ'.
rewrite !transportf_forall.
etrans.
use transportf_subst_TypeIn.
unfold nat_trans_eq.
rewrite base_total2_paths.
rewrite toforallpaths_funextsec.
rewrite toforallpaths_funextsec.
rewrite idpath_transportf.
cbn.
admit.
Admitted.

End try2.

(* Try 1: Not very good as uniformity gets very complicated *)
Section try1.

(* Composition operation *)
(* Note that the substitutions are not combined, this way we avoid rewriting
   with subst_type_comp later on *)
Definition comp_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) : UU :=
    yo I ⊢ A⦃ρ⦄⦃e₁_PreShv I⦄.

Definition u_subst_eq {Γ : PreShv C} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) : u_subst φ · ι · ρ = ι · e₁_PreShv I · ρ.
Proof.
apply (nat_trans_eq (has_homsets_HSET)); intros J.
now apply funextsec; intro ρ'.
Qed.

(* Arguments functor_on_morphisms : simpl never. *)

Lemma eq {Γ : PreShv C} {A : Γ ⊢} {I : C} {ρ : yo (I+) --> Γ} {φ : yo I --> FF} :
  ((A⦃ρ⦄)⦃ι⦄)⦃u_subst φ⦄ = ((A⦃ρ⦄)⦃e₁_PreShv I⦄)⦃ι⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- abstract (intros a b f;
  etrans; [use idpath_transportf|]; etrans; [use idpath_transportf|]; simpl;
  apply maponpaths;
  now apply subtypeEquality; [intros x; apply setproperty|]).
(* use (@idpath_transportf _ (λ x, pr1 (pr1 (((A⦃ρ⦄)⦃e₁_PreShv I⦄)⦃ι⦄)) a --> x)(pr1 A (get_ob b,, pr1 ρ (get_ob b) (pr1 (get_el b) · e₁ I)))). *)
(* Check  . *)
(*   (λ x : HSET, HSET ⟦ pr1 (pr1 (((A⦃ρ⦄)⦃e₁_PreShv I⦄)⦃ι⦄))a,x⟧)). *)
(*             rewrite !idpath_transportf; apply maponpaths; *)
(*             now apply subtypeEquality; [intros x; apply setproperty|]). *)
Defined.

Lemma base_paths_eq {Γ : PreShv C} {A : Γ ⊢} {I : C} {ρ : yo (I+) --> Γ} {φ : yo I --> FF} :
  base_paths _ _ (base_paths _ _ (@eq Γ A I ρ φ)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold eq, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

Definition comp_op_face1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ρ⦄⦃ι⦄}
  (c : comp_op1 ρ φ u) : UU :=
    subst_term hsC (@ι _ φ) c =
    transportf (λ x, yo I,φ ⊢ x) eq (subst_term hsC (u_subst φ) u).

Lemma eq1_prf {Γ : PreShv C} {A : Γ ⊢} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) J (f : J --> I) : ∏ (C1 C2 : (∫ (box J (# yo f · φ)))^op)
  (f0 : C1 --> C2),
  transportf
    (λ x, pr1 (pr1 ((A⦃# yo (# F f) · ρ⦄)⦃ι⦄)) C1 --> x)
    (idpath (pr1 (pr1 ((A⦃# yo (# F f) · ρ⦄)⦃ι⦄)) C2))
    (transportf
       (λ x, x --> pr1 (pr1 (((A⦃ρ⦄)⦃ι⦄)⦃box_subst f φ⦄)) C2)
       (idpath (pr1 (pr1 ((A⦃# yo (# F f) · ρ⦄)⦃ι⦄)) C1))
       (pr2 (pr1 (((A⦃ρ⦄)⦃ι⦄)⦃box_subst f φ⦄)) C1 C2 f0)) =
  pr2 (pr1 ((A⦃# yo (# F f) · ρ⦄)⦃ι⦄)) C1 C2 f0.
Proof.
intros a b g;
  etrans; [use idpath_transportf|]; etrans; [use idpath_transportf|]; simpl;
  apply maponpaths;
  now apply subtypeEquality; [intros x; apply setproperty|].
Admitted. (* How to make this Qed fast? *)

Lemma eq1 {Γ : PreShv C} {A : Γ ⊢} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) J (f : J --> I) :
  ((A⦃ρ⦄)⦃ι⦄)⦃box_subst f φ⦄ = (A⦃# yo (# F f) · ρ⦄)⦃ι⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- use eq1_prf.
Defined.

Lemma base_paths_eq1 {Γ : PreShv C} {A : Γ ⊢} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) J (f : J --> I) :
  base_paths _ _ (base_paths _ _ (@eq1 Γ A I ρ φ J f)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold eq1, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

Lemma eq2 {Γ : PreShv C} {A : Γ ⊢} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) J (f : J --> I) :
  (A⦃# yo (# F f) · ρ⦄)⦃e₁_PreShv J⦄ = ((A⦃ρ⦄)⦃e₁_PreShv I⦄)⦃# yo f⦄.
Proof.
rewrite subst_type_comp.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c.
cbn.
apply maponpaths.
apply pair_path_in2.
apply maponpaths.
unfold yoneda_morphisms_data.
rewrite <- !assoc.
apply maponpaths.
apply (!nat_trans_ax e₁ J I f).
- admit.
Admitted.

(* Uniformity *)
Definition comp_op_uniform1 {Γ : PreShv C} {A : Γ ⊢}
  {I : C} (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (comp : ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), comp_op1 ρ φ u) :
  ∏ (J : C) (f : J --> I), UU.
Proof.
intros J f.
set (x1 := subst_term hsC (# yo f) (comp I ρ φ u)).
set (ρ' := # yo (# F f) · ρ).
set (φ' := # yo f · φ).
set (u' := subst_term hsC (box_subst f φ) u).
set (x2 := comp J ρ' φ' (transportf (λ x, box J φ' ⊢ x) (eq1 ρ φ J f) u')).
apply (x1 = transportf (λ x, yo J ⊢ x) (eq2 ρ φ J f) x2).
Defined.

Definition comp_struct1 {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (c : ∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), comp_op1 ρ φ u),
  (∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄),
     comp_op_face1 (c _ ρ φ u)) ×
  (∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) J (f : J --> I),
     comp_op_uniform1 ρ φ u c J f).

(* Filling operation *)
Definition fill_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) : UU :=
    yo (I+) ⊢ A⦃ρ⦄.

Definition fill_op_face1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ρ⦄⦃ι⦄} (f : fill_op1 ρ φ u) : UU :=
    subst_term hsC (@ι _ (p_PreShv I · φ ∨ δ₀ I)) f = u.

Definition fill_struct1 {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (f : ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄), fill_op1 ρ φ u),
  ∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄),
     fill_op_face1 (f _ ρ φ u).

Definition comp_op_from_fill_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (f : fill_op1 ρ φ u) : comp_op1 ρ φ u := subst_term hsC (e₁_PreShv I) f.

Definition comp_struct_from_fill_struct1 {Γ : PreShv C} {A : Γ ⊢} :
  fill_struct1 A → comp_struct1 A.
Proof.
intros [f1 f2].
mkpair.
- intros I ρ φ u.
  apply (comp_op_from_fill_op1 ρ φ u (f1 I ρ φ u)).
- split.
  + intros I ρ φ u.
unfold comp_op_face, comp_op_from_fill_op.
apply pathsinv0, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro J; apply funextsec; intro ρ'.
rewrite !transportf_forall, transportf_TypeIn.
rewrite (@base_paths_eq Γ A I ρ φ).
rewrite toforallpaths_funextsec, idpath_transportf.
generalize (f2 I ρ φ u).
Search subst_term.
unfold fill_op_face.
intros H.
cbn.
generalize (eqtohomot (eqtohomot (maponpaths pr1 H) J) ( (pr1 ρ';; e₁ I,,
     maponpaths _
       (pathsdirprod (u_subst_subproof I φ J ρ')
          (idpath _)) @
     eqtohomot
       (nat_trans_eq_pointwise
          (join_mor_top_mor BinProducts_PreShv 1 FF_lattice) J)
       (pr1 (δ₀ I) J (pr1 ρ';; e₁ I))))).
cbn.
apply pathsinv0.
+ intros.
admit.
Admitted.

Definition fill_op_from_comp_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (c : comp_op1 ρ φ u) : fill_op1 ρ φ u.
Proof.
unfold comp_op in c.
unfold fill_op.
Admitted.

End try1.

End cubical.