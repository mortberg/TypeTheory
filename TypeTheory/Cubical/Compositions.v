Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
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
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.LatticeObject.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.yoneda.

Require Import TypeTheory.Instances.Presheaves.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).
Arguments nat_trans_comp {_ _ _ _ _} _ _.
Arguments isPullback {_ _ _ _ _ _ _ _ _} _.

Section cubical.

Context {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C).

(* Setup notations *)
Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).
Local Notation "c '⊗' d" :=
  (BinProductObject _ (@BinProducts_PreShv C c d)) (at level 30) : cat.
Local Notation "f '××' g" :=
  (BinProductOfArrows _ (BinProducts_PreShv _ _) (BinProducts_PreShv _ _) f g)
  (at level 90) : cat.
Local Notation "1" := Terminal_PreShv.
Local Notation "'Id'" := (functor_identity _).

Let p {Γ : PreShv C} {A : Γ ⊢} := @ctx_proj _ _ A.

(* Why is the formatting not working for this notation: *)
Local Notation "C ⟦ a , b ⟧" :=
  (precategory_morphisms (C:=C) a b) (format "C ⟦ a , b ⟧", at level 50) : cat.

Definition binprod_delta x : x --> x ⊗ x := BinProductArrow _ _ (identity x) (identity x).
Local Notation "'δ'" := (binprod_delta _).

Let Ω : bounded_latticeob BinProducts_PreShv 1 Ω_PreShv :=
  @Ω_PreShv_bounded_lattice C.

(* Assume that we have a sublattice of Ω *)
Context (FF : PreShv C) (i : FF --> Ω_PreShv) (Hi : isMonic i).
Context (meet_FF : FF ⊗ FF --> FF) (join_FF : FF ⊗ FF --> FF).
Context (bot_FF : 1 --> FF) (top_FF : 1 --> FF).
Context (Hmeet_FF : meet_FF · i = (i ×× i) · meet_mor Ω).
Context (Hjoin_FF : join_FF · i = (i ×× i) · join_mor Ω).
Context (Hbot_FF : bot_FF · i = bot_mor Ω).
Context (Htop_FF : top_FF · i = top_mor Ω).

(* Maybe package this up? *)
Definition FF_lattice : bounded_latticeob BinProducts_PreShv 1 FF :=
  sub_bounded_latticeob BinProducts_PreShv Terminal_PreShv Hi Ω
                        Hmeet_FF Hjoin_FF Hbot_FF Htop_FF.

(* Extract the top and bottom elements of the lattice (as sets)*)
Definition FF1 {I} : pr1 FF I : hSet := pr1 top_FF I tt.
Definition FF0 {I} : pr1 FF I : hSet := pr1 bot_FF I tt.

(* The map that constantly returns FF1 *)
Definition true : 1 --> FF.
Proof.
use mk_nat_trans.
+ intros I _.
  exact (@FF1 I).
+ intros I J f; cbn.
  apply funextsec; intros _.
  apply (eqtohomot (nat_trans_ax top_FF I J f) tt).
Defined.

(* The meet and join operations *)
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

(* Some pointwise equations for the face lattice. TODO: better notations *)
Lemma meet_FF1 (I : C) (φ : pr1 FF I : hSet) : pr1 meet_FF I (FF1,,φ) = φ.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (islunit_meet_mor_top_mor _ _ FF_lattice) I) φ).
Qed.

Lemma join_absorb_meet_FF (I : C) (φ ψ : pr1 FF I : hSet) :
  pr1 join_FF I (φ,,pr1 meet_FF I (φ,,ψ)) = φ.
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (join_mor_absorb_meet_mor _ FF_lattice) I) (φ,,ψ)).
Qed.

Lemma join_FF_assoc (I : C) (x y z : pr1 FF I : hSet) :
  pr1 join_FF I (pr1 join_FF I (x,,y),, z) = pr1 join_FF I (x,,pr1 join_FF I (y,,z)).
Proof.
exact (eqtohomot (nat_trans_eq_pointwise (isassoc_join_mor _ FF_lattice) I) ((x,,y),,z)).
Qed.

Lemma join_FF1 (I : C) (x : pr1 FF I : hSet) :
  pr1 join_FF I (FF1,,x) = FF1.
Proof.
now rewrite <- (meet_FF1 _ x), join_absorb_meet_FF.
Qed.

(* Context restriction: Γ, φ |- *)
Definition ctx_restrict (Γ : PreShv C) (φ : Γ --> FF) : PreShv C.
Proof.
use mk_functor.
- mkpair.
  + simpl; intros I.
    exists (∑ ρ : pr1 ((pr1 Γ) I), pr1 φ I ρ = FF1).
    abstract (apply isaset_total2; [ apply setproperty
                                   | intros ρ; apply isasetaprop, setproperty ]).
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

(* Canonical inclusion *)
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
exact (eqtohomot (nat_trans_eq_pointwise H I) ρ).
Qed.

Definition join_subst {Γ : PreShv C} (φ ψ : Γ --> FF) : Γ,φ --> Γ,(φ ∨ ψ).
Proof.
use mk_nat_trans.
- intros I ρ.
  exists (pr1 ρ).
  abstract (cbn; etrans; [apply maponpaths, (pathsdirprod (pr2 ρ) (idpath _))|];
            apply join_FF1).
- intros I J f.
  apply funextsec; intro ρ.
  now apply subtypeEquality; [intros x; apply setproperty|].
Defined.

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


(*************************)
(* Cylinder functor on C *)
(*************************)

Context (F : C ⟶ C).

Notation "I +" := (F I) (at level 20).

(* We assume a cylinder functor F *)
Context (p_F : F ⟹ Id) (e₀ e₁ : Id ⟹ F).
Context (Hpe₀ : nat_trans_comp e₀ p_F = nat_trans_id Id).
Context (Hpe₁ : nat_trans_comp e₁ p_F = nat_trans_id Id).

(* We also assume a conjunction map m : F^2 -> F satisfying: *)
(* m e0 = e0 p *)
(* m (e0+) = e0 p *)
(* m e1 = 1 *)
(* m (e1+) = 1 *)
(* p m = p p *)

Context (m : F ∙ F ⟹ F).
Context (He₀m : nat_trans_comp (post_whisker e₀ F) m = nat_trans_comp p_F e₀).
Context (He₀m' : nat_trans_comp (pre_whisker F e₀) m = nat_trans_comp p_F e₀).
Context (He₁m : nat_trans_comp (post_whisker e₁ F) m = nat_trans_id F).
Context (He₁m' : nat_trans_comp (pre_whisker F e₁) m = nat_trans_id F).
Context (Hmp : nat_trans_comp m p_F = nat_trans_comp (pre_whisker F p_F) p_F).

Goal ∏ (I : C), UU.
intros.
generalize (nat_trans_eq_pointwise He₁m I).
generalize (nat_trans_eq_pointwise He₁m' I).
generalize (nat_trans_eq_pointwise He₀m I).
generalize (nat_trans_eq_pointwise He₀m' I).
generalize (nat_trans_eq_pointwise Hmp I).
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

(* We can lift the above operations to presheaves using yoneda *)
Let yo := yoneda_functor_data C hsC.

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

Lemma e₁_m_PreShv I : e₁_PreShv (I +) · m_PreShv I = identity (yo (I+)).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro J.
apply funextsec; intro ρ; cbn; unfold yoneda_morphisms_data.
rewrite <-assoc.
etrans; [apply maponpaths, (nat_trans_eq_pointwise He₁m' I)|].
now apply id_right.
Qed.

Lemma m_p_PreShv I : m_PreShv I · p_PreShv I = p_PreShv (I+) · p_PreShv I.
Proof.
apply (nat_trans_eq has_homsets_HSET); intros J.
cbn; unfold yoneda_morphisms_data.
apply funextsec; intro ρ; cbn.
rewrite <-!assoc; apply maponpaths.
apply (nat_trans_eq_pointwise Hmp I).
Qed.

(* TODO: define the rest of the equations for m *)


(**************)
(* Open boxes *)
(**************)

(* Introduce δ₀ which classifies e₀_PreShv *)
(* Is this correctly expressed? *)
Context (δ₀ : ∏ I, yo (I +) --> FF).
Context (Hδ₀ : ∏ I, e₀_PreShv I · δ₀ I = TerminalArrow _ · true).

Context (Hδ₀_pb : ∏ I, isPullback (Hδ₀ I)).

(* Maybe uniqueness should be defined like this: *)
Context (Hδ₀_unique : ∏ (I : C) (d0 : yo (I+) --> FF)
                        (Hd0 : e₀_PreShv I · d0 = TerminalArrow _ · true),
                        isPullback Hd0 → d0 = δ₀ I).


(* TODO: generalize the rest so that it works in both directions *)

(* This axiom follows if we work with II. I think it is a bit stronger than
   necessary. How can we weaken it? Maybe using something along the lines of:
     box(phi) m  <=  box(box(phi))

This is like: 
  (φ ∧ ψ) = 0  iff   (φ = 0) ∨ (ψ = 0) 
*)
Context (Hmδ₀ : ∏ I, m_PreShv I · δ₀ I = (p_PreShv (I +) · δ₀ I ∨ δ₀ (I +))).

(* The box formula *)
Definition b {I : C} (φ : yo I --> FF) : yo (I +) --> FF :=
  (p_PreShv I · φ) ∨ (δ₀ I).

(* A box is a representable cube restricted by the box formula *)
Definition box (I : C) (φ : yo I --> FF) : PreShv C :=
  yo (I+), b φ.

(* This substitution is used for the box u below, hence the name *)
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
  (* This is a direct definition of this substitution, 
     but reasoning about it is a nightmare: *)
  (* rewrite assoc, e₁_p_PreShv, id_left. *)
  (* apply identity. *)
}
set (σ2 := subst_restriction (e₁_PreShv I) (p_PreShv I · φ)).
exact (σ1 · σ2 · join_subst _ _).
Defined.

Definition u_subst_eq {Γ : PreShv C} {I : C} (ρ : yo (I+) --> Γ)
  (φ : yo I --> FF) : u_subst φ · ι · ρ = ι · e₁_PreShv I · ρ.
Proof.
now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec.
Qed.

Lemma plus_δ₀_prf (I J : C) (f : J --> I) :
  e₀_PreShv J · (# yo (# F f) · δ₀ I) = TerminalArrow (yo J) · true.
Proof.
rewrite assoc.
assert (H : e₀_PreShv J · # yo (# F f) = # yo f · e₀_PreShv I).
{ apply (nat_trans_eq has_homsets_HSET); intros K; apply funextsec; intro ρ.
  cbn; unfold yoneda_morphisms_data.
  rewrite <-!assoc.
  apply maponpaths, (!nat_trans_ax e₀ J I f).
}
rewrite H, <- assoc, Hδ₀.
now apply (nat_trans_eq has_homsets_HSET); intros K; apply funextsec.
Qed.

(* Why is this true? *)
Lemma plus_δ₀ I J (f : J --> I) : # yo (# F f) · δ₀ I = δ₀ J.
Proof.
use Hδ₀_unique.
- apply plus_δ₀_prf.
- admit.
Admitted.

Definition box_subst_prf {I J : C} (f : J --> I) (φ : yo I --> FF) (K : C)
  (ρ' : pr1 (box J (# yo f · φ)) K : hSet) :
  pr1 (# yo (# F f) · (p_PreShv I · φ ∨ δ₀ I)) K (pr1 ρ') = FF1.
Proof.
rewrite comp_join.
assert (h1 : # yo (# F f) · (p_PreShv I · φ) = p_PreShv J · (# yo f · φ)).
{ rewrite !assoc.
  apply cancel_postcomposition, (nat_trans_eq has_homsets_HSET); intros L.
  apply funextsec; intro ρ''; cbn; unfold yoneda_morphisms_data.
  rewrite <-!assoc; apply maponpaths, (nat_trans_ax p_F).
}
rewrite plus_δ₀, <- (pr2 ρ').
now unfold b; rewrite <- h1.
Qed.

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

Lemma b_yo {I J} (f : J --> I) (φ : yo I --> FF) :
  b (# yo f · φ) = # yo (# F f) · b φ.
Proof.
apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intro ρ; cbn.
apply maponpaths; simpl.
unfold yoneda_objects_ob, yoneda_morphisms_data, prodtofuntoprod; simpl.
apply pathsdirprod.
- apply maponpaths.
  rewrite <-!assoc.
  apply maponpaths, (!nat_trans_ax p_F J I f).
- apply (!eqtohomot (nat_trans_eq_pointwise (plus_δ₀ I J f) K) ρ).
Qed.

(* Multiplication rule for the box formula *)
Lemma m_b (I : C) (φ : yo I --> FF) : m_PreShv I · b φ = b (b φ).
Proof.
apply pathsinv0; unfold b.
rewrite !comp_join, assoc, <- m_p_PreShv, <- assoc, Hmδ₀.
apply (nat_trans_eq has_homsets_HSET); intros J.
cbn; unfold yoneda_morphisms_data, prodtofuntoprod.
apply funextsec; intro ρ; cbn.
now apply (join_FF_assoc J _ _ _).
Qed.

Lemma box_b_subst {X Y : PreShv C} (α : X --> Y) (I : C) (φ : yo I --> FF)
  (u : box I φ --> X) : box (I +) (b φ) --> X.
Proof.
use (_ · subst_restriction (m_PreShv I) (b φ) · u).
(* Make a special lemma for this? *)
use mk_nat_trans.
- intros J XX.
  exists (pr1 XX).
  abstract (now rewrite m_b, (pr2 XX)).
- intros J K f.
  apply funextsec; intro ρ.
  apply subtypeEquality; trivial; intros x; apply setproperty.
Defined.



(***********************************)
(* Composition and fill structures *)
(***********************************)

(* Fibration approach *)
(* These definitions of fill and comp are a lot easier to 
   work with than the ones similar to the paper *)
Section fibrations.

Local Notation "a --> b" := (precategory_morphisms a b).

Lemma fibfill_uniform_prf {X Y : PreShv C} {α : X --> Y} {I : C} {φ : yo I --> FF}
  {u : box I φ --> X} {v : yo (I+) --> Y} (H : u · α = ι · v)
  {J} (f : J --> I)  : box_subst f φ · u · α = ι · (# yo (# F f) · v).
Proof.
rewrite <- assoc, H.
apply (nat_trans_eq has_homsets_HSET); intros K.
now apply funextsec.
Qed.

(* Fibfill structure - computes diagonal map for

                  u
     box(I,phi) ------> X
         |              |
       i |              | α
         |              |
         V              V
      yo(I+) ---------> Y
                  v
 *)
Definition fibfill_struct {X Y : PreShv C} (α : X --> Y) : UU.
Proof.
use total2.
- apply (∏ (I : C) (φ : yo I --> FF) (u : box I φ --> X)
           (v : yo (I+) --> Y) (H : u · α = ι · v), yo (I+) --> X).
- intros fibfill.
  use (∏ I (φ : yo I --> FF) (u : box I φ --> X)
         (v : yo (I+) --> Y) (H : u · α = ι · v), (_ × _) × _).
  + (* upper triangle *)
    apply (u = ι · fibfill _ _ _ _ H).
  + (* lower triangle *)
    apply (fibfill _ _ _ _ H · α = v).
  + (* uniformity *)
    apply (∏ J (f : J --> I),
           # yo (# F f) · fibfill I φ u v H =
           fibfill J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v)
                   (fibfill_uniform_prf H f)).
Defined.


(* A fibcomp struct - diagonal map for the extended diagram *)
Definition fibcomp_struct {X Y : PreShv C} (α : X --> Y) : UU.
Proof.
use total2.
- apply (∏ {I} {φ : yo I --> FF} {u : box I φ --> X}
           {v : yo (I+) --> Y} (H : u · α = ι · v), yo I --> X).
- intros fibcomp.
  use (∏ I (φ : yo I --> FF) (u : box I φ --> X)
         (v : yo (I+) --> Y) (H : u · α = ι · v), (_ × _) × _).
  + (* upper triangle *)
    apply (ι · fibcomp _ _ _ _ H = u_subst φ · u).
  + (* lower triangle *)
    apply (fibcomp _ _ _ _ H · α = e₁_PreShv I · v).
  + (* uniformity *)
    apply (∏ J (f : J --> I),
           # yo f · fibcomp I φ u v H =
           fibcomp J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v)
                     (fibfill_uniform_prf H f)).
Defined.

Lemma fibcomp_eq {X Y : PreShv C} (α : X --> Y)
  (fibcomp : ∏ (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y),
             u · α = ι · v → yo I --> X)
  (I : C) (φ : yo I --> FF) (u1 u2 : box I φ --> X) (v1 v2 : yo (I +) --> Y)
  (H1 : u1 · α = ι · v1) (H2 : u2 · α = ι · v2)
  (Hu12 : u1 = u2) (Hv12 : v1 = v2) :
  fibcomp I φ u1 v1 H1 = fibcomp I φ u2 v2 H2.
Proof.
induction Hu12.
induction Hv12.
apply maponpaths, (isaset_nat_trans has_homsets_HSET).
Qed.


(** The easy direction: fibfill implies fibcomp *)

(* First define the operation *)
Definition fibfill_to_fibcomp_op {X Y : PreShv C} {α : X --> Y} (Fα : fibfill_struct α) :
  ∏ (I : C) (φ : yo I --> FF) (u : box I φ --> X) 
    (v : yo (I +) --> Y), u · α = ι · v → yo I --> X.
Proof.
intros I φ u v H.
apply (e₁_PreShv I · pr1 Fα I φ u v H).
Defined.

(* Upper triangle commutes *)
Lemma fibfill_to_fibcomp_comm1 {X Y : PreShv C} {α : X --> Y} (Fα : fibfill_struct α)
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) :
  ι · fibfill_to_fibcomp_op Fα I φ u v H = u_subst φ · u.
Proof.
unfold fibfill_to_fibcomp_op; induction Fα as [fibfill Hfibfill]; simpl.
destruct (Hfibfill I φ u v H) as [[Hfibfill1 _] _].
apply pathsinv0; etrans; [apply maponpaths, Hfibfill1|].
now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec.
Qed.

(* Lower triangle commutes *)
Lemma fibfill_to_fibcomp_comm2 {X Y : PreShv C} {α : X --> Y} (Fα : fibfill_struct α)
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) :
  fibfill_to_fibcomp_op Fα I φ u v H · α = e₁_PreShv I · v.
Proof.
unfold fibfill_to_fibcomp_op; induction Fα as [fibfill Hfibfill]; simpl.
destruct (Hfibfill I φ u v H) as [[_ Hfibfill2] _].
etrans; [apply (! (assoc (e₁_PreShv I) _ _))|].
now rewrite Hfibfill2.
(* etrans; [|apply maponpaths, Hfibfill2]. *)
(* now apply (nat_trans_eq (has_homsets_HSET)); intros J; apply funextsec. *)
Qed.

(* Uniformity *)
Lemma fibfill_to_fibcomp_uniform {X Y : PreShv C} {α : X --> Y} (Fα : fibfill_struct α)
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) :
  ∏ (J : C) (f : J --> I), # yo f · fibfill_to_fibcomp_op Fα I φ u v H =
  fibfill_to_fibcomp_op Fα J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v) (fibfill_uniform_prf H f).
Proof.
intros J f; unfold fibfill_to_fibcomp_op; induction Fα as [fibfill Hfibfill].
destruct (Hfibfill I φ u v H) as [_ fibfill_uni].
rewrite <- fibfill_uni, !assoc.
apply cancel_postcomposition, (nat_trans_eq (has_homsets_HSET)); intros K.
apply funextsec; intro ρ'; cbn; unfold yoneda_morphisms_data.
now rewrite <-!assoc; apply maponpaths, (nat_trans_ax e₁).
Qed.

Lemma fibfill_to_fibcomp {X Y : PreShv C} (α : X --> Y) (Fα : fibfill_struct α) :
  fibcomp_struct α.
Proof.
exists (fibfill_to_fibcomp_op Fα); intros I φ u v H.
split; [split|].
+ apply fibfill_to_fibcomp_comm1.
+ apply fibfill_to_fibcomp_comm2.
+ apply fibfill_to_fibcomp_uniform.
Defined.


(* Now the harder direction *)

(* First define the operation *)
Definition fibcomp_to_fibfill_op {X Y : PreShv C} {α : X --> Y} (Cα : fibcomp_struct α) :
  ∏ (I : C) (φ : yo I --> FF) (u : box I φ --> X)
    (v : yo (I +) --> Y), u · α = ι · v → yo (I +) --> X.
Proof.
intros I φ u v H.
apply (pr1 Cα (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)).
abstract (apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec; intro ρ;
          apply (eqtohomot (nat_trans_eq_pointwise H J))).
Defined.

(* Upper triangle commutes *)
Lemma fibcomp_to_fibfill_comm1 {X Y : PreShv C} {α : X --> Y} (Cα : fibcomp_struct α) 
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) :
  u = ι · fibcomp_to_fibfill_op Cα I φ u v H.
Proof.
unfold fibcomp_to_fibfill_op; induction Cα as [comp Hcomp]; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (fibcomp_to_fibfill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [|apply (!Hcomp1)].
apply (nat_trans_eq has_homsets_HSET (pr1 (box I φ)) (pr1 X)); intros J.
apply funextsec; intro ρ; cbn.
apply maponpaths, subtypeEquality; [ intros x; apply setproperty|]; cbn.
rewrite <-assoc; apply pathsinv0.
etrans; [ apply maponpaths, (nat_trans_eq_pointwise He₁m' I)|].
now apply id_right.
Qed. (* This is slow *)

(* Lower triangle commutes *)
Lemma fibcomp_to_fibfill_comm2 {X Y : PreShv C} {α : X --> Y} (Cα : fibcomp_struct α)
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) :
  fibcomp_to_fibfill_op Cα I φ u v H · α = v.
Proof.
unfold fibcomp_to_fibfill_op; induction Cα as [comp Hcomp]; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (fibcomp_to_fibfill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [apply Hcomp|].
now rewrite assoc, e₁_m_PreShv, id_left.
Qed.

(* Uniformity *)

Arguments functor_on_morphisms : simpl never.

Lemma ρ_eq (I K : C) (φ ψ : yo I --> FF)
  (ρ : pr1 (pr1 (box I φ) K)) (eq : φ = ψ) :
  pr1 ρ = pr1 (pr1 (pr1 (idtoiso (maponpaths (box I) eq))) K ρ).
Proof.
now induction eq.
Qed.

Lemma box_subst_comp_box_b_subst {I J} (f : J --> I) (φ : yo I --> FF)
  {X Y : PreShv C} (α : X --> Y) (u : box I φ --> X) :
  box_subst (# F f) (b φ) · box_b_subst α I φ u =
  transportf (λ x, box (J +) x --> X) (b_yo f φ)
    (box_b_subst α J (# yo f · φ) (box_subst f φ · u)).
Proof.
pathvia (transportf (λ x, x --> X) (maponpaths (box (J+)) (b_yo f φ))
                    (box_b_subst α J (# yo f · φ) (box_subst f φ · u))).
{ apply (@transportf_transpose _ (λ x, x --> X)), pathsinv0.
  etrans; [|apply idtoiso_precompose].
  rewrite pathsinv0inv0.
  apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intros ρ.
  apply (maponpaths (pr1 u K)).
  apply subtypeEquality; [ intros x; apply setproperty|].
  (* simpl. *) (* This simpl gives an EXTREMELY slow Qed *)
  etrans; [|apply assoc].
  etrans; [|eapply pathsinv0, maponpaths, (nat_trans_ax m J I f)].
  rewrite assoc.
  apply cancel_postcomposition, cancel_postcomposition.
  apply (ρ_eq (J +) K (b (# yo f · φ)) (# yo (# F f) · b φ) ρ (b_yo f φ)). }
{ induction (b_yo f φ).
  now rewrite idpath_transportf. }
Qed.

Lemma yo_m_v {I J} (f : J --> I) (Y : PreShv C) (v : yo (I +) --> Y) :
  # yo (# F (# F f)) · (m_PreShv I · v) = m_PreShv J · (# yo (# F f) · v).
Proof.
apply (nat_trans_eq has_homsets_HSET); intro K; apply funextsec; intro ρ; cbn.
apply maponpaths; simpl; unfold yoneda_morphisms_data.
rewrite <- !assoc.
apply maponpaths, (nat_trans_ax m J I f).
Qed.

Lemma fibcomp_to_fibfill_uniform {X Y : PreShv C} {α : X --> Y} (Cα : fibcomp_struct α)
  (I : C) (φ : yo I --> FF) (u : box I φ --> X) (v : yo (I +) --> Y) (H : u · α = ι · v) : 
  ∏ (J : C) (f : J --> I),
  # yo (# F f) · fibcomp_to_fibfill_op Cα I φ u v H =
  fibcomp_to_fibfill_op Cα J (# yo f · φ) (box_subst f φ · u) (# yo (# F f) · v)
                                           (fibfill_uniform_prf H f).
Proof.
unfold fibcomp_to_fibfill_op; induction Cα as [comp Hcomp]; intros J f; simpl.
destruct (Hcomp (I +) (b φ) (box_b_subst α I φ u) (m_PreShv I · v)
                (fibcomp_to_fibfill_op_subproof X Y α I φ u v H)) as
                [[Hcomp1 Hcomp2] comp_uni].
etrans; [apply (comp_uni (J+) (# F f))|].
match goal with |-comp _ ?AA1 ?AA2 ?AA3 ?AA4 = comp _ ?BB1 ?BB2 ?BB3 ?BB4 =>
  set (A1 := AA1); set (A2 := AA2); set (A3 := AA3); set (A4 := AA4);
  set (B1 := BB1); set (B2 := BB2); set (B3 := BB3); set (B4 := BB4) end.
set (B2' := transportf (λ x, box (J +) x --> X) (b_yo f φ) B2).
assert (B4' : B2' · α = ι · A3).
{ now etrans; [eapply cancel_postcomposition, pathsinv0, box_subst_comp_box_b_subst|]. }
pathvia (comp (J+) A1 B2' A3 B4').
- apply fibcomp_eq; trivial.
  now apply box_subst_comp_box_b_subst.
- induction (b_yo f φ).
  now apply fibcomp_eq; trivial; apply yo_m_v.
Qed.

Lemma fibcomp_to_fibfill {X Y : PreShv C} (α : X --> Y) (Cα : fibcomp_struct α) :
  fibfill_struct α.
Proof.
exists (fibcomp_to_fibfill_op Cα); intros I φ u v H.
split; [split|].
- apply fibcomp_to_fibfill_comm1.
- apply fibcomp_to_fibfill_comm2.
- apply fibcomp_to_fibfill_uniform.
Defined.

End fibrations.


(*** WIP below *)

(* Composition and filling structure *)
Section fill_struct.

Local Notation "a --> b" := (precategory_morphisms a b).

(* Lemma nat_trans_eq {C' C'' : precategory_data} (hs: has_homsets C'') *)
(*   (F' F'' : functor_data C' C'')(a a' : nat_trans F' F''): *)
(*   (∏ x, a x = a' x) -> a = a'. *)
(* Proof. *)
(*   intro H. *)
(*   assert (H' : pr1 a = pr1 a'). *)
(*   { now apply funextsec. } *)
(*   apply (total2_paths_f H'), proofirrelevance, isaprop_is_nat_trans, hs. *)
(* Defined. *)


(* Define a version of subst_term that takes

σ1 : Δ --> Γ
a : Δ ⊢ A⦃σ1⦄
σ2 : Θ --> Δ

and gives

a⦃σ2⦄ : Θ ⊢ A⦃σ2 · σ1⦄

and always start with a : Γ ⊢ A⦃1⦄

This way all of the transports will be on λ x, Γ ⊢ A⦃x⦄ instead of λ x, Γ ⊢ x
*)
Definition subst_term' {Γ Δ Θ : PreShv C} {σ1 : Δ --> Γ} (σ2 : Θ --> Δ)
  {A : Γ ⊢} (a : Δ ⊢ A⦃σ1⦄) : Θ ⊢ A⦃σ2 · σ1⦄ :=
 transportb (λ x, Θ ⊢ x) (subst_type_comp hsC σ2 σ1 A) (subst_term hsC σ2 a).

Definition fill_struct {Γ : PreShv C} (A : Γ ⊢) : UU.
Proof.
use total2.
- apply (∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF)
              (u : box I φ ⊢ A⦃ι · ρ⦄), yo (I+) ⊢ A⦃ρ⦄).
- intros fill.
  use (∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), _ × _).
  + apply (subst_term' (@ι _ (b φ)) (fill I ρ φ u) = u).
  + use (∏ J (f : J --> I), _).
    apply UU. (* TODO: uniformity *)
Defined.

Lemma fill_struct_to_fib {Γ : PreShv C} (A : Γ ⊢) :
  fill_struct A → fibfill_struct (@p _ A).
Proof.
intros [fill Hfill].
transparent assert (u' : (∏ (I : C) (φ : yo I --> FF) (v : yo (I +) --> Γ) (u : box I φ --> Γ ⋆ A) (H : u · p = ι · v), box I φ ⊢ A⦃ι · v⦄)).
{ intros.
  induction H.
  use (transportb (λ x, _ ⊢ x) (subst_type_comp _ _ _ _) (subst_term hsC u (ctx_last hsC))).
}
use (tpair _ _ _).
+ intros I φ u v H.
  exact (subst_pair hsC v (fill I v φ (u' I φ v u H))).
+ cbn beta zeta.
  intros.
  split.
  split.
  *
  set (HH := pr1 (Hfill I v φ (u' I φ v u H))).
  rewrite subst_pair_subst.
  unfold subst_term' in HH.
  rewrite HH.
  unfold u'.
  clear -u.
  induction H.
  simpl.
  Search subst_pair.
  unfold transportb.
  etrans.
  Focus 2.
  apply (@subst_pair_subst C hsC _ _ _ (ctx_proj) u A (ctx_last hsC)).
  rewrite subst_pair_id.
  now rewrite id_right.
* unfold p.
  now rewrite (subst_pair_p hsC v).
* admit.
Admitted.

Lemma fib_to_fill_struct {Γ : PreShv C} (A : Γ ⊢) :
  fibfill_struct (@p _ A) → fill_struct A.
Proof.
intros [fibfill Hfibfill].
transparent assert (u' : (∏ (I : C) (ρ : yo (I +) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), box I φ --> Γ ⋆ A)).
{ intros; exact (subst_pair hsC _ u). }
use (tpair _ _ _).
- intros.

  assert (H : u' I ρ φ u · p = ι · ρ).
  { now apply subst_pair_p. }
  exact (transportf (λ x, yo (I+) ⊢ A⦃x⦄) (pr2 (pr1 (Hfibfill I φ (u' I ρ φ u) ρ H)))
        (transportb (λ x, yo (I+) ⊢ x) (subst_type_comp _ _ _ _)
                    (subst_term hsC (fibfill I φ (u' I ρ φ u) ρ H) (ctx_last hsC)))).
- cbn beta zeta.
  intros.
    assert (H : u' I ρ φ u · p = ι · ρ).
  { now apply subst_pair_p. }
  split.
  +
    unfold subst_term'.
    generalize (subst_term_comp hsC (@ι _ (b φ)) (fibfill I φ (u' I ρ φ u) ρ (subst_pair_p hsC (ι · ρ) u)) (ctx_last hsC)).
    admit.
  + admit.
Admitted.


(* Composition operation *)
Definition comp_op {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄) : UU :=
    yo I ⊢ A⦃e₁_PreShv I · ρ⦄.

Definition comp_op_face {Γ : PreShv C} {A : Γ ⊢} {I : C}
  {ρ : yo (I+) --> Γ} {φ : yo I --> FF} {u : box I φ ⊢ A⦃ι · ρ⦄}
  (c : comp_op ρ φ u) : UU.
Proof.
set (x1 := subst_term' (@ι _ φ) c).
set (x2 := subst_term' (u_subst φ) u).
assert (eq : u_subst φ · (ι · ρ) = ι · (e₁_PreShv I · ρ)).
{ now apply (nat_trans_eq has_homsets_HSET); intros J; apply funextsec. }
(* Maybe we can split the equality? *)
(* use total2. *)
(* apply (pr1 x1 = pr1 x2). *)
(* intros H. *)

apply (x1 = transportf (λ x, yo I,φ ⊢ A⦃x⦄) eq x2).
Defined.

Definition comp_struct {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ (c : ∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄), comp_op ρ φ u),
  (∏ I (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄),
     comp_op_face (c _ ρ φ u)).
  (* × *)
  (* (∏ (I : C) (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) J (f : J --> I), *)
  (*    comp_op_uniform ρ φ u c J f). *)


(* Attempt at constructing comp from fill, this gets hard because of transports *)

(* Definition comp_op_from_fill_op2 {Γ : PreShv C} {A : Γ ⊢} {I : C} *)
(*   (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ι · ρ⦄) *)
(*   (f : fill_op ρ φ u) : comp_op2 ρ φ u := subst_term' (e₁_PreShv I) f. *)

(* Lemma transportf_subst_TypeIn (Γ Δ : PreShv C) (σ1 σ2 : Δ --> Γ) (eq : σ1 = σ2) *)
(*   (A : Γ ⊢) (I : C) (ρ : pr1 (pr1 Δ I)) (x : pr1 (pr1 (A⦃σ1⦄) (make_ob I ρ))) : *)
(*   transportf (λ x, pr1 (pr1 ((pr1 (A⦃x⦄))) (make_ob I ρ))) eq x = *)
(*   transportf (λ x, pr1 (pr1 A (make_ob I x))) (eqtohomot (eqtohomot (base_paths _ _ eq) I) ρ) x. *)
(* Proof. *)
(* now induction eq. *)
(* Qed. *)

(* Lemma transportf_TypeIn {Γ : PreShv C} (I : C) (ρ : pr1 (pr1 Γ I)) (A B : Γ ⊢) (e : A = B) *)
(*   (x : pr1 ((pr1 A) (make_ob I ρ))) : *)
(*   transportf (λ x0 : Γ ⊢, pr1 ((pr1 x0) (make_ob I ρ))) e x = *)
(*   transportf (λ x0 : hSet, pr1 x0) (eqtohomot (base_paths _ _ (base_paths _ _ e)) (make_ob I ρ)) x. *)

(* Lemma asdf {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) {A : Γ ⊢} *)
(*   (x : Δ ⊢ A⦃σ2⦄) (y : Δ ⊢ A⦃σ2⦄) *)
(*   (I : C) (ρ : pr1 (pr1 Θ I)) : *)
(*   x = y -> *)
(*   pr1 (@subst_term' _ _ _ σ2 σ1 A x) I ρ = pr1 (@subst_term' _ _ _ σ2 σ1 A y) I ρ. *)
(* Proof. *)
(* intros H. *)
(* now induction H. *)
(* Qed. *)

(* Definition comp_struct_from_fill_struct2 {Γ : PreShv C} {A : Γ ⊢} : *)
(*   fill_struct2 A → comp_struct2 A. *)
(* Proof. *)
(* intros [f1 f2]. *)
(* mkpair. *)
(* - intros I ρ φ u. *)
(*   apply (comp_op_from_fill_op2 ρ φ u (f1 I ρ φ u)). *)
(* - intros I ρ φ u. *)
(* unfold comp_op_face, comp_op_from_fill_op2. *)
(* unfold fill_op_face in *. *)
(* apply pathsinv0. *)
(* etrans. *)
(* apply maponpaths. *)
(* apply maponpaths. *)
(* eapply pathsinv0. *)
(* apply f2. *)
(* apply TermIn_eq. *)
(* etrans; [use pr1_transportf|]. *)
(* apply funextsec; intro J; apply funextsec; intro ρ'. *)
(* rewrite !transportf_forall. *)
(* etrans. *)
(* use transportf_subst_TypeIn. *)
(* unfold nat_trans_eq. *)
(* rewrite base_total2_paths. *)
(* rewrite toforallpaths_funextsec. *)
(* rewrite toforallpaths_funextsec. *)
(* rewrite idpath_transportf. *)
(* pathvia (pr1 (subst_term' (u_subst φ · ι) (f1 I ρ φ u)) J ρ'). *)
(* admit. *)
(* pathvia (pr1 (subst_term' (ι · e₁_PreShv I) (f1 I ρ φ u)) J ρ'). *)
(* unfold subst_term'. *)
(* admit. *)
(* admit. *)
(* Admitted. *)

End fill_struct.




(* First attempt: Not very good as uniformity gets very complicated *)
(* Some proofs are also extremely slow *)
Section try1.

(* Composition operation *)

(* Note that the substitutions are not combined, this way we avoid rewriting
   with subst_type_comp later on *)
Definition comp_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ) (φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄) : UU :=
    yo I ⊢ A⦃ρ⦄⦃e₁_PreShv I⦄.

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
- intros.
cbn.
unfold yoneda_morphisms_data.
simpl.
admit.
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
simpl in *.
unfold comp_op1 in *.
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

Require Import TypeTheory.Auxiliary.Auxiliary.

Definition comp_struct_from_fill_struct1 {Γ : PreShv C} {A : Γ ⊢} :
  fill_struct1 A → comp_struct1 A.
Proof.
intros [f1 f2].
mkpair.
- intros I ρ φ u.
  apply (comp_op_from_fill_op1 ρ φ u (f1 I ρ φ u)).
- split.
  + intros I ρ φ u.
unfold comp_op_face1, comp_op_from_fill_op1.
apply pathsinv0, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro J; apply funextsec; intro ρ'.
rewrite !transportf_forall, transportf_TypeIn.
rewrite (@base_paths_eq Γ A I ρ φ).
rewrite toforallpaths_funextsec, idpath_transportf.
generalize (f2 I ρ φ u).
Search subst_term.
unfold fill_op_face1.
intros H.
cbn.
admit.
Admitted.

Definition fill_op_from_comp_op1 {Γ : PreShv C} {A : Γ ⊢} {I : C}
  (ρ : yo (I+) --> Γ)(φ : yo I --> FF) (u : box I φ ⊢ A⦃ρ⦄⦃ι⦄)
  (c : comp_op1 ρ φ u) : fill_op1 ρ φ u.
Proof.
unfold comp_op1 in c.
unfold fill_op1.
Admitted.

End try1.


End cubical.