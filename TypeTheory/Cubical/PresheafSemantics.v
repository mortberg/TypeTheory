Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import TypeTheory.Auxiliary.Auxiliary.

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
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section upstream.

(* Redefine this so that it is transparent... *)
Lemma functor_data_eq {C C' : precategory_ob_mor} (F F' : functor_data C C')
      (H : ∏ (c : C), (pr1 F) c = (pr1 F') c)
      (H1 : ∏ (C1 C2 : ob C) (f : C1 --> C2),
            transportf (λ x : C', pr1 F' C1 --> x) (H C2)
                       (transportf (λ x : C', x --> pr1 F C2) (H C1) (pr2 F C1 C2 f)) =
            pr2 F' C1 C2 f) : F = F'.
Proof.
  use total2_paths_f.
  - use funextfun. intros c. exact (H c).
  - use funextsec. intros C1. use funextsec. intros C2. use funextsec. intros f.
    assert (e : transportf (λ x : C → C', ∏ a b : C, a --> b → x a --> x b)
                           (funextfun (pr1 F) (pr1 F') (λ c : C, H c))
                           (pr2 F) C1 C2 f =
                transportf (λ x : C → C', x C1 --> x C2)
                           (funextfun (pr1 F) (pr1 F') (λ c : C, H c))
                           ((pr2 F) C1 C2 f)).
    {
      induction (funextfun (pr1 F) (pr1 F') (λ c : C, H c)).
      apply idpath.
    }
    rewrite e. clear e.
    rewrite transport_mor_funextfun.
    rewrite transport_source_funextfun. rewrite transport_target_funextfun.
    exact (H1 C1 C2 f).
Defined.

Lemma transportf_to_transportb (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) :
  px = transportb P e py -> transportf P e px = py.
Proof.
intros H.
now rewrite H; apply transportfbinv.
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

Lemma base_paths_pair_path_in2 (X : UU) (P : X → UU) (x : X) (p q : P x) (e : p = q) :
  base_paths _ _ (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

End upstream.

(* Upstream this to ElementsOp.v? *)
Section prelims.

Context {C : precategory} {Γ : PreShv C}.

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).

(* Any f : J → I and ρ : Γ I defines a morphism from (J,,# Γ ρ) to (I,,ρ) in ∫ Γ *)
Definition mor_to_el_mor {I J : C} (f : J --> I) (ρ : pr1 Γ I : hSet) :
  ∫ Γ ⟦ make_ob J (# (pr1 Γ) f ρ), make_ob I ρ ⟧ :=
  make_mor (J,,# (pr1 Γ) f ρ) (I,,ρ) f (idpath (# (pr1 Γ) f ρ)).

Lemma make_ob_eq {I : C} {x y} (e : x = y) :
  make_ob I x = @make_ob C Γ I y.
Proof.
apply pair_path_in2, e.
Defined.

Lemma base_paths_make_ob_eq {I : C} x y (e : x = y) : base_paths _ _ (make_ob_eq e) = idpath I.
Proof.
now apply base_paths_pair_path_in2.
Qed.

Lemma transportf_make_ob_eq {I J} (f : C⟦J,I⟧) {a b} (e : make_ob J a = make_ob J b) :
  transportf (λ x : ∫ Γ, C⟦pr1 x,I⟧) e f = transportf (λ x, C⟦x,I⟧) (base_paths _ _ e) f.
Proof.
now induction e.
Qed.

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
  transportb (λ X, ∫ Γ⟦X, make_ob I ρ⟧) (make_ob_identity_eq ρ) (identity _).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl; rewrite transportf_make_ob_eq.
now unfold make_ob_identity_eq; rewrite base_paths_make_ob_eq, idpath_transportf.
Qed.

Lemma make_ob_comp_eq {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  make_ob _ (# (pr1 Γ) (f · g) ρ) = make_ob _ (# (pr1 Γ) g (# (pr1 Γ) f ρ)).
Proof.
exact (make_ob_eq (eqtohomot (functor_comp Γ f g) ρ)).
Defined.

Lemma mor_to_el_mor_comp {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  mor_to_el_mor (f · g) ρ =
  transportb (λ X, ∫ Γ⟦X,_⟧) (make_ob_comp_eq ρ f g)
             (mor_to_el_mor g (# (pr1 Γ) f ρ) · mor_to_el_mor f ρ).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl; rewrite transportf_make_ob_eq.
now unfold make_ob_comp_eq; rewrite base_paths_make_ob_eq, idpath_transportf.
Qed.

End prelims.

Section types.

Context {C : precategory} (hsC : has_homsets C).

(** Γ ⊢ A is interpreted as a presheaf of ∫ Γ. In Coq this is written A : Γ ⊢ *)
Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).

Local Notation "'1'" := (nat_trans_id _).

(** The substitution functor *)
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

(** The right adjoint to substitution *)
Definition π {Γ Δ : PreShv C} (σ : Δ --> Γ) :=
   right_adjoint (is_left_adjoint_subst_functor σ).

(* TODO: define the left adjoint as well? *)

(* Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Definition subst_type {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ :=
  subst_functor σ A.

Local Notation "A ⦃ s ⦄" := (subst_type A s) (at level 40, format "A ⦃ s ⦄").

(** A1 = A *)
Lemma subst_type_id {Γ : PreShv C} (A : Γ ⊢) : A⦃1⦄ = A.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
Defined.

(* It is important that the above proof is the way it is so the following is provable *)
Lemma base_paths_subst_type_id {Γ : PreShv C} (A : Γ ⊢) :
  base_paths _ _ (base_paths _ _ (subst_type_id A)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_id, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(* TODO: use different order for composition of substitutions? *)
(** A(σ1 σ2) = (A σ2) σ1 *)
Lemma subst_type_comp {Γ Δ Θ : PreShv C}
  (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) : A⦃σ1 · σ2⦄ = A⦃σ2⦄⦃σ1⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
Defined.

Lemma base_paths_subst_type_comp {Γ Δ Θ : PreShv C}
  (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) :
  base_paths _ _ (base_paths _ _ (subst_type_comp σ1 σ2 A)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_comp, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(** Context extension: given a context Γ and a type Γ ⊢ A define Γ.A *)
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

(** Context projection *)
Definition p {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A --> Γ.
Proof.
use mk_nat_trans.
- intros I X.
  apply (pr1 X).
- now intros I J f; apply funextsec.
Defined.

(** Note that ctx_ext and p defines one part of the equivalence:

     PreShv(∫ Γ) ≃ PreShv(C) / Γ

by: Γ ⊢ A  ↦  (Γ ⋆ A,p)

Intuition: Γ ⋆ A is over Γ by p

*)


(** Direct definition of terms: Γ ⊢ a : A *)
Definition TermIn {Γ : PreShv C} (A : Γ ⊢) : UU.
Proof.
use total2.
- apply (∏ (I : C) (ρ : pr1 (pr1 Γ I)), pr1 (pr1 A (make_ob I ρ))).
- intros a.
  apply (∏ (I J : C) (f : J --> I) (ρ : pr1 (pr1 Γ I)),
           # (pr1 A) (mor_to_el_mor f ρ) (a I ρ) = a J (# (pr1 Γ) f ρ)).
Defined.

Local Notation "Γ ⊢ A" := (@TermIn Γ A) (at level 50).

Definition mkTermIn {Γ : PreShv C} (A : Γ ⊢)
  (u : ∏ (I : C) (ρ : pr1 ((pr1 Γ) I)), pr1 ((pr1 A) (make_ob I ρ)))
  (Hu : ∏ I J (f : C ⟦ J, I ⟧) (ρ : pr1 ((pr1 Γ) I)),
        # (pr1 A) (mor_to_el_mor f ρ) (u I ρ) = u J (# (pr1 Γ) f ρ)) : Γ ⊢ A.
Proof.
mkpair.
- exact u.
- abstract (exact Hu).
Defined.

Lemma TermIn_eq {Γ : PreShv C} {A : Γ ⊢} (a b : Γ ⊢ A) (H : pr1 a = pr1 b) : a = b.
Proof.
apply subtypeEquality; trivial.
now intros x; repeat (apply impred; intros); apply setproperty.
Qed.

(* The last element of the context *)
Definition q {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A ⊢ A⦃p⦄.
Proof.
use mkTermIn.
+ intros I ρ.
  apply (pr2 ρ).
+ intros I J f ρ; cbn; apply map_on_two_paths; trivial.
  now apply cat_of_elems_mor_eq.
Defined.

Lemma transportf_term {Γ : PreShv C} (A : Γ ⊢) (a : Γ ⊢ A) (J : C)
  (x y : pr1 (pr1 Γ J)) (e : x = y) :
  transportf (λ x, pr1 (pr1 A (make_ob J x))) e (pr1 a J x) = pr1 a J y.
Proof.
now induction e.
Qed.

Lemma subst_term_prf {Γ Δ : PreShv C} (σ : Δ --> Γ) (A : Γ ⊢) (a : Γ ⊢ A)
  (I J : C) (f : C ⟦ J, I ⟧) (ρ : pr1 ((pr1 Δ) I)) :
  # (pr1 (A⦃σ⦄)) (mor_to_el_mor f ρ) (pr1 a I (pr1 σ I ρ)) =
  pr1 a J (pr1 σ J (# (pr1 Δ) f ρ)).
Proof.
set (eq := eqtohomot (nat_trans_ax σ I J f) ρ).
set (x := # (pr1 A) (mor_to_el_mor f (pr1 σ I ρ)) (pr1 a I (pr1 σ I ρ))).
pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) eq x).
{ apply pathsinv0.
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|]; cbn.
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq; cbn in *.
  rewrite transportf_total2; simpl; rewrite (transportf_make_ob_eq _ (make_ob_eq (!eq))).
  now rewrite base_paths_make_ob_eq, idpath_transportf. }
set (w := pr1 a J (# (pr1 Γ) f (pr1 σ I ρ))).
pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) eq w).
{ now apply maponpaths, (pr2 a I J f (pr1 σ _ ρ)). }
now apply transportf_term.
Qed.

(** Given Γ ⊢ a : A and a substitution σ : Δ → Γ we get Δ ⊢ aσ : Aσ *)
Definition subst_term {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) : Δ ⊢ A⦃σ⦄.
Proof.
use mkTermIn.
- intros I ρ.
  apply (pr1 a _ (pr1 σ I ρ)).
- apply subst_term_prf.
Defined.

Lemma transportf_TypeIn {Γ : PreShv C} (I : C) (ρ : pr1 (pr1 Γ I)) (A B : Γ ⊢) (e : A = B)
  (x : pr1 ((pr1 A) (make_ob I ρ))) :
  transportf (λ x0 : Γ ⊢, pr1 ((pr1 x0) (make_ob I ρ))) e x =
  transportf (λ x0 : hSet, pr1 x0) (eqtohomot (base_paths _ _ (base_paths _ _ e)) (make_ob I ρ)) x.
Proof.
now induction e.
Qed.

(* This lemma is not very useful? *)
Lemma transportf_subst_type0 {Γ Δ : PreShv C} (σ : Δ --> Γ)
  {A : Γ ⊢} {B : Γ ⊢} (a : Γ ⊢ A) (e : A = B) :
    transportf (λ x, Δ ⊢ x) (maponpaths (λ x, subst_type x σ) e)
               (subst_term σ a) =
    subst_term σ (transportf TermIn e a).
Proof.
now induction e.
Qed.

Lemma subst_term_id {Γ : PreShv C} {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term 1 a = transportb TermIn (subst_type_id A) a.
Proof.
apply transportb_to_transportf, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn.
now rewrite base_paths_subst_type_id, toforallpaths_funextsec, idpath_transportf.
Qed.

Lemma subst_term_comp {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term (σ1 · σ2) a =
  transportb (λ x, Θ ⊢ x) (subst_type_comp σ1 σ2 A) (subst_term σ1 (subst_term σ2 a)).
Proof.
apply transportb_to_transportf, TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn.
now rewrite (base_paths_subst_type_comp σ1 σ2 A), toforallpaths_funextsec, idpath_transportf.
Qed.

(** Pairing of substitutions *)
Definition subst_pair {Γ Δ : PreShv C} {A : Γ ⊢} (σ : Δ --> Γ) (a : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A.
Proof.
use mk_nat_trans.
- intros I ρ.
  apply (pr1 σ _ ρ,,pr1 a I ρ).
- intros I J f.
  apply funextsec; intro ρ; cbn.
  apply (total2_paths2_f (eqtohomot (nat_trans_ax σ I J f) ρ)).
  etrans; [eapply maponpaths, (!(pr2 a I J f ρ))|].
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq; simpl.
  rewrite transportf_total2; simpl.
  etrans; [apply transportf_make_ob_eq|].
  now rewrite base_paths_make_ob_eq, idpath_transportf.
Defined.

(* [a] = (1,a) *)
Definition subst_el {Γ : PreShv C} {A : Γ ⊢}  (a : Γ ⊢ A⦃1⦄) : Γ --> Γ ⋆ A :=
  subst_pair 1 a.

Definition term_to_subst {Γ : PreShv C} (A : Γ ⊢) (a : Γ ⊢ A) : Γ --> Γ ⋆ A.
Proof.
apply subst_el.
now rewrite subst_type_id. (* probably better to define more directly *)
Defined.

(* p(σ,a) = σ *)
Lemma subst_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  subst_pair σ a · p = σ.
Proof.
apply (nat_trans_eq has_homsets_HSET).
now intros I; apply funextsec.
Qed.

(* It is very important that this lemma is proved this way *)
Lemma subst_type_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  (A⦃p⦄)⦃subst_pair σ a⦄ = A⦃σ⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros c; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
Defined.

(* The above lemma could also be proved by: *)
(* set (e := maponpaths (λ σ, A⦃σ⦄) (subst_pair_p σ a)). *)
(* set (e' := !subst_type_comp (subst_pair σ a) p A). *)
(* exact (e' @ e). *)

(* Or even: *)
(* now rewrite <- subst_type_comp, subst_pair_p. *)

(* But if the definition is not the right one above the following lemma is not easily provable *)
Lemma base_paths_subst_type_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  base_paths _ _ (base_paths _ _ (subst_type_pair_p σ a)) =
  funextsec _ _ _ (λ c, idpath _).
Proof.
unfold subst_type_pair_p, functor_eq, functor_data_eq.
now rewrite !base_total2_paths.
Qed.

(* q(σ,a) = a *)
Lemma subst_pair_q {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  transportf (λ x, Δ ⊢ x) (subst_type_pair_p σ a) (subst_term (subst_pair σ a) q) = a.
Proof.
apply TermIn_eq.
etrans; [use pr1_transportf|].
apply funextsec; intro I; apply funextsec; intro ρ.
rewrite !transportf_forall, transportf_TypeIn.
now rewrite (base_paths_subst_type_pair_p σ a), toforallpaths_funextsec, idpath_transportf.
Qed.

(* TODO: prove this *)
(* Lemma subst_pair_subst {Γ Δ Θ : PreShv C} (σ1 : Δ --> Γ) (σ2 : Θ --> Δ) *)
(*   {A : Γ ⊢} (a : Δ ⊢ A⦃σ1⦄) : *)
(*   σ2 · subst_pair σ1 a = *)
(*   subst_pair (σ2 · σ1) (transportf (λ x : Θ ⊢, Θ ⊢ x) (!subst_type_comp σ2 σ1 A) (subst_term σ2 a)). *)
(* Proof. *)
(* apply (nat_trans_eq has_homsets_HSET); simpl; intros I. *)
(* apply funextsec; intro ρ. *)
(* apply pair_path_in2, pathsinv0. *)
(* Admitted. *)

(* (p,q) = 1 *)
Lemma subst_pair_id {Γ : PreShv C} {A : Γ ⊢} : subst_pair (A:=A) p q = 1.
Proof.
apply (nat_trans_eq has_homsets_HSET); simpl; intros I.
now apply funextsec.
Qed.


(** Γ ⊢ a : A can also be interpreted as sections s : Γ --> Γ.A to p *)
Definition TermInSection {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ s : Γ --> Γ ⋆ A, s · p = 1.

Lemma TermIn_to_TermInSection {Γ : PreShv C} (A : Γ ⊢) : TermIn A → TermInSection A.
Proof.
intros a.
mkpair.
- apply (term_to_subst _ a).
- abstract (apply (nat_trans_eq has_homsets_HSET);
            now intros I; simpl; apply funextfun).
Defined.

Lemma TermInSection_to_TermIn {Γ : PreShv C} (A : Γ ⊢) : TermInSection A → TermIn A.
Proof.
intros a.
rewrite <-subst_type_id, <- (pr2 a), subst_type_comp.
exact (subst_term _ q).
Defined.

(* This alternative definition of q is very slow *)
(* Definition q' {Γ : PreShv C} (A : Γ ⊢) : TermInSection (A⦃@p Γ A⦄). *)
(* Proof. *)
(* mkpair. *)
(* - use mk_nat_trans. *)
(*   + intros I ρ. *)
(*     exists ρ. *)
(*     apply (pr2 ρ). *)
(*   + abstract (intros I J f; apply funextsec; intro ρ; *)
(*               apply pair_path_in2; cbn; *)
(*               apply map_on_two_paths; trivial; *)
(*               now apply cat_of_elems_mor_eq). *)
(* (* This abstract is VERY slow *) *)
(* (* - abstract (apply (nat_trans_eq has_homsets_HSET); intros I; simpl; *) *)
(* (*             apply funextsec; intro ρ; apply idpath). *) *)
(* (* Defined. *) *)
(* Admitted. *)


(** Various results for instantiating TypeCat  *)

Definition p_gen {Γ Δ : PreShv C} {A : Δ ⊢} (σ : Δ --> Γ) : Δ ⋆ A --> Γ.
Proof.
use mk_nat_trans.
- intros I X.
  apply (pr1 σ _ (pr1 X)).
- intros I J f; apply funextsec; intro ρ.
  apply (eqtohomot (nat_trans_ax σ I J f) (pr1 ρ)).
Defined.

Definition q_gen {Γ Δ : PreShv C} {A : Γ ⊢} (σ : Δ --> Γ) : (Δ ⋆ (A⦃σ⦄)) ⊢ A⦃p_gen σ⦄.
Proof.
use mkTermIn.
- intros I ρ.
  apply (pr2 ρ).
- intros I J f ρ; cbn.
  now apply map_on_two_paths; [apply cat_of_elems_mor_eq|].
Defined.

Definition q_gen_mor {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⋆ (A⦃σ⦄) --> Γ ⋆ A :=
  subst_pair (p_gen σ) (q_gen σ).

Lemma q_gen_mor_p {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) :
  q_gen_mor A σ · p = p · σ.
Proof.
apply (nat_trans_eq has_homsets_HSET); intro I.
now apply funextsec.
Qed.

Lemma isPullback_q_gen_mor {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) :
  isPullback _ _ _ _ (q_gen_mor_p A σ).
Proof.
use pb_if_pointwise_pb.
intros I.
use isPullback_HSET.
intros a b eq.
use unique_exists.
- cbn in *.
  exists b.
  apply (transportf (λ x, pr1 (A (make_ob I x))) eq (pr2 a)).
- split; trivial; simpl.
  use total2_paths_f.
  + apply (!eq).
  + now cbn; rewrite transport_f_f, pathsinv0r, idpath_transportf.
- intros ρ.
  apply isapropdirprod, setproperty.
  assert (H : isaset (pr1 (pr1 (Γ ⋆ A) I))).
  { apply setproperty. }
  apply H.
- simpl; intros [x1 x2] [h1 h2].
  use total2_paths_f.
  + apply h2.
  + induction h2; induction h1; simpl.
    assert (H : eq = idpath _).
    { apply setproperty. }
    now rewrite H, !idpath_transportf.
Defined.

End types.


Section TypeCat.

Require Import TypeTheory.ALV1.TypeCat.

Context (C : precategory) (hsC : has_homsets C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).

Definition PreShv_TypeCat : type_cat_struct (PreShv C).
Proof.
mkpair.
- exists (λ Γ, Γ ⊢).
  exists (λ Γ A, Γ ⋆ A).
  intros Γ A Δ σ.
  exact (A⦃σ⦄).
- exists (λ Γ A, @p _ Γ A).
  exists (λ Γ A Δ σ, q_gen_mor hsC A σ).
  exists (λ Γ A Δ σ, q_gen_mor_p hsC A σ).
  intros Γ A Δ σ.
  exact (isPullback_q_gen_mor hsC A σ).
Defined.

End TypeCat.


Section CwF.

Require Import TypeTheory.OtherDefs.CwF_Pitts.

Context (C : precategory) (hsC : has_homsets C).

Local Notation "Γ ⊢" := (PreShv (∫ Γ)) (at level 50).
Local Notation "Γ ⊢ A" := (@TermIn _ Γ A) (at level 50).
Local Notation "A ⦃ s ⦄" := (subst_type hsC A s) (at level 40, format "A ⦃ s ⦄").
Local Notation "Γ ⋆ A" := (@ctx_ext _ Γ A) (at level 30).

Definition PreShv_tt_structure : tt_structure (PreShv C).
Proof.
exists (λ Γ, Γ ⊢).
intros Γ A.
exact (Γ ⊢ A).
Defined.

Lemma PreShv_reindx_structure : reindx_structure PreShv_tt_structure.
Proof.
mkpair.
- intros Γ Δ A σ.
  exact (A⦃σ⦄).
- intros Γ Δ A a σ.
  exact (subst_term _ σ a).
Defined.

Definition PreShv_tt_reindx_type_struct : tt_reindx_type_struct (PreShv C).
Proof.
mkpair.
+ exists (PreShv_tt_structure,,PreShv_reindx_structure).
  intros Γ A.
  exists (Γ ⋆ A).
  apply p.
+ intros Γ A.
  split.
  * apply q.
  * intros Δ σ a.
    exact (subst_pair hsC σ a).
Defined.

Lemma PreShv_reindx_laws : reindx_laws PreShv_tt_reindx_type_struct.
Proof.
mkpair.
- mkpair.
  + intros Γ A.
    apply subst_type_id.
  + intros Γ Δ Θ σ1 σ2 A.
    apply (subst_type_comp hsC).
- mkpair.
  + intros Γ A a.
    apply (subst_term_id hsC a).
  + intros Γ Δ Θ σ1 σ2 A a.
    exact (subst_term_comp hsC σ2 σ1 a). (* why is this slow? *)
Defined.

Definition PreShv_CwF : cwf_struct (PreShv C).
Proof.
exists PreShv_tt_reindx_type_struct.
mkpair.
- exists PreShv_reindx_laws.
  repeat split.
  + intros Γ A Δ σ a.
    exists (subst_pair_p hsC σ a).
    pathvia (transportf (λ x, Δ ⊢ x)
            (subst_type_pair_p hsC σ a) (subst_term hsC (subst_pair hsC σ a) (@q _ hsC _ A))).
    admit. (* why is this stated so complicated? *)
    apply subst_pair_q.
  + intros Γ A Δ Θ σ1 σ2 a.
    admit. (* haven't proved yet *)
    (* exact (subst_pair_subst hsC σ1 σ2 a). *)
  + intros Γ A.
    apply (@subst_pair_id C hsC Γ A).
- repeat split.
  + apply (functor_category_has_homsets C^op HSET has_homsets_HSET).
  + intros Γ.
    admit. (* this is not provable! *)
  + intros Γ A.
    use isaset_total2.
    * repeat (apply impred_isaset; intro); apply setproperty.
    * intros a; repeat (apply impred_isaset; intro).
      apply isasetaprop, setproperty.
Admitted.

End CwF.