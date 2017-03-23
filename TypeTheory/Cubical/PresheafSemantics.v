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

Require Import TypeTheory.OtherDefs.CwF_Pitts.
Require Import TypeTheory.Auxiliary.Auxiliary.

Local Open Scope cat.

Ltac pathvia b := (eapply (@pathscomp0 _ _ b _ )).

Section upstream.

Lemma transportf_to_transportb (X : UU) (P : X -> UU) (x y : X) (e : x = y) (px : P x) (py : P y) :
  px = transportb P e py -> transportf P e px = py.
Proof.
intros H.
rewrite H.
apply transportfbinv.
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

Lemma pr1_pair_path_in2 (X : UU) (P : X → UU) (x : X) (p q : P x) (e : p = q) :
  maponpaths pr1 (pair_path_in2 P e) = idpath x.
Proof.
now induction e.
Qed.

End upstream.

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
  transportb (λ X, ∫ Γ⟦X, make_ob I ρ⟧) (make_ob_eq (eqtohomot (functor_id Γ I) ρ)) (identity _).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl.
etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (make_ob_identity_eq _))|].
assert (H : maponpaths pr1 (make_ob_identity_eq ρ) = idpath _).
{ apply pr1_pair_path_in2. }
now rewrite H, idpath_transportf.
Qed.

Lemma mor_to_el_mor_comp_eq {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
 make_ob _ (# (pr1 Γ) (f · g) ρ) = make_ob _ (# (pr1 Γ) g (# (pr1 Γ) f ρ)).
Proof.
exact (make_ob_eq (eqtohomot (functor_comp Γ f g) ρ)).
Defined.

Lemma mor_to_el_mor_comp {I J K} (ρ : pr1 (pr1 Γ I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  mor_to_el_mor (f · g) ρ =
  transportb (λ X, ∫ Γ⟦X,_⟧) (mor_to_el_mor_comp_eq ρ f g)
             (mor_to_el_mor g (# (pr1 Γ) f ρ) · mor_to_el_mor f ρ).
Proof.
apply (transportb_to_transportf _ (λ X : ∫ Γ, ∫ Γ ⟦X,_⟧)), cat_of_elems_mor_eq; simpl.
rewrite transportf_total2; simpl.
etrans; [apply (functtransportf pr1 (λ x, C⟦x,I⟧) (mor_to_el_mor_comp_eq ρ f g))|].
assert (H : maponpaths pr1 (mor_to_el_mor_comp_eq ρ f g) = idpath _).
{ apply pr1_pair_path_in2. }
now rewrite H, idpath_transportf.
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

(* TODO: define the left adjoints as well? *)

(* Given Γ ⊢ A and a substitution σ : Δ → Γ we get Δ ⊢ Aσ *)
Definition subst_type {Γ Δ : PreShv C} (A : Γ ⊢) (σ : Δ --> Γ) : Δ ⊢ :=
  subst_functor σ A.

Local Notation "A ⦃ s ⦄" := (subst_type A s) (at level 40, format "A ⦃ s ⦄").

(** A1 = A *)
Lemma subst_type_id (Γ : PreShv C) (A : Γ ⊢) : A⦃1⦄ = A.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros [c1 c2]; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
(* apply (functor_eq _ _ has_homsets_HSET). *)
(* use functor_data_eq. *)
(* - intros c. cbn. unfold get_ob, get_el. apply maponpaths. *)
(* apply pathsinv0. *)
(* apply tppr. *)
(* - *)
(* intros a b f. *)
(* induction a as [a1 a2]. *)
(* induction b as [b1 b2]. *)
(* cbn. *)
(* apply maponpaths. *)
(* apply subtypeEquality; trivial. *)
(* intros x; apply setproperty. *)
(* intros [a1 a2] [b1 b2] f; cbn; *)
(*   now apply maponpaths, subtypeEquality; [intros x; apply setproperty|]. *)
Qed.

Print subst_type_id.

(* TODO: use different order for composition of substitutions? *)
(** A(σ1 σ2) = (A σ2) σ1 *)
Lemma subst_type_comp (Γ Δ Θ : PreShv C)
  (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) (A : Γ ⊢) : A⦃σ1 · σ2⦄ = A⦃σ2⦄⦃σ1⦄.
Proof.
apply (functor_eq _ _ has_homsets_HSET).
use functor_data_eq.
- intros [c1 c2]; apply idpath.
- intros [a1 a2] [b1 b2] f; cbn.
  now apply maponpaths, subtypeEquality; [intros x; apply setproperty|].
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

(* The last element of the context *)
Definition q {Γ : PreShv C} {A : Γ ⊢} : Γ ⋆ A ⊢ A⦃p⦄.
Proof.
use mkTermIn.
+ intros I ρ.
  apply (pr2 ρ).
+ intros I J f ρ; cbn; apply map_on_two_paths; trivial.
  now apply cat_of_elems_mor_eq.
Defined.

Lemma temp {Γ : PreShv C} (A : Γ ⊢) (a : Γ ⊢ A) (J : C) (x y : pr1 (pr1 Γ J)) (e : x = y) :
  transportf (λ x, pr1 (pr1 A (make_ob J x))) e (pr1 a J x) = pr1 a J y.
Proof.
now induction e.
Qed.

(** Given Γ ⊢ a : A and a substitution σ : Δ → Γ we get Δ ⊢ aσ : Aσ *)
Definition subst_term {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) : Δ ⊢ A⦃σ⦄.
Proof.
use mkTermIn.
- intros I ρ.
  apply (pr1 a _ (pr1 σ I ρ)).
- intros I J f ρ.
  generalize (pr2 a I J f (pr1 σ _ ρ)).
  set (H := eqtohomot (nat_trans_ax σ I J f) ρ).
  cbn in *.
  intros H2.
  match goal with |- ?XX = ?YY => set (X := XX); set (Y := YY) end.
  cbn in *.
  set (W := # (pr1 A) (mor_to_el_mor f (σ I ρ)) (pr1 a I (σ I ρ))).
  pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) H W).
  { unfold X, W, H.
  apply pathsinv0.
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
  apply cat_of_elems_mor_eq.
  cbn in *.
  match goal with |- get_mor (transportf _ ?XXX _) = ?ZZ => set (XX := XXX); set (Z := ZZ) end.
  unfold mor_to_el_mor, make_mor.
  rewrite transportf_total2.
  cbn.
  assert (transportf (λ x : ∑ c : C, pr1 (Γ c), C ⟦ pr1 x, I ⟧) XX f =
          transportf (λ x, C ⟦ x, I ⟧) (maponpaths pr1 XX) f).
  induction XX.
  trivial.
  etrans.
  apply X0.
  assert (HHH : maponpaths pr1 XX = idpath _).
  apply pr1_pair_path_in2.
  rewrite HHH.
  now rewrite idpath_transportf.
  }
  set (W2 := pr1 a J (# (pr1 Γ) f (σ I ρ))).
  apply pathsinv0.
  pathvia (transportb (λ x, pr1 ((pr1 A) (make_ob J x))) H W2).
  { apply pathsinv0, temp. }
  now apply maponpaths.
Defined.

Lemma transportf_subst_type0 {Γ Δ : PreShv C} (σ : Δ --> Γ)
  {A : Γ ⊢} {B : Γ ⊢} (a : Γ ⊢ A) (e : A = B) :  
    transportf (λ x, Δ ⊢ x) (maponpaths (λ x, subst_type x σ) e)
               (subst_term σ a) =
    subst_term σ (transportf TermIn e a).
Proof.
now induction e.
Qed.

(* Lemma moo (Γ : opp_precat_data C ⟶ hset_precategory_data) (I : C) *)
(*   (ρ : pr1 ((pr1 Γ) I)) (F G : Γ ⊢) (x : pr1 ((pr1 F) (I,,ρ))) (e : G = F) : *)
(*   transportf (λ x : opp_precat_data (cat_of_elems_data Γ) ⟶ hset_precategory_data, pr1 ((pr1 x) (I,,ρ))) e x = x. *)
Lemma functor_eq_pointwise (D1 D2 : precategory) (F G : functor D1 D2) (e : F = G) :
  ∏ x : D1, F x = G x.
Proof.
intro x.
now rewrite e.
Qed.

Lemma asdf (A : hSet) (a : A) (e : a = a) : e = idpath a.
Proof.
apply setproperty.
Defined.


Lemma transportf_subst_type1 {Γ : PreShv C} 
  {A : Γ ⊢} (a : Γ ⊢ A) : 
  subst_term 1 a = transportb TermIn (subst_type_id Γ A) a.
Proof.
apply transportb_to_transportf.
apply subtypeEquality.
(* TODO: state a general equality lemma for elements *)
intros x.
repeat (apply impred; intros).
apply setproperty.
etrans.
use pr1_transportf.
apply funextsec; intro I.
apply funextsec; intro ρ.
induction a as [a1 a2].
rewrite !transportf_forall.
cbn.
match goal with |- transportf ?XX ?YY ?ZZ = ?WW => set (X := XX); set (Y := YY) end.
set (x := a1 I ρ).
pathvia (transportf (λ x,pr1 ((pr1 x) (make_ob I ρ))) (maponpaths pr1 Y) x).
now induction Y.
unfold Y, x.
clear -I.
pathvia (transportf (λ x : _ -> hSet ,pr1 (x (make_ob I ρ))) (maponpaths pr1  (maponpaths pr1 (subst_type_id Γ A))) (a1 I ρ)).
generalize ((maponpaths pr1 (subst_type_id Γ A))) .
intros p.
cbn in *.
now induction p.
match goal with |- transportf ?XX ?YY ?ZZ = ?WW => set (X := XX); set (Y := YY) end.
pathvia (transportf (λ x : hSet,pr1 x) (eqtohomot Y (I,,ρ)) (a1 I ρ)).
now induction Y.
unfold Y.
clear -I.
simpl.
match goal with |- transportf ?XX ?YY ?ZZ = ?WW => set (X := XX); set (Y := YY) end.
simpl in Y.
unfold identity in Y.
simpl in *.
set (x := a1 I ρ).
clearbody x.
clearbody Y.
Check (A (I,,ρ)).
clear -I.
rewrite (@functtransportf hSet UU pr1 (idfun UU)).
cbn in *.
Check (maponpaths pr1 Y).
Check (pr1 (A (I,,ρ))).
(* assert (Y = idpath _). *)
(* Check (A (I,,ρ)). *)
(* admit. *)
(* rewrite X0. *)
(* cbn. *)
(* trivial. *)

(* pathvia (transportf (λ _,pr1 ((pr1 A) (make_ob I ρ))) (maponpaths pr1 p) x). *)
(* cbn. *)
(* admit. *)
(* now induction p. *)
Admitted.

Lemma subst_term_id {Γ : PreShv C} {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term 1 a = transportb TermIn (subst_type_id Γ A) a.
Proof.
induction a as [a1 a2].
apply subtypeEquality.
(* TODO: state a general equality lemma for elements *)
intros x.
repeat (apply impred; intros).
apply setproperty.
cbn.
apply funextsec; intro I.
apply funextsec; intro ρ.
unfold transportb.
Check pr1_transportf.
admit.
Admitted.

Lemma subst_term_comp {Γ Δ Θ : PreShv C} (σ1 : Θ --> Δ) (σ2 : Δ --> Γ) {A : Γ ⊢} (a : Γ ⊢ A) :
  subst_term (σ1 · σ2) a =
  transportb (λ x, Θ ⊢ x) (subst_type_comp _ _ _ σ1 σ2 A)(subst_term σ1 (subst_term σ2 a)).
Proof.
induction a as [a1 a2].
apply subtypeEquality.
(* TODO: state a general equality lemma for elements *)
intros x.
repeat (apply impred; intros).
apply setproperty.
cbn.
apply funextsec; intro I.
apply funextsec; intro ρ.
admit.
Admitted.

(** Pairing of substitutions *)
Definition subst_pair {Γ Δ : PreShv C} {A : Γ ⊢} (σ : Δ --> Γ) (a : Δ ⊢ A⦃σ⦄) : Δ --> Γ ⋆ A.
Proof.
use mk_nat_trans.
- simpl; intros I ρ.
  mkpair.
  + apply (pr1 σ _ ρ).
  + apply (pr1 a I ρ).
- intros I J f.
  apply funextsec; intro ρ; cbn in *.
  use total2_paths2_f.
  apply (eqtohomot (nat_trans_ax σ I J f) ρ).
  set (H:=pr2 a I J f ρ).
  cbn in H.
  etrans.
  eapply maponpaths.
  apply (!H).
  etrans; [use transportf_make_ob|].
  etrans; [apply (transportf_PreShv (∫ Γ) A)|].
  apply map_on_two_paths; trivial.
    apply cat_of_elems_mor_eq.
  cbn.
  rewrite transportf_total2.
  cbn.
  match goal with |- transportf _ ?XXX _ = _ => set (XX := XXX) end.
  assert (transportf (λ x : ∑ c : C, pr1 (Γ c), C ⟦ pr1 x, I ⟧) XX f =
          transportf (λ x, C ⟦ x, I ⟧) (maponpaths pr1 XX) f).
  induction XX.
  trivial.
  etrans.
  apply X.
  assert (HHH : maponpaths pr1 XX = idpath _).
  apply pr1_pair_path_in2.
  rewrite HHH.
  now rewrite idpath_transportf.
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

Lemma subst_type_pair_p {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) :
  (A⦃p⦄)⦃subst_pair σ a⦄ = A⦃σ⦄.
Proof.
now rewrite <- subst_type_comp, subst_pair_p.
Defined.

(* q(σ,a) = a *)
(* Lemma subst_pair_q {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) : *)
(*   subst_term (subst_pair σ a) q = *)
(*   transportb (λ x, Δ ⊢ x) (subst_type_pair_p σ a) a. *)
(* Proof. *)
(* induction a as [a1 a2]. *)
(* apply subtypeEquality. *)
(* (* TODO: state a general equality lemma for elements *) *)
(* intros x. *)
(* repeat (apply impred; intros). *)
(* apply setproperty. *)
(* cbn. *)
(* apply funextsec; intro I. *)
(* apply funextsec; intro ρ. *)
(* admit. *)
(* Admitted. *)

(* Lemma subst_pair_subst {Γ Δ : PreShv C} (σ : Δ --> Γ) {A : Γ ⊢} (a : Δ ⊢ A⦃σ⦄) (τ : ?) : *)
(*   (subst_pair σ a) τ = subst_pair (σ τ) (a τ). *)

Lemma subst_pair_id {Γ : PreShv C} {A : Γ ⊢} : subst_pair (A:=A) p q = 1.
Proof.
apply (nat_trans_eq has_homsets_HSET).
simpl; intros I.
apply funextsec; intro ρ; cbn.
apply pathsinv0, tppr.
Qed.


(** Γ ⊢ a : A can also be interpreted as sections s : Γ --> Γ.A to p *)
Definition TermInSection {Γ : PreShv C} (A : Γ ⊢) : UU :=
  ∑ s : Γ --> Γ ⋆ A, s · p = 1.

Lemma TermIn_to_TermInSection {Γ : PreShv C} (A : Γ ⊢) : TermIn A → TermInSection A.
Proof.
intros a.
(* intros [a p]. *)
mkpair.
- apply (term_to_subst _ a).
(* + use mk_nat_trans. *)
(*   - intros I ρ. *)
(*     apply (ρ,,a I ρ). *)
(*   - intros I J f. *)
(*     apply funextfun; intro ρ; apply pair_path_in2. *)
(*     now rewrite p. *)
- abstract (apply (nat_trans_eq has_homsets_HSET);
            now intros I; simpl; apply funextfun).
Defined.

Lemma TermInSection_to_TermIn {Γ : PreShv C} (A : Γ ⊢) : TermInSection A → TermIn A.
Proof.
intros [a pa].
generalize (subst_term a q).
now rewrite <- subst_type_comp, pa, subst_type_id.
Defined.


(* s : Γ --> Γ.A
   σ : Δ --> Γ
Need 
Δ --> Δ.A⦃σ⦄
*)

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

End types.


Section CwF.

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
    admit. (* we expressed this differently *)
  + intros Γ A Δ Θ σ1 σ2 a.
    admit. (* don't have yet *)
  + intros Γ A.
    apply (@subst_pair_id C hsC Γ A).
- repeat split.
  + apply (functor_category_has_homsets C^op HSET has_homsets_HSET).
  + intros Γ.
    (* hmm, how to prove this? *)
    (* apply (functor_isaset _ _ has_homsets_HSET). *)
    admit.
  + intros Γ A.
    use isaset_total2.
    * repeat (apply impred_isaset; intro); apply setproperty.
    * intros a; repeat (apply impred_isaset; intro).
      apply isasetaprop, setproperty.
Admitted.

End CwF.