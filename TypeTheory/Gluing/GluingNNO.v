Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.ElementsOp.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.

Local Open Scope cat.
Local Open Scope Cat.

Section nno.

Context {C : precategory} (TC : Terminal C).

Local Notation "1" := TC.

Definition isNNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧) : hProp.
Proof.
use tpair.
- exact (∏ (a : C) (q : C ⟦ 1, a ⟧) (f : C ⟦ a, a ⟧),
         ∃! u : C ⟦ n, a ⟧, (z · u = q) × (s · u = u · f)).
- abstract (repeat (apply impred_isaprop; intros); apply isapropiscontr).
Defined.

Definition NNO : UU := 
  ∑ (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧), isNNO n z s.

Definition NNObject (n : NNO) : C := pr1 n.
Coercion NNObject : NNO >-> ob.

Definition zeroNNO (n : NNO) : C ⟦1,n⟧ := pr1 (pr2 n).
Definition sucNNO (n : NNO) : C ⟦n,n⟧ := pr1 (pr2 (pr2 n)).

Lemma isNNO_NNO (n : NNO) : isNNO n (zeroNNO n) (sucNNO n).
Proof.
exact (pr2 (pr2 (pr2 n))).
Qed.

Definition mk_NNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧)
 (h : isNNO n z s) : NNO := (n,,z,,s,,h).

Definition hasNNO : hProp := ∥ NNO ∥.

End nno.

Lemma nat_ob_NNO {C : precategory} (BC : BinCoproducts C) (hsC : has_homsets C) (TC : Terminal C) : 
  nat_ob C BC hsC TC → NNO TC.
Proof.
intros N.
use mk_NNO.
- exact (nat_ob_carrier _ _ _ _ N).
- apply nat_ob_z.
- apply nat_ob_s.
- intros n z s.
  use unique_exists.
  + apply (nat_ob_rec _ _ _ _ _ z s).
  + split; [ apply nat_ob_rec_z | apply nat_ob_rec_s ].
  + intros x; apply isapropdirprod; apply hsC.
  + intros x [H1 H2].
    transparent assert (xalg : (FunctorAlg (BinCoproduct_of_functors C C BC 
                                              (constant_functor C C TC)
                                              (functor_identity C)) hsC 
                                              ⟦ InitialObject N, mk_F_alg C BC hsC TC z s ⟧)).
    { refine (x,,_).
      abstract (apply pathsinv0; etrans; [apply precompWithBinCoproductArrow |]; 
                rewrite id_left, <- H1;
                etrans; [eapply maponpaths, pathsinv0, H2|];
                now apply pathsinv0, BinCoproductArrowUnique; rewrite assoc;
                apply maponpaths).
    }
    exact (maponpaths pr1 (InitialArrowUnique N (mk_F_alg C BC hsC TC z s) xalg)).
Defined.

Section natnno.

Lemma isNNO_nat : isNNO TerminalHSET natHSET (λ _, 0) S.
Proof.
intros X z s.
use unique_exists.
+ intros n.
  induction n as [|_ n].
  * exact (z tt).
  * exact (s n).
+ now split; apply funextfun; intros [].
+ now intros; apply isapropdirprod; apply setproperty.
+ intros q [hq1 hq2].
  apply funextfun; intros n.
  induction n as [|n IH].
  * now rewrite <- hq1.
  * cbn in *; now rewrite (toforallpaths _ _ _ hq2 n), IH.
Qed.

Definition NNO_HSET : NNO TerminalHSET.
Proof.
use mk_NNO.
- exact natHSET.
- exact (λ _, 0).
- exact S.
- exact isNNO_nat.
Defined.

End natnno.


Section gluing.

(* First define the 1-category of set categories with terminal object and nno *)
Definition setcatNNO : UU := ∑ (C : setcategory) (TC : Terminal C), (NNO TC).

Definition setcatNNOc : precategory.
Proof.
use mk_precategory.
- use tpair. 
  + exists setcatNNO.
    intros [x [TCx NNOx]] [y [TCy NNOy]].
    (* Morphisms are structure preserving functors *)
    apply (∑ (F : functor x y), (F TCx = TCy) × (F NNOx = NNOy)).
  + simpl.
use tpair.
* 
simpl.
intros c.
now exists (functor_identity (pr1 c)).
* 
simpl.
intros a b c [F [HF1 HF2]] [G [HG1 HG2]].
exists (functor_composite F G).
split.
now rewrite <- HG1, <- HF1.
now rewrite <- HG2, <- HF2.
- use tpair; try split.
*
cbn.
intros a b f.
apply subtypeEquality.
intros H.
apply isapropdirprod; apply (pr21 b).
apply functor_eq.
apply (pr21 b).
simpl.
cbn.
unfold functor_composite_data.
cbn.
unfold functor_data_constr.
Search total2 paths transportf.
eapply total2_paths_f.
cbn.
Unshelve.
cbn.
Focus 2.
apply idpath.
now rewrite idpath_transportf.
* 
cbn.
intros a b f.
apply subtypeEquality.
intros H.
apply isapropdirprod; apply (pr21 b).
apply functor_eq.
unfold has_homsets.
apply (pr21 b).
simpl.
cbn.
unfold functor_composite_data.
cbn.
unfold functor_data_constr.
Search total2 paths transportf.
eapply total2_paths_f.
cbn.
Unshelve.
cbn.
Focus 2.
apply idpath.
now rewrite idpath_transportf.
* cbn.
intros a b c d f g h.
apply subtypeEquality.
intros H.
apply isapropdirprod; apply (pr21 d).
apply functor_eq.
apply (pr21 d).
simpl.
cbn.
unfold functor_composite_data.
cbn.
unfold functor_data_constr.
Search total2 paths transportf.
eapply total2_paths_f.
cbn.
Unshelve.
cbn.
Focus 2.
apply idpath.
now rewrite idpath_transportf.
Defined.

(* Assume that we have an initial such category *)
Variable (C : setcatNNOc) (IC : isInitial _ C).

(* Assume that there is a setcategory V with the necessary structure *)
Context (V : setcategory) (TV : Terminal V) (NV : NNO TV).

Definition Vset : setcatNNOc := (V,,TV,,NV).

Local Notation "1" := TV.

(* TODO: add coercion *)
(* Assume that there is a functor to glue along (this is an
   abstraction over the global section functor) *)

(* What I need is that for each object X of C there is a set
   C(1,X). But I think it also really has to be a functor... *)
Context (F : functor (pr1 C) (pr1 Vset)).

(* F has to preserve the terminal object *)
Context (HF : iso TV (F (pr12 C))).

(* Now the define the glue category of F *)
Definition glue : precategory.
Proof.
use mk_precategory.
- use tpair.
  + exists (∑ (x : V) (a : pr1 C), V⟦x,F a⟧).
    intros XAα YBβ.
    exact (∑ (f01 : V⟦pr1 XAα,pr1 YBβ⟧ × pr1 C⟦pr12 XAα, pr12 YBβ⟧),
             pr22 XAα · # F (pr2 f01) = (pr1 f01) · pr22 YBβ).
  + split; cbn.
    * intros XAα.
      exists (identity (pr1 XAα),,identity (pr12 XAα)); simpl.
      abstract (now rewrite functor_id, id_left, id_right).
    * intros XAα1 XAα2 XAα3 f0 f1.
      exists (compose (pr11 f0) (pr11 f1),,compose (pr21 f0) (pr21 f1)); simpl.
      abstract (rewrite functor_comp, assoc, (pr2 f0), <- !assoc;
                apply cancel_precomposition, (pr2 f1)).
- split; [split|]; simpl.
+ intros.
  apply subtypeEquality; simpl.
  * intros H; apply (pr22 V).
  * now rewrite !id_left.
+ intros.
  apply subtypeEquality; simpl.
  * intros H; apply (pr22 V).
  * now rewrite !id_right.
+ intros.
  apply subtypeEquality; simpl.
  * intros H; apply (pr22 V).
  * now rewrite !assoc.
Defined.

Definition TG : Terminal glue.
Proof.
use mk_Terminal.
+ exists TV.
  exists (pr12 C).
  exact (pr1 HF).
+
 intros g.
simpl.
use unique_exists.
split.
apply TerminalArrow.
apply TerminalArrow.
apply pathsinv0.
apply iso_inv_to_right, pathsinv0.
apply TerminalArrowUnique.
intros X.
simpl.
apply (pr22 V).
simpl.
intros X HX.
use total2_paths_f; apply TerminalArrowUnique.
Defined.


End gluing.