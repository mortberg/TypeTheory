
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.Bicats.Auxiliary.
Require Import Systems.Bicats.Displayed_Precats.
Require Import Systems.Structures.
Require Import Systems.Structures_Cats.
Require Import Systems.CwF_SplitTypeCat_Maps.

Local Set Automatic Introduction.
(* only needed since imports globally unset it *)

Section Auxiliary.

(* TODO: seek, move, prove.

 ([isaprop_total2] in library is less convenient to apply.) *)
Lemma isaprop_total2' {A} {B : A -> Type} 
  (HA: isaprop A) (HB : forall x:A, isaprop (B x))
  : isaprop (total2 B).
Proof.
Admitted.

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "'Ty'" := (fun X Γ => (TY X : functor _ _) Γ : hSet) (at level 10).

(* TODO: replace [Q_comp_ext_compare] with this *)
Lemma Q_comp_ext_compare_general {C:precategory} {hsC}
  {X} {Y : families_structure hsC X}
  {Γ Γ':C} {A A' : Ty X Γ} (e : A = A') (t : Γ' ⇒ Γ ◂ A)
  : (Q Y A' : nat_trans _ _) _ (t ;; comp_ext_compare e)
  = (Q Y A : nat_trans _ _) _ t.
Proof.
  destruct e. apply maponpaths, id_right.
Qed.

End Auxiliary.

Section Fix_Context.

Context {C : Precategory}.

Local Notation hsC := (homset_property C).

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Notation "Γ ◂ A" := (comp_ext _ Γ A) (at level 30).
Local Notation "A [ f ]" := (# (TY _ : functor _ _ ) f A) (at level 4).

Local Notation Δ := comp_ext_compare.
Local Notation φ := obj_ext_mor_φ.

Section Compatible_Disp_Cat.

Definition strucs_compat_ob_mor
  : disp_precat_ob_mor (total_precat
      (families_disp_precat C × qq_structure_disp_precat C)).
Proof.
  use tpair.
  - intros XYZ. exact (compatible_scomp_families (pr1 (pr2 XYZ)) (pr2 (pr2 XYZ))).
  - simpl; intros; exact unit.
    (* For a given map of object-extension structures, a lifting to a map of either families-structures or _q_-morphism structues is essentially unique; so there is no extra compatibility condition required here on maps. *)
Defined.

Definition strucs_compat_id_comp
  : disp_precat_id_comp _ strucs_compat_ob_mor.
Proof.
  split; intros; exact tt.
Qed.

Definition strucs_compat_data : disp_precat_data _
  := ( _ ,, strucs_compat_id_comp).

Definition strucs_compat_axioms : disp_precat_axioms _ strucs_compat_data.
Proof.
  repeat apply tpair; intros; try apply isasetaprop; apply isapropunit.
Qed.

Definition strucs_compat_disp_precat
  : disp_precat (total_precat
      (families_disp_precat C × qq_structure_disp_precat C))
:= ( _ ,, strucs_compat_axioms).

End Compatible_Disp_Cat.

(** * Lemmas towards an equivalence *)

(** In the following two sections, we prove facts about [strucs_compat_disp_precat] which should be sufficient to imply (by general lemmas about displayed precategories) that it induces an equivalence between the (displayed) precategories of families structures and _q_-morphism structures. *)
 
Section Unique_QQ_From_Fam.

Lemma qq_from_fam_ob {X : obj_ext_precat} (Y : families_disp_precat C X)
  : Σ (Z : qq_structure_disp_precat C X), strucs_compat_disp_precat (X ,, (Y ,, Z)).
Proof.
  exists (qq_from_fam Y).
  apply iscompatible_qq_from_fam.
Defined.

Lemma qq_from_fam_mor {X X' : obj_ext_precat} {F : X ⇒ X'}
  {Y : families_disp_precat C X} {Y'} (FY : Y ⇒[F] Y')
  {Z : qq_structure_disp_precat C X} {Z'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Σ (FZ : Z ⇒[F] Z'), W ⇒[(F,,(FY,,FZ))] W'.
Proof.
  refine (_,, tt).
  intros Γ' Γ f A.
  cbn in W, W', FY. unfold compatible_scomp_families in *. 
  unfold families_mor in FY.
  (* Compare [term_to_section_naturality]. Perhaps worth abstracting? *)
  set (Pb := isPullback_preShv_to_pointwise hsC
        (isPullback_Q_pp Y' ((obj_ext_mor_TY F : nat_trans _ _) Γ A)) 
        (Γ' ◂ # (TY X : functor _ _) f A));
    simpl in Pb.
  apply (pullback_HSET_elements_unique Pb); clear Pb; unfold yoneda_morphisms_data.
  - etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, obj_ext_mor_ax.
      (* TODO: name of [obj_ext_mor_ax] unmemorable.  Rename more like [qq_π]? *)
    etrans. apply @pathsinv0, qq_π.
      (* TODO: name of [qq_π] misleading, suggests opposite direction. *)
    apply pathsinv0.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, @pathsinv0, qq_π.
    etrans. apply assoc. apply cancel_postcomposition.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths. apply comp_ext_compare_π.
    apply obj_ext_mor_ax.
  - etrans.
      (* Again, compare [H1] in [term_to_section_naturality].
      Surely there’s something to abstract! *)
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
    etrans. apply maponpaths, @pathsinv0, id_left.
    etrans. cbn. apply maponpaths.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (W _ _ _ _) _) _).
    apply pathsinv0.
    etrans.
      exact (!toforallpaths _ _ _
        (nat_trans_eq_pointwise (W' _ _ _ _) _) _).
    etrans. apply Q_comp_ext_compare_general.
    etrans. apply maponpaths, @pathsinv0, id_left.
    exact (!toforallpaths _ _ _
      (nat_trans_eq_pointwise (families_mor_Q FY _) _) _).
Qed.

Lemma qq_from_fam_mor_unique {X X' : obj_ext_precat} {F : X ⇒ X'}
  {Y : families_disp_precat C X} {Y'} (FY : Y ⇒[F] Y')
  {Z : qq_structure_disp_precat C X} {Z'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : isaprop (Σ (FZ : Z ⇒[F] Z'), W ⇒[(F,,(FY,,FZ))] W').
Proof.
  apply isaprop_total2'.
  - simpl. repeat (apply impred_isaprop; intro). apply hsC.
  - intros; simpl. apply isapropunit.
Qed.

End Unique_QQ_From_Fam.

Section Unique_Fam_From_QQ.

Lemma fam_from_qq_ob {X : obj_ext_precat} (Z : qq_structure_disp_precat C X)
  : Σ (Y : families_disp_precat C X), strucs_compat_disp_precat (X ,, (Y ,, Z)).
Proof.
  exists (fam_from_qq (pr1 Z) (pr2 Z)).
  apply iscompatible_fam_from_qq.
Defined.

Lemma fam_from_qq_mor {X X' : obj_ext_precat} {F : X ⇒ X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z ⇒[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : Σ (FY : Y ⇒[F] Y'), W ⇒[(F,,(FY,,FZ))] W'.
Admitted.

Lemma fam_from_qq_mor_unique {X X' : obj_ext_precat} {F : X ⇒ X'}
  {Z : qq_structure_disp_precat C X} {Z'} (FZ : Z ⇒[F] Z')
  {Y : families_disp_precat C X} {Y'}
  (W : strucs_compat_disp_precat (X,,(Y,,Z)))
  (W' : strucs_compat_disp_precat (X',,(Y',,Z')))
  : isaprop (Σ (FY : Y ⇒[F] Y'), W ⇒[(F,,(FY,,FZ))] W').
Proof.
  apply isaprop_total2'.
  - simpl. apply isaprop_families_mor.
  - intros; simpl. apply isapropunit.
Defined.

End Unique_Fam_From_QQ.


End Fix_Context.