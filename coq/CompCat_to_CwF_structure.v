
Require Import UniMath.RezkCompletion.total2_paths.

Require Import Systems.Auxiliary.
Require Import Systems.UnicodeNotations.
Require Import Systems.CompCat_structure.
Require Import Systems.cwf_structure.



(** * wF structure from (split) comprehension structure on a precategory 

Every pre-(split)-Comp-cat gives rise to a pre-category with families.

Since the components of the pre-cat with Families structure are highly successively dependent, we construct most of them individually, before putting them together in [cwf_of_comp_precat].
 *)

Section CwF_of_Comp. 

 
Context (CC : precategory) (C : split_comp_struct CC) (homs_sets : has_homsets CC).

Definition tt_structure_of_comp_cat : tt_structure CC.
Proof.
  unfold tt_structure.
  exists (ty_comp_cat C).
  intros Γ A.
  exact (Σ f : Γ ⇒ Γ ◂ A, f ;; dpr_comp_cat _  = identity _ ). 
Defined.


(* Maybe some of the below stuff should be opaque, to avoid too much unfolding? *)
Definition reindx_struct_of_comp_cat : reindx_structure tt_structure_of_comp_cat.
Proof.
  unfold reindx_structure.
  refine (tpair _ _ _ ).
  - intros Γ Γ'.
    unfold tt_structure_of_comp_cat.
    simpl.
    intros A γ.
    exact (reind_comp_cat A γ).
  - intros Γ Γ' A H. unfold tt_structure_of_comp_cat in *.
    simpl in *.
    intro γ.
    refine (tpair _ _ _ ).
    eapply map_into_Pb.
    apply reind_pb_comp_cat.
    etrans. Focus 2. eapply pathsinv0. apply id_left.
    etrans. cancel_postcomposition. apply (idpath (γ ;; pr1 H)).
    {   etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply (pr2 H).
        apply id_right.
    }
    apply Pb_map_commutes_2.
Defined.    

Definition tt_reindx_from_comp : tt_reindx_struct CC.
Proof.
  exists tt_structure_of_comp_cat.
  exact reindx_struct_of_comp_cat.
Defined.

Lemma reindx_laws_type_of_comp_cat : reindx_laws_type tt_reindx_from_comp.
Proof.
  split.
  - unfold tt_reindx_from_comp. simpl.
    intros Γ A.
    unfold rtype. simpl.
    assert (X:= pr2 (pr1 (pr2 C))). simpl in X.
    apply (pr1 X).
  - intros.
    assert (X:= pr1 (pr2 (pr2 C))). simpl in X.
    apply (X).
Defined.

Definition reindx_laws_terms_of_comp_cat : reindx_laws_terms  reindx_laws_type_of_comp_cat.
Proof.
  split.
  - intros; simpl. unfold tt_reindx_from_comp in *. simpl in *.
    apply total2_paths_second_isaprop.
    apply homs_sets. simpl.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + simpl.
      rewrite id_left.
      destruct a as [f H]; simpl in *.
      assert (X := (pr2 (pr1 (pr2 C)))). simpl in X.
      rewrite (pr2 X).

      assert (T:=@transportf_total2).
      assert (T':= T (C Γ) (λ B,  Γ ⇒ Γ ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f, f ;; dpr_comp_cat B = identity Γ)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A)).
      assert (T4 := T3 (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_comp_cat A = identity Γ) f H)).
      clear T3 T'' T'. simpl in T4.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      etrans.
      cancel_postcomposition. apply T5.

      clear T5.
      
      rewrite idtoiso_postcompose.
      etrans.
      eapply pathsinv0. apply functtransportf.
      rewrite transportf_pathscomp0.
      match goal with |[|- transportf _ ?e _ = _ ] =>
                       assert (He : e = idpath _ )  end .
      apply (pr1 (pr2 C)).
      rewrite He. apply idpath.
    +
      
      destruct a as [f H]; simpl in *.
      rewrite <- H.
      assert (T:=@transportf_total2).
      assert (T':= T (C Γ) (λ B,  Γ ⇒ Γ ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = f ;; dpr_comp_cat A)).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr1 (pr2 C))) Γ A) ).
      assert (T4 := T3  (tpair (λ f0 : Γ ⇒ Γ ◂ A, f0;; dpr_comp_cat A = f;; dpr_comp_cat A) f
                               (idpath (f;; dpr_comp_cat A)))).
      clear T3 T'' T'. simpl in T4.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      etrans.
      cancel_postcomposition. apply T5.
      clear T5.

      apply transportf_dpr_comp_cat.

  -

    intros.
    unfold tt_reindx_from_comp in *. simpl in *.
    apply total2_paths_second_isaprop.
    apply homs_sets. simpl.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + simpl.
      destruct a as [f H]; simpl in *.
      assert (X := (pr2 (pr2 (pr2 C)))). simpl in X.
      rewrite (X). clear X
      .

      assert (T:=@transportf_total2).

      rewrite assoc.
      assert (T':= T (C Γ'') (λ B,  Γ'' ⇒ Γ'' ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ'')).
      simpl in *.
      assert (T3:= T'' _ _  (! pr1 (pr2 (pr2 C)) Γ A Γ' γ Γ'' γ') ).

      match goal with | [ |- pr1 (transportf _ _ ?e ) ;; _ ;; _ = _ ] => set (E:=e) end.
      assert (T4 := T3 E).
      
      clear T3 T'' T'.
      assert (T5:= base_paths _ _ T4). clear T4; simpl in *.
      rewrite <- assoc.
      etrans.
      cancel_postcomposition. apply T5.

      clear T5 T.

      clear E.

      etrans. apply assoc.
      etrans. cancel_postcomposition. apply assoc.
      rewrite idtoiso_postcompose.

       etrans.
      eapply pathsinv0. cancel_postcomposition. cancel_postcomposition. apply functtransportf.
      rewrite transportf_pathscomp0.

      match goal with |[|- transportf ?a ?b ?c ;; _ ;; _ = _ ] =>
           set (a':=a); set (b':=b); set (c':=c) end.
      assert (T':= Pb_map_commutes_1).
      assert (b' = idpath _ ).
      apply (pr1 (pr2 C)).
      rewrite X.
      simpl.
      etrans.
      cancel_postcomposition.
      apply T'.
      etrans.
      eapply pathsinv0.
      apply assoc.
      etrans. Focus 2.
      apply assoc.
      apply maponpaths.
      etrans.
      apply T'.
      apply idpath.
 
    +
      idtac.
      match goal with |[|- pr1 (transportf ?P' ?e' ?x') ;; _ = _ ] =>
                       set (P:=P') ; set (e := e') ; set (x := x') end.
      assert (T:=@transportf_total2).
      assert (T':= T (C Γ'') (λ B,  Γ'' ⇒ Γ'' ◂ B)). simpl in T'.
      assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ'')).
        
      simpl in *.
      assert (T3:= T'' _ _  e x).
      assert (T5:= base_paths _ _ T3). clear T3; simpl in *. clear T' T'' T.
      etrans.
      cancel_postcomposition.
      apply T5.
      clear T5.
      etrans.
        apply transportf_dpr_comp_cat.
        set (T:=Pb_map_commutes_2).
        apply T.
Qed.

Definition reindx_laws_of_comp_cat : reindx_laws tt_reindx_from_comp.
Proof.
  exists reindx_laws_type_of_comp_cat.
  exact reindx_laws_terms_of_comp_cat.
Qed.

Definition comp_1_struct_of_comp_cat : comp_1_struct tt_reindx_from_comp.
Proof.
  unfold comp_1_struct.
  intros Γ A.
  refine (tpair _ _ _ ).
  unfold tt_reindx_from_comp in A. simpl in A.
  exact (ext_comp_cat Γ A).
  exact (dpr_comp_cat A).
Defined.

Definition tt_reindx_comp_1_of_comp_cat : tt_reindx_comp_1_struct CC .
Proof.
  exists tt_reindx_from_comp.
  exact comp_1_struct_of_comp_cat.
Defined.

Definition comp_2_struct_of_comp_cat : comp_2_struct tt_reindx_comp_1_of_comp_cat.
Proof.
  split.
  - unfold tt_reindx_comp_1_of_comp_cat in *.
    simpl in *.
    + refine (tpair _ _ _ ).
      * { eapply map_into_Pb.
          - apply  reind_pb_comp_cat.
          - cancel_postcomposition.
            apply (idpath (identity _ )). }
      * assert (T:= Pb_map_commutes_2).
        apply T.
  - intros Γ' γ.
    intro a.
    unfold tt_reindx_comp_1_of_comp_cat in *.
    simpl in *.
    apply (pr1 a ;; q_comp_cat _ _ ).
Defined.

Definition tt_reindx_comp_struct_of_comp_cat : tt_reindx_comp_struct CC.
Proof.
  exists tt_reindx_comp_1_of_comp_cat.
  exact  comp_2_struct_of_comp_cat.
Defined.

Lemma cwf_laws_of_comp_cat : cwf_laws tt_reindx_comp_struct_of_comp_cat .
Proof.
  repeat split.
  - exists reindx_laws_of_comp_cat.
    repeat split.
    + unfold comp_laws_1_2.
      intros Γ A Γ' γ a. unfold tt_reindx_comp_struct_of_comp_cat.
      simpl in * .
      refine (tpair _ _ _ ).
      * unfold pairing. simpl.
        destruct a as [f H]; simpl in *.
        etrans. eapply pathsinv0. apply assoc.
        etrans. apply maponpaths. apply dpr_q_comp_cat.
        etrans. apply assoc.
        etrans. cancel_postcomposition. apply H.
        apply id_left.
      * simpl.
        apply total2_paths_second_isaprop.
        { apply homs_sets. }
        destruct a as [f H]; simpl in *.
        match goal with |[ |- pr1 (transportf ?P' ?e' (transportf ?P1' ?e1' ?x')) = _ ] =>
                         set (P := P'); set (e:=e'); set (P1 := P1') ; set (e1:=e1'); set (x:=x') end.
        simpl in *.
        unfold pairing in *. simpl in *.
        etrans.
        apply maponpaths.
        apply maponpaths.
        assert (T:=@transportf_total2).
        assert (T':= T (C Γ') (λ B,  Γ' ⇒ Γ' ◂ B)). simpl in T'.
        assert (T'' := T' (λ B f0, f0 ;; dpr_comp_cat B = identity Γ')).
        simpl in *.
        assert (T3:= T'' _ _  e1 x).
        apply T3.

        
        match goal with |[|- pr1 (transportf _ _ ?x1') = _ ] => set (x1:= x1') end.
        assert (T:=@transportf_total2).
        assert (T' := T (Γ' ⇒ Γ)).
        unfold rtype in f.
        assert (T'':= T' (λ i, Γ' ⇒ Γ' ◂ reind_comp_cat A i)).
        simpl in T''.
        assert (T3 := T'' (λ i f0, f0 ;; dpr_comp_cat (reind_comp_cat A i) = identity Γ')).
        simpl in *.
        assert (T4:= T3 _ _  e x1).  
        assert (T5:= base_paths _ _ T4). clear T3; simpl in *. clear T' T'' T.
      etrans.
      apply T5.

      clear T5. clear T4.
      unfold x1; simpl in *. clear x1.
      clear x.
      match goal with |[ |- transportf _ _ ?e' = _ ] => set (x := e') end.
      pathvia (transportf (λ B, Γ' ⇒ Γ' ◂ B) (maponpaths _ e) x).
       { admit. }
      unfold x; clear x.
      rewrite transportf_pathscomp0.
      Check (e1 @ maponpaths _  e).
      admit.
    + admit.
    + admit.
  -  assumption.
  - admit.
  - admit.
Admitted.
    
End CwF_of_Comp.













