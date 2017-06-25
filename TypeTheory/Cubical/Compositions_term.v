(* Attempts at defining composition structures using terms instead (like in the paper) *)

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
