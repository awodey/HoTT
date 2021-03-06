(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import Constant Factorization UnivalenceImpliesFunext.
Require Import Modalities.Modality hit.Truncations hit.Connectedness.
Import TrM.

Local Open Scope path_scope.

(** * BAut(X) *)

(** ** Basics *)

(** [BAut X] is the type of types that are merely equivalent to [X]. *)
Definition BAut (X : Type) := { Z : Type & merely (Z = X) }.

(** Equivalently, [BAut X] is the (-1)-image of the classifying map [1 -> Type] of [X]. *)

Definition equiv_baut_image_unit X
: BAut X <~> image (Tr -1) (unit_name X).
Proof.
  unfold BAut, image; simpl.
  refine (equiv_functor_sigma' (equiv_idmap Type) _); intros Z; simpl.
  apply equiv_O_functor; unfold hfiber.
  refine (equiv_compose' (equiv_inverse (equiv_contr_sigma _)) _).
  apply equiv_path_inverse.
Defined.

(** It is canonically pointed by [X] itself. *)
Global Instance ispointed_baut X : IsPointed (BAut X)
  := (X ; tr 1).

Definition BAut_pr1 X : BAut X -> Type := pr1.
Coercion BAut_pr1 : BAut >-> Sortclass.

Definition path_baut `{Univalence} {X} (Z Z' : BAut X)
: (Z <~> Z') <~> (Z = Z' :> BAut X).
Proof.
  eapply equiv_compose'.
  - apply equiv_path_sigma_hprop.
  - apply equiv_path_universe.
Defined.

Definition ap_pr1_path_baut `{Univalence} {X}
           {Z Z' : BAut X} (f : Z <~> Z')
: ap (BAut_pr1 X) (path_baut Z Z' f) = path_universe f.
Proof.
  unfold path_baut, BAut_pr1; simpl.
  apply ap_pr1_path_sigma_hprop.
Defined.

Definition transport_path_baut `{Univalence} {X}
           {Z Z' : BAut X} (f : Z <~> Z') (z : Z)
: transport (fun (W:BAut X) => W) (path_baut Z Z' f) z = f z.
Proof.
  refine (transport_compose idmap (BAut_pr1 X) _ _ @ _).
  refine (_ @ transport_path_universe f z).
  apply ap10, ap, ap_pr1_path_baut.
Defined.

(** ** Truncation *)

(** If [X] is an [n.+1]-type, then [BAut X] is an [n.+2]-type. *)
Global Instance trunc_baut `{Univalence} {n X} `{IsTrunc n.+1 X}
: IsTrunc n.+2 (BAut X).
Proof.
  intros [Z p] [W q].
  strip_truncations.
  refine (@trunc_equiv' _ _ (path_baut _ _) n.+1 _); simpl.
  symmetry in q; destruct q.
  symmetry in p; destruct p.
  exact _.
Defined.

(** And it is 0-connected *)
Global Instance isconnected_baut X : IsConnected 0 (BAut X).
Proof.
  refine (conn_pointed_type (point (BAut X))); try exact _.
  pose (c := conn_map_compose (Tr -1)
                              (factor1 (image (Tr -1) (unit_name X)))
                              (equiv_baut_image_unit X)^-1).
  refine (conn_map_homotopic _ _ _ _ c); intros []; reflexivity.
Defined.

(** Therefore, any two points in it are merely equal. *)
Definition merely_path_baut `{Univalence} {X} (Z Z' : BAut X)
: merely (Z = Z')
:= merely_path_is0connected (BAut X) Z Z'.

(** The following tactic, which applies when trying to prove an hprop, replaces all assumed elements of [BAut X] by [X] itself. *)
Ltac baut_reduce :=
  progress repeat
    match goal with
      | [ Z : BAut ?X |- _ ]
        => let Zispoint := fresh "Zispoint" in
           assert (Zispoint := merely_path_baut (point (BAut X)) Z);
           revert Zispoint;
           refine (@Trunc_ind _ _ _ _ _);
           intro Zispoint;
           destruct Zispoint
    end.

(** If [X] is truncated, then so is every element of [BAut X]. *)
Global Instance trunc_el_baut `{Funext} {n X} `{IsTrunc n X} (Z : BAut X)
: IsTrunc n Z.
Proof.
  destruct Z as [Z p].
  strip_truncations.
  destruct p; exact _.
Defined.

(** ** Centers *)

(** The following lemma says that to define a section of a family [P] of hsets over [BAut X], it is equivalent to define an element of [P X] which is fixed by all automorphisms of [X]. *)
Lemma baut_ind_hset `{Univalence} X
      (** It ought to be possible to allow more generally [P : BAut X -> Type], but the proof would get more complicated, and this version suffices for present applications. *)
      (P : Type -> Type) `{forall (Z : BAut X), IsHSet (P Z)}
: { e : P (point (BAut X)) &
    forall g : X <~> X, transport P (path_universe g) e = e }
  <~> (forall (Z:BAut X), P Z).
Proof.
  refine (equiv_compose' (equiv_sigT_ind _) _).
  (** We use the fact that maps out of a propositional truncation into an hset are equivalent to weakly constant functions. *)
  refine (equiv_compose'
           (equiv_functor_forall'
             (P := fun Z => { f : (Z=X) -> P Z & WeaklyConstant f })
             (equiv_idmap Type)
             (fun Z => equiv_merely_rec_hset _ _)) _); simpl.
  { intros p. change (IsHSet (P (BAut_pr1 X (Z ; tr p)))). exact _. }
  unfold WeaklyConstant.
  (** Now we peel away a bunch of contractible types. *)
  refine (equiv_compose' (equiv_sigT_coind _ _) _).
  refine (equiv_compose' (equiv_functor_sigma'
           (P := fun k => forall Z p q, k (Z;p) = k (Z;q))
           (equiv_inverse (equiv_sigT_ind
              (fun Zp => P Zp.1))) (fun k => equiv_idmap _)) _).
  refine (equiv_compose' (equiv_functor_sigma'
           (equiv_idmap (forall Zp : {Z:Type & Z=X}, P Zp.1))
           (fun k => equiv_inverse (equiv_sigT_ind
                     (fun Zp => forall q, k Zp = k (Zp.1;q))))) _).
  refine (equiv_compose' (equiv_functor_sigma'
           (equiv_idmap (forall Zp : {Z:Type & Z=X}, P Zp.1))
           (fun k => equiv_inverse (equiv_contr_forall
                     (fun Zp => forall q, k Zp = k (Zp.1;q))))) _); simpl.
  refine (equiv_compose' (equiv_functor_sigma'
           (P := fun (e : P X) => forall q:X=X, transport P q^ e = e)
           (equiv_inverse (equiv_contr_forall
             (fun (Zp:{Z:Type & Z=X}) => P Zp.1)))
             (fun f => equiv_functor_forall' (equiv_idmap (X=X)) _)) _).
  { intros g; simpl.
    refine (equiv_compose' (equiv_path_inverse _ _) _).
    apply equiv_concat_l.
    refine (transport_compose P pr1 (path_contr (X;1) (X;g)) f @ _).
    apply transport2.
    refine (ap_pr1_path_contr_basedpaths' _ _ @ concat_1p g^). }
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros e.
  refine (equiv_functor_forall' (equiv_inverse (equiv_path_universe X X)) _).
  intros g; simpl.
  refine (equiv_compose' (equiv_moveR_transport_V _ _ _ _) _).
  refine (equiv_compose' (equiv_path_inverse _ _) _).
  apply equiv_concat_l, transport2.
  symmetry; apply (eissect (equiv_path X X)).
Defined.

(** This implies that if [X] is a set, then the center of [BAut X] is the set of automorphisms of [X] that commute with every other automorphism (i.e. the center, in the usual sense, of the group of automorphisms of [X]). *)

Definition center_baut `{Univalence} X `{IsHSet X}
: { f : X <~> X & forall g:X<~>X, g o f == f o g }
  <~> (forall Z:BAut X, Z = Z).
Proof.
  refine (equiv_compose'
            (equiv_functor_forall'
               (P := fun Z => Z.1 = Z.1)
               (equiv_idmap (BAut X))
               (fun Z => equiv_path_sigma_hprop Z Z)) _).
  refine (equiv_compose' (baut_ind_hset X (fun Z => Z = Z)) _).
  simpl.
  refine (equiv_functor_sigma' (equiv_path_universe X X) _); intros f.
  refine (equiv_functor_forall' (equiv_idmap _) _); intros g; simpl.
  refine (equiv_compose' _ (equiv_path_arrow _ _)).
  refine (equiv_compose' _ (equiv_path_equiv (equiv_compose' g f) (equiv_compose' f g))).
  revert g. equiv_intro (equiv_path X X) g.
  revert f. equiv_intro (equiv_path X X) f.
  refine (equiv_compose' _ (equiv_concat_l (equiv_path_pp _ _) _)).
  refine (equiv_compose' _ (equiv_concat_r (equiv_path_pp _ _)^ _)).
  refine (equiv_compose' _ (equiv_inverse (equiv_ap (equiv_path X X) _ _))).
  refine (equiv_compose' (equiv_concat_l (transport_paths_lr _ _) _) _).
  refine (equiv_compose' (equiv_concat_l (concat_pp_p _ _ _) _) _).
  refine (equiv_compose' (equiv_moveR_Vp _ _ _) _).
  refine (equiv_compose' (equiv_concat_l _ _) (equiv_concat_r _ _)).
  - apply concat2; apply eissect.
  - symmetry; apply concat2; apply eissect.
Defined.

(** We show that this equivalence takes the identity equivalence to the identity in the center.  We have to be careful in this proof never to [simpl] or [unfold] too many things, or Coq will produce gigantic terms that take it forever to compute with. *)
Definition id_center_baut `{Univalence} X `{IsHSet X}
: center_baut X (existT
                   (fun (f:X<~>X) => forall (g:X<~>X), g o f == f o g)
                   (equiv_idmap X)
                   (fun (g:X<~>X) (x:X) => idpath (g x)))
  = fun Z => idpath Z.
Proof.
  apply path_forall; intros Z.
  assert (IsHSet (Z.1 = Z.1)) by exact _.
  baut_reduce.
  exact (ap (path_sigma_hprop _ _) path_universe_1
            @ path_sigma_hprop_1 _).
Defined.

(** Similarly, if [X] is a 1-type, we can characterize the 2-center of [BAut X]. *)

(** Coq is too eager about unfolding some things appearing in this proof. *)
Section Center2BAut.
  Local Arguments equiv_path_equiv : simpl never.
  Local Arguments equiv_path2_universe : simpl never.

  Definition center2_baut `{Univalence} X `{IsTrunc 1 X}
  : { f : forall x:X, x=x & forall (g:X<~>X) (x:X), ap g (f x) = f (g x) }
      <~> (forall Z:BAut X, (idpath Z) = (idpath Z)).
  Proof.
    refine (equiv_compose'
              (equiv_functor_forall'
                 (P := fun Z => idpath Z.1 = idpath Z.1)
                 (equiv_idmap (BAut X))
                 (fun Z => equiv_compose' (equiv_concat_lr _ _)
                             (equiv_ap (equiv_path_sigma_hprop Z Z)
                                       (idpath Z.1) (idpath Z.1)))) _).
    { symmetry; apply path_sigma_hprop_1. }
    { apply path_sigma_hprop_1. }
    assert (forall Z:BAut X, IsHSet (idpath Z.1 = idpath Z.1)) by exact _.
    refine (equiv_compose' (baut_ind_hset X (fun Z => idpath Z = idpath Z)) _).
    refine (equiv_functor_sigma' _ _).
    { refine (equiv_compose' _
                             (equiv_path2_universe (equiv_idmap X) (equiv_idmap X))).
      apply equiv_concat_lr.
      - symmetry; apply path_universe_1.
      - apply path_universe_1. }
    intros f.
    refine (equiv_functor_forall' (equiv_idmap _) _); intros g.
    refine (equiv_compose' _ (equiv_path3_universe _ _)).
    refine (equiv_compose' (dpath_paths2 (path_universe g) _ _) _).
    cbn.
    change (equiv_idmap X == equiv_idmap X) in f.
    refine (equiv_concat_lr _ _).
    - refine (_ @ (path2_universe_postcompose_idmap f g)^).
      abstract (rewrite !whiskerR_pp, !concat_pp_p; reflexivity).
    - refine (path2_universe_precompose_idmap f g @ _).
      abstract (rewrite !whiskerL_pp, !concat_pp_p; reflexivity).
  Defined.

  (** Once again we compute it on the identity.  In this case it seems to be unavoidable to do some [simpl]ing (or at least [cbn]ing), making this proof somewhat slower. *)
  Definition id_center2_baut `{Univalence} X `{IsTrunc 1 X}
  : center2_baut X (existT
                      (fun (f:forall x:X, x=x) =>
                         forall (g:X<~>X) (x:X), ap g (f x) = f (g x))
                      (fun x => idpath x)
                      (fun (g:X<~>X) (x:X) => idpath (idpath (g x))))
    = fun Z => idpath (idpath Z).
  Proof.
    apply path_forall; intros Z.
    assert (IsHSet (idpath Z.1 = idpath Z.1)) by exact _.
    baut_reduce.
    cbn. unfold functor_forall, sig_rect, merely_rec_hset. cbn.
    rewrite equiv_path2_universe_1.
    rewrite !concat_p1, !concat_Vp.
    simpl.
    rewrite !concat_p1, !concat_Vp.
    reflexivity.
  Defined.

End Center2BAut.
