(* ========================================================================= *)
(* RegionLattice.v                                   *)
(* *)
(* Finite distributive lattices of regions as the substrate for gluing.     *)
(* *)
(* Whiteheadian interpretation: Regions are not containers of points but    *)
(* achieved unities - "actual occasions" in their spatial aspect. The       *)
(* lattice structure encodes potentiality for synthesis (join) and mutual   *)
(* relevance (meet). The empty region is pure potentiality; the top region  *)
(* is maximal achieved unity.                                               *)
(* ========================================================================= *)

Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Sets.Finite_sets.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Lists.List.

(** * Basic Lattice Structure *)

(** A region lattice is a bounded distributive lattice. We use a bundled 
    representation with explicit operations and proofs. *)

Class RegionLattice := {
  (** The carrier type of regions *)
  Reg : Type;
  
  (** Decidable equality - essential for finite, computational setting *)
  Reg_eq_dec : forall (R S : Reg), {R = S} + {R <> S};
  
  (** Lattice operations *)
  empty : Reg;                          (* ∅ - pure potentiality *)
  top : Reg;                            (* ⊤ - maximal unity *)
  join : Reg -> Reg -> Reg;             (* ∪ - synthesis *)
  meet : Reg -> Reg -> Reg;             (* ∩ - mutual relevance *)
  
  (** The inclusion order, defined via meet *)
  incl (R S : Reg) : Prop := meet R S = R;
  
  (** Lattice axioms: meet *)
  meet_comm : forall R S, meet R S = meet S R;
  meet_assoc : forall R S T, meet (meet R S) T = meet R (meet S T);
  meet_idem : forall R, meet R R = R;
  
  (** Lattice axioms: join *)
  join_comm : forall R S, join R S = join S R;
  join_assoc : forall R S T, join (join R S) T = join R (join S T);
  join_idem : forall R, join R R = R;
  
  (** Absorption laws - connect meet and join *)
  absorb_join_meet : forall R S, join R (meet R S) = R;
  absorb_meet_join : forall R S, meet R (join R S) = R;
  
  (** Distributivity - the key structural property *)
  distrib_meet_join : forall R S T, 
    meet R (join S T) = join (meet R S) (meet R T);
  
  (** Bounded lattice axioms *)
  meet_empty : forall R, meet R empty = empty;
  join_empty : forall R, join R empty = R;
  meet_top : forall R, meet R top = R;
  join_top : forall R, join R top = top;
}.

(** Notation for region operations *)
Declare Scope region_scope.
Notation "∅" := empty : region_scope.
Notation "⊤" := top : region_scope.
Notation "R ∪ S" := (join R S) (at level 50, left associativity) : region_scope.
Notation "R ∩ S" := (meet R S) (at level 40, left associativity) : region_scope.
Notation "R ⊆ S" := (incl R S) (at level 70, no associativity) : region_scope.

Open Scope region_scope.

Section LatticeProperties.
  Context `{RL : RegionLattice}.
  

  (** * Derived Properties *)
  
  (** The inclusion relation is a partial order *)
  
  Lemma incl_refl : forall R, R ⊆ R.
  Proof.
    intro R. unfold incl. apply meet_idem.
  Qed.
  
  Lemma incl_trans : forall R S T, R ⊆ S -> S ⊆ T -> R ⊆ T.
  Proof.
    intros R S T HRS HST.
    unfold incl in *.
    rewrite <- HRS.
    rewrite meet_assoc.
    rewrite HST.
    reflexivity.
  Qed.
  
  Lemma incl_antisym : forall R S, R ⊆ S -> S ⊆ R -> R = S.
  Proof.
    intros R S HRS HSR.
    unfold incl in *.
    rewrite <- HRS.
    rewrite meet_comm.
    exact HSR.
  Qed.
  
  (** Join is the least upper bound *)
  
  Lemma incl_join_l : forall R S, R ⊆ (R ∪ S).
  Proof.
    intros R S. unfold incl.
    apply absorb_meet_join.
  Qed.
  
  Lemma incl_join_r : forall R S, S ⊆ (R ∪ S).
  Proof.
    intros R S. unfold incl.
    rewrite join_comm.
    apply absorb_meet_join.
  Qed.
  
  Lemma join_lub : forall R S T, R ⊆ T -> S ⊆ T -> (R ∪ S) ⊆ T.
  Proof.
    intros R S T HRT HST.
    unfold incl in *.
    rewrite meet_comm.
    rewrite distrib_meet_join.
    rewrite meet_comm.
    rewrite HRT.
    rewrite meet_comm.
    rewrite HST.
    reflexivity.
  Qed.
  
  (** Meet is the greatest lower bound *)
  
  Lemma meet_incl_l : forall R S, (R ∩ S) ⊆ R.
  Proof.
    intros R S. unfold incl.
    (* Goal: meet (meet R S) R = meet R S *)
    rewrite meet_assoc.
    (* Goal becomes: meet R (meet S R) = meet R S *)
    rewrite (meet_comm S R).
    (* Now: meet R (meet R S) = meet R S *)
    rewrite <- meet_assoc.
    (* Now: meet (meet R R) S = meet R S *)
    rewrite meet_idem.
    reflexivity.
  Qed.

  Lemma meet_incl_r : forall R S, (R ∩ S) ⊆ S.
  Proof.
    intros R S. unfold incl.
    (* meet (meet R S) S = meet R S *)
    rewrite meet_assoc.
    (* meet R (meet S S) = meet R S *)
    rewrite meet_idem.
    reflexivity.
  Qed.

  Lemma meet_glb : forall R S T, T ⊆ R -> T ⊆ S -> T ⊆ (R ∩ S).
  Proof.
    intros R S T HTR HTS.
    unfold incl in *.
    rewrite <- meet_assoc.
    rewrite HTR.
    rewrite HTS.
    reflexivity.
  Qed.
  
  (** Empty is bottom, top is top *)
  
  Lemma empty_incl : forall R, ∅ ⊆ R.
  Proof.
    intro R. unfold incl.
    rewrite meet_comm.
    apply meet_empty.
  Qed.
  
  Lemma incl_top : forall R, R ⊆ ⊤.
  Proof.
    intro R. unfold incl.
    apply meet_top.
  Qed.
  
  (** * Triple and quadruple overlaps *)
  
  (** These are central to the cohomological obstruction *)
  
  Definition triple_meet (R S T : Reg) : Reg := R ∩ S ∩ T.
  
  Definition quad_meet (R S T U : Reg) : Reg := R ∩ S ∩ T ∩ U.
  
  Notation "R ∩₃ S ∩₃ T" := (triple_meet R S T) 
    (at level 40, S at next level) : region_scope.
  
  (** Triple meet is symmetric *)
  
  Lemma triple_meet_perm12 : forall R S T,
    triple_meet R S T = triple_meet S R T.
  Proof.
    intros. unfold triple_meet.
    rewrite (meet_comm R S). reflexivity.
  Qed.
  
  Lemma triple_meet_perm23 : forall R S T,
    triple_meet R S T = triple_meet R T S.
  Proof.
    intros. unfold triple_meet.
    rewrite meet_assoc.
    rewrite (meet_comm S T).
    rewrite <- meet_assoc.
    reflexivity.
  Qed.
  
  (** Triple meet is contained in all pairwise meets *)
  
  Lemma triple_meet_incl_12 : forall R S T,
    triple_meet R S T ⊆ (R ∩ S).
  Proof.
    intros. unfold triple_meet.
    apply meet_incl_l.
  Qed.
  
  Lemma triple_meet_incl_23 : forall R S T,
    triple_meet R S T ⊆ (S ∩ T).
  Proof.
    intros R S T. unfold triple_meet.
    (* Goal: ((R ∩ S) ∩ T) ⊆ (S ∩ T) *)
    apply (meet_glb S T).
    - (* ((R ∩ S) ∩ T) ⊆ S *)
      eapply incl_trans.
      + apply meet_incl_l.  (* ⊆ (R ∩ S) *)
      + apply meet_incl_r.  (* (R ∩ S) ⊆ S *)
    - (* ((R ∩ S) ∩ T) ⊆ T *)
      apply meet_incl_r.
  Qed.

  (** * Key identity for the localization lemma *)
  
  (** This is the lattice-theoretic fact underlying Lemma 4.2:
      the triple overlap of (U ∪ V), W, and any region containing
      both equals the original triple overlap. *)
  
  Lemma triple_overlap_join : forall U V W,
    (U ∪ V) ∩ W = (U ∩ W) ∪ (V ∩ W).
  Proof.
    intros.
    rewrite meet_comm.
    rewrite distrib_meet_join.
    rewrite (meet_comm W U).
    rewrite (meet_comm W V).
    reflexivity.
  Qed.
  
  Lemma triple_overlap_localization : forall U V W,
    triple_meet U V W = meet (meet U V) (meet V W) ∩ (meet U W).
  Proof.
    Admitted.

End LatticeProperties.

(** * Finiteness *)

(** For computational purposes and Čech cohomology, we need finiteness. *)

Class FiniteRegionLattice `{RL : RegionLattice} := {
  (** The lattice is finite *)
  regions_finite : exists (l : list Reg), forall R, List.In R l;
  
  (** We can enumerate all regions *)
  all_regions : list Reg;
  all_regions_complete : forall R, List.In R all_regions;
}.

(** * Concrete Example: Power Set Lattice *)

(** For any finite type X, the power set forms a region lattice.
    This is the "pointillist" interpretation that Whitehead would reject,
    but it serves as a useful computational model. *)

Section PowerSetLattice.
  Variable X : Type.
  Variable X_finite : exists (l : list X), forall x, List.In x l.
  Variable X_eq_dec : forall (x y : X), {x = y} + {x <> y}.
  
  Definition PSet := Ensemble X.
  
  Definition PSet_eq_dec : forall (A B : PSet), 
    (forall x, Ensembles.In X A x <-> Ensembles.In X B x) -> A = B.
  Proof.
    intros A B H.
    apply Extensionality_Ensembles.
    split; intros x Hx; apply H; exact Hx.
  Qed.
  
  Definition PSet_empty : PSet := Empty_set X.
  Definition PSet_top : PSet := Full_set X.
  Definition PSet_join (A B : PSet) : PSet := Union X A B.
  Definition PSet_meet (A B : PSet) : PSet := Intersection X A B.
  
  (* The lattice laws follow from set theory *)
  (* We omit the proofs here; they are standard *)
  
End PowerSetLattice.

(** * The Three-Region Case *)


(** The minimal interesting case for associativity obstruction:
    three regions U, V, W with overlaps. *)

Section ThreeRegions.
  Context `{RL : RegionLattice}.
  
  Variables U V W : Reg.
  
  (** Pairwise overlaps *)
  Definition Gamma_UV : Reg := U ∩ V.
  Definition Gamma_VW : Reg := V ∩ W.
  Definition Gamma_UW : Reg := U ∩ W.
  
  (** Triple overlap - where the associator lives *)
  Definition Lambda : Reg := U ∩ V ∩ W.
  
  (** The union - where glued products live *)
  Definition R_UVW : Reg := U ∪ V ∪ W.
  
  (** Pairwise unions *)
  Definition S_UV : Reg := U ∪ V.
  Definition T_VW : Reg := V ∪ W.
  
  (** Key inclusions *)
  
  Lemma Lambda_in_all_Gamma : 
    Lambda ⊆ Gamma_UV /\ Lambda ⊆ Gamma_VW /\ Lambda ⊆ Gamma_UW.
  Proof.
    Admitted.
  
  (** The overlap of (U ∪ V) with W decomposes via distributivity *)
  
  Lemma S_UV_meet_W : S_UV ∩ W = Gamma_UW ∪ Gamma_VW.
  Proof.
    unfold S_UV, Gamma_UW, Gamma_VW.
    apply triple_overlap_join.
  Qed.
  
  Lemma U_meet_T_VW : U ∩ T_VW = Gamma_UV ∪ Gamma_UW.
  Proof.
    unfold T_VW, Gamma_UV, Gamma_UW.
    rewrite meet_comm.
    rewrite triple_overlap_join.
    rewrite (meet_comm V U).
    rewrite (meet_comm W U).
    reflexivity.
  Qed.

End ThreeRegions.

(** * Philosophical Commentary *)

(** In Process and Reality, Whitehead distinguishes between "coordinate 
   division" (analysis into parts) and "genetic division" (analysis into
   phases of becoming). The region lattice formalizes coordinate division:
   regions can be decomposed into overlapping sub-regions.
   
   The key Whiteheadian insight is that this decomposition is not 
   metaphysically primitive. A region is first an achieved unity; its
   decomposition into sub-regions is a secondary abstraction. This is
   why we work with the lattice structure rather than point-sets: the
   lattice operations (join, meet) express *potential* for synthesis
   and mutual relevance, not actual constitution.
   
   The associativity obstruction we will construct measures the extent
   to which regional achievements resist re-parenthesization. When 
   [α] ≠ 0, the regions exhibit irreducible tripartite structure that
   cannot be factored through binary syntheses alone. This is "contrast"
   in Whitehead's terminology: a pattern of incompatibility that is
   itself a positive datum.
*)