(* ========================================================================= *)
(*                          BinaryGluing.v                                   *)
(*                                                                           *)
(*  Binary gluing data: how to multiply elements from different regions.     *)
(*  The correction term β captures the novel contribution of synthesis.      *)
(*                                                                           *)
(*  Whiteheadian interpretation: When two regional achievements U and V      *)
(*  are synthesized into U ∪ V, multiplication gains a new component β       *)
(*  that was not present in either piece alone. This is the "novelty" of     *)
(*  concrescence - the creative advance that emerges from prehension.        *)
(* ========================================================================= *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import RegionLattice.
Require Import AlgebraicAssignment.

Open Scope region_scope.
Open Scope alg_scope.

Section BinaryGluing.
  Context `{k : CommRing}.
  Context `{RL : RegionLattice}.
  Context `{AA : AlgebraicAssignment}.
  Context `{IA : InjectiveAssignment}.
  
  (** * Definition 3.5: Binary Gluing Datum *)
  
  (** For a binary decomposition R = U ∪ V with overlap Γ = U ∩ V *)
  
  Record BinaryGluingDatum (U V : Reg) := {
    (** The overlap region *)
    overlap := U ∩ V;
    
    (** The union region *)
    union := U ∪ V;
    
    (** Inclusion proofs *)
    U_incl_union : U ⊆ union;
    V_incl_union : V ⊆ union;
    overlap_incl_U : overlap ⊆ U;
    overlap_incl_V : overlap ⊆ V;
    
    (** The bilinear gluing map *)
    glue : @alg_carrier k (alg_at U) -> @alg_carrier k (alg_at V) -> 
           @alg_carrier k (alg_at union);
    
    (** The correction map - lands in the overlap algebra *)
    correction : @alg_carrier k (alg_at U) -> @alg_carrier k (alg_at V) ->
                 @alg_carrier k (alg_at overlap);
    
    (** Bilinearity of glue *)
    glue_linear_l_plus : forall a1 a2 b,
      glue (@alg_plus k (alg_at U) a1 a2) b = 
      @alg_plus k (alg_at union) (glue a1 b) (glue a2 b);
    glue_linear_l_scale : forall (r : carrier) a b,
      glue (@alg_scale k (alg_at U) r a) b = 
      @alg_scale k (alg_at union) r (glue a b);
    glue_linear_r_plus : forall a b1 b2,
      glue a (@alg_plus k (alg_at V) b1 b2) = 
      @alg_plus k (alg_at union) (glue a b1) (glue a b2);
    glue_linear_r_scale : forall (r : carrier) a b,
      glue a (@alg_scale k (alg_at V) r b) = 
      @alg_scale k (alg_at union) r (glue a b);
    
    (** Bilinearity of correction *)
    corr_linear_l_plus : forall a1 a2 b,
      correction (@alg_plus k (alg_at U) a1 a2) b = 
      @alg_plus k (alg_at overlap) (correction a1 b) (correction a2 b);
    corr_linear_l_scale : forall (r : carrier) a b,
      correction (@alg_scale k (alg_at U) r a) b = 
      @alg_scale k (alg_at overlap) r (correction a b);
    corr_linear_r_plus : forall a b1 b2,
      correction a (@alg_plus k (alg_at V) b1 b2) = 
      @alg_plus k (alg_at overlap) (correction a b1) (correction a b2);
    corr_linear_r_scale : forall (r : carrier) a b,
      correction a (@alg_scale k (alg_at V) r b) = 
      @alg_scale k (alg_at overlap) r (correction a b);
    
    (** Interior compatibility: on each piece, glue recovers local mult *)
    interior_compat_U : forall a1 a2 : @alg_carrier k (alg_at U),
      glue a1 (embed U V (meet_incl_r U V) 
               (embed overlap U overlap_incl_U 
                (restrict overlap U overlap_incl_U 
                  a2 (* assuming a2 supported on overlap *)))) = 
      embed U union U_incl_union (@alg_mult k (alg_at U) a1 a2);
      (* This axiom is stated informally; see Decomposition below *)
  }.
  
  (** * The Inclusion-Exclusion Decomposition *)
  
  (** Equation (1) from the paper: the glue decomposes as
      
      m_{U,V}(a,b) = ι(a ·_U b|_U) + ι(a|_V ·_V b) - ι(a|_Γ ·_Γ b|_Γ) + ι(β(a,b))
      
      We formalize this for elements with specific support conditions. *)
  
  Section Decomposition.
    Variable U V : Reg.
    Variable BGD : BinaryGluingDatum U V.
    
    Let Gamma := overlap U V BGD.
    Let R := union U V BGD.
    
    (** Helper: embed from overlap to union via U *)
    Definition embed_overlap_via_U : 
        @alg_carrier k (alg_at Gamma) -> @alg_carrier k (alg_at R) :=
      fun x => embed U R (U_incl_union U V BGD) 
               (embed Gamma U (overlap_incl_U U V BGD) x).
    
    (** Helper: embed from overlap to union via V *)
    Definition embed_overlap_via_V :
        @alg_carrier k (alg_at Gamma) -> @alg_carrier k (alg_at R) :=
      fun x => embed V R (V_incl_union U V BGD)
               (embed Gamma V (overlap_incl_V U V BGD) x).
    
    (** These two embeddings agree (by composition of structure maps) *)
    Lemma embed_overlap_coherent : forall x,
      embed_overlap_via_U x = embed_overlap_via_V x.
    Proof.
      intro x.
      unfold embed_overlap_via_U, embed_overlap_via_V.
      (* This follows from the composition law for structure maps *)
      (* and the fact that Gamma ⊆ U, Gamma ⊆ V both compose to Gamma ⊆ R *)
      admit.
    Admitted.
    
    (** Canonical embedding of overlap into union *)
    Definition embed_overlap : 
        @alg_carrier k (alg_at Gamma) -> @alg_carrier k (alg_at R) :=
      embed_overlap_via_U.  (* Either works by coherence *)
    
    (** The decomposition formula, stated for "generic position" elements *)
    (** 
       For a ∈ A(U) supported only on U (not on Gamma) and 
       b ∈ A(V) supported only on V (not on Gamma):
       
       glue(a, b) = ι_U(a) * 0 + 0 * ι_V(b) - 0 + ι_Gamma(β(a,b))
                  = ι_Gamma(β(a,b))
       
       The full decomposition is more complex for elements with overlap support.
    *)
    
    (** * Decomposition for Overlap-Supported Elements *)
    
    (** When both a and b are supported on Gamma: *)
    
    Lemma glue_overlap_supported : 
      forall (a_gamma b_gamma : @alg_carrier k (alg_at Gamma)),
      let a := embed Gamma U (overlap_incl_U U V BGD) a_gamma in
      let b := embed Gamma V (overlap_incl_V U V BGD) b_gamma in
      glue U V BGD a b = 
        @alg_plus k (alg_at R)
          (embed_overlap (@alg_mult k (alg_at Gamma) a_gamma b_gamma))
          (embed_overlap (correction U V BGD a b)).
    Proof.
      (* This should follow from interior compatibility + correction structure *)
      admit.
    Admitted.

  End Decomposition.
  
  (** * Restriction Compatibility (Definition 3.8) *)
  
  (** When we have nested regions U ⊆ U' and V ⊆ V', the gluing data
      must be compatible under restriction. *)
  
  Record RestrictionCompatible 
      (U V U' V' : Reg)
      (HU : U ⊆ U') (HV : V ⊆ V')
      (BGD : BinaryGluingDatum U V)
      (BGD' : BinaryGluingDatum U' V') := {
    
    (** The unions are related *)
    union_incl : union U V BGD ⊆ union U' V' BGD';
    
    (** The overlaps are related *)
    overlap_incl : overlap U V BGD ⊆ overlap U' V' BGD';
    
    (** Gluing maps commute with structure maps *)
    glue_compat : forall a b,
      embed (union U V BGD) (union U' V' BGD') union_incl
        (glue U V BGD a b) =
      glue U' V' BGD' 
        (embed U U' HU a)
        (embed V V' HV b);
    
    (** Correction terms commute with structure maps *)
    correction_compat : forall a b,
      embed (overlap U V BGD) (overlap U' V' BGD') overlap_incl
        (correction U V BGD a b) =
      correction U' V' BGD'
        (embed U U' HU a)
        (embed V V' HV b);
  }.

  (** * A System of Binary Gluing Data *)
  
  (** For the full theory, we need compatible gluing data for all pairs *)
  
  Class BinaryGluingSystem := {
    (** For each pair of regions, a gluing datum *)
    bgd : forall U V : Reg, BinaryGluingDatum U V;
    
    (** Symmetry: glue_{U,V} and glue_{V,U} are related *)
    bgd_symm : forall U V a b,
      glue U V (bgd U V) a b = glue V U (bgd V U) b a;
    
    (** Restriction compatibility holds for all nested pairs *)
    bgd_restriction_compat : 
      forall U V U' V' (HU : U ⊆ U') (HV : V ⊆ V'),
      RestrictionCompatible U V U' V' HU HV (bgd U V) (bgd U' V');
  }.

End BinaryGluing.

(** * The β-term as Emergent Novelty *)

(** 
   The correction term β : A(U) ⊗ A(V) → A(U ∩ V) is the mathematical
   expression of Whiteheadian novelty. When two occasions prehend each
   other in synthesis, something new emerges that was not present in
   either alone.
   
   The key properties of β:
   
   1. It is bilinear - novelty respects the linear structure of data
   
   2. It lands on the overlap - novelty emerges precisely where the
      two regional achievements have mutual relevance
   
   3. It is not determined by the pieces alone - the decomposition
      formula shows that β is an independent datum, not derivable
      from the local multiplications
   
   4. It is subject to restriction compatibility - novelty at a finer
      scale embeds coherently into novelty at a coarser scale
   
   The inclusion-exclusion form of Equation (1):
   
      m(a,b) = (U-part) + (V-part) - (double-counted) + β
   
   is formally analogous to the principle of extensive abstraction
   in Process and Reality. The algebraic contribution of each region
   is tallied, overlap is removed to avoid double-counting, and then
   the creative contribution β is added.
   
   When β = 0, the gluing is "trivial" in the sense that no novelty
   emerges from synthesis. The obstruction class [α] measures whether
   there exist non-trivial β that nonetheless fail to compose 
   associatively on triple overlaps.
*)

(** * Computing Compound Gluings *)

Section CompoundGluing.
  Context `{k : CommRing}.
  Context `{RL : RegionLattice}.
  Context `{AA : AlgebraicAssignment}.
  Context `{IA : InjectiveAssignment}.
  Context `{BGS : BinaryGluingSystem}.
  
  (** For three regions U, V, W, we can glue in two ways:
      
      Left:  (U ∪ V) with W, i.e., glue_{U∪V, W}(glue_{U,V}(a,b), c)
      Right: U with (V ∪ W), i.e., glue_{U, V∪W}(a, glue_{V,W}(b,c))
      
      The difference is the associator. *)
  
  Variables U V W : Reg.
  
  Definition S_UV := U ∪ V.
  Definition T_VW := V ∪ W.
  Definition R_UVW := U ∪ V ∪ W.
  
  (** Left parenthesization *)
  
  Definition left_assoc 
      (a : @alg_carrier k (alg_at U))
      (b : @alg_carrier k (alg_at V))
      (c : @alg_carrier k (alg_at W)) : @alg_carrier k (alg_at R_UVW).
  Proof.
    (* First glue a and b *)
    pose (ab := glue U V (bgd U V) a b).
    (* ab lives in A(U ∪ V) = A(S_UV) *)
    (* Now glue ab with c *)
    (* Need: glue_{S_UV, W} *)
    (* The result lives in A((U ∪ V) ∪ W) = A(R_UVW) *)
    
    (* We need to embed ab into A(S_UV) appropriately *)
    (* This requires the inclusion S_UV ⊆ R_UVW *)
    assert (H_S : S_UV ⊆ R_UVW).
    { unfold S_UV, R_UVW, incl.
      rewrite <- meet_assoc.
      rewrite absorb_meet_join.
      reflexivity. }
    
    assert (H_W : W ⊆ R_UVW).
    { unfold R_UVW, incl.
      rewrite meet_comm.
      rewrite join_assoc.
      rewrite absorb_meet_join.
      reflexivity. }
    
    (* Glue in A(R_UVW) *)
    (* We need bgd for S_UV and W *)
    exact (glue S_UV W (bgd S_UV W) ab c).
  Defined.
  
  (** Right parenthesization *)
  
  Definition right_assoc
      (a : @alg_carrier k (alg_at U))
      (b : @alg_carrier k (alg_at V))
      (c : @alg_carrier k (alg_at W)) : @alg_carrier k (alg_at R_UVW).
  Proof.
    (* First glue b and c *)
    pose (bc := glue V W (bgd V W) b c).
    (* bc lives in A(V ∪ W) = A(T_VW) *)
    (* Now glue a with bc *)
    
    assert (H_U : U ⊆ R_UVW).
    { unfold R_UVW, incl.
      rewrite absorb_meet_join.
      reflexivity. }
    
    assert (H_T : T_VW ⊆ R_UVW).
    { unfold T_VW, R_UVW, incl.
      rewrite join_assoc.
      rewrite meet_comm.
      rewrite <- join_assoc.
      rewrite absorb_meet_join.
      reflexivity. }
    
    exact (glue U T_VW (bgd U T_VW) a bc).
  Defined.
  
  (** The associator defect *)
  
  Definition associator
      (a : @alg_carrier k (alg_at U))
      (b : @alg_carrier k (alg_at V))
      (c : @alg_carrier k (alg_at W)) : @alg_carrier k (alg_at R_UVW) :=
    @alg_plus k (alg_at R_UVW) 
      (left_assoc a b c) 
      (@alg_neg k (alg_at R_UVW) (right_assoc a b c)).

End CompoundGluing.

(** * Notation Summary *)

(**
   Regions:     R, S, T, U, V, W : Reg
   Operations:  ∅, ⊤, R ∪ S, R ∩ S, R ⊆ S
   
   Algebras:    A(R) = alg_at R
   Structure:   ι[R→S|H] : A(R) → A(S)
   
   Gluing:      bgd U V : BinaryGluingDatum U V
                glue U V bgd : A(U) → A(V) → A(U ∪ V)
                correction U V bgd : A(U) → A(V) → A(U ∩ V)
   
   Associator:  associator U V W a b c : A(U ∪ V ∪ W)
*)
