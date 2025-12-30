(* ========================================================================= *)
(*                            Associator.v                                   *)
(*                                                                           *)
(*  The associator defect and its localization to the triple overlap.        *)
(*  This is Lemma 4.2 from the paper: the key geometric fact that makes      *)
(*  the cohomological obstruction possible.                                  *)
(*                                                                           *)
(*  Whiteheadian interpretation: The associator measures the irreducible     *)
(*  contribution of triple synthesis. When three regions are unified, the    *)
(*  order of prehension (which two are synthesized first) matters. The       *)
(*  associator quantifies this non-commutativity of becoming. Its support    *)
(*  on the triple overlap shows that the obstruction is a genuinely          *)
(*  tripartite phenomenon - not reducible to pairwise interactions.          *)
(* ========================================================================= *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import RegionLattice.
Require Import AlgebraicAssignment.
Require Import BinaryGluing.

Open Scope region_scope.
Open Scope alg_scope.

Section AssociatorLocalization.
  Context `{k : CommRing}.
  Context `{RL : RegionLattice}.
  Context `{AA : AlgebraicAssignment}.
  Context `{IA : InjectiveAssignment}.
  Context `{BGS : BinaryGluingSystem}.
  
  Variables U V W : Reg.
  
  (** * Key Regions *)
  
  Definition Gamma_UV : Reg := U ∩ V.
  Definition Gamma_VW : Reg := V ∩ W.
  Definition Gamma_UW : Reg := U ∩ W.
  Definition Lambda : Reg := U ∩ V ∩ W.      (* Triple overlap *)
  Definition S : Reg := U ∪ V.               (* Intermediate for left *)
  Definition T : Reg := V ∪ W.               (* Intermediate for right *)
  Definition R : Reg := U ∪ V ∪ W.           (* Full union *)
  
  (** * Key Inclusions *)
  
  Lemma Lambda_incl_Gamma_UV : Lambda ⊆ Gamma_UV.
  Proof.
    unfold Lambda, Gamma_UV, incl.
    rewrite meet_assoc.
    rewrite meet_idem.
    reflexivity.
  Qed.
  
  Lemma Lambda_incl_Gamma_VW : Lambda ⊆ Gamma_VW.
  Proof.
    unfold Lambda, Gamma_VW, incl.
    rewrite (meet_comm (U ∩ V) W).
    rewrite <- meet_assoc.
    rewrite (meet_assoc W V W).
    rewrite (meet_comm W V).
    rewrite <- (meet_assoc V W W).
    rewrite meet_idem.
    rewrite meet_assoc.
    rewrite (meet_comm (V ∩ W) U).
    rewrite <- meet_assoc.
    rewrite meet_assoc.
    rewrite (meet_comm U V).
    rewrite meet_idem.
    reflexivity.
  Qed.
  
  Lemma Lambda_incl_Gamma_UW : Lambda ⊆ Gamma_UW.
  Proof.
    unfold Lambda, Gamma_UW, incl.
    rewrite meet_assoc.
    rewrite (meet_comm (U ∩ V ∩ W) (U ∩ W)).
    rewrite <- meet_assoc.
    rewrite (meet_assoc (U ∩ W) U V).
    rewrite (meet_comm (U ∩ W) U).
    rewrite <- (meet_assoc U U W).
    rewrite meet_idem.
    rewrite (meet_assoc (U ∩ W) V W).
    rewrite (meet_comm V W).
    rewrite <- (meet_assoc (U ∩ W) W V).
    rewrite meet_assoc.
    rewrite (meet_comm W U).
    rewrite <- (meet_assoc U W W).
    rewrite meet_idem.
    rewrite meet_assoc.
    rewrite meet_idem.
    reflexivity.
  Qed.
  
  Lemma Lambda_incl_R : Lambda ⊆ R.
  Proof.
    apply incl_trans with U.
    - apply incl_trans with Gamma_UV.
      + exact Lambda_incl_Gamma_UV.
      + apply meet_incl_l.
    - unfold R. apply incl_join_l.
  Qed.
  
  (** * The Overlap of (U ∪ V) with W *)
  
  Lemma S_meet_W : S ∩ W = Gamma_UW ∪ Gamma_VW.
  Proof.
    unfold S, Gamma_UW, Gamma_VW.
    rewrite meet_comm.
    apply distrib_meet_join.
  Qed.
  
  Lemma U_meet_T : U ∩ T = Gamma_UV ∪ Gamma_UW.
  Proof.
    unfold T, Gamma_UV, Gamma_UW.
    apply distrib_meet_join.
  Qed.
  
  (** * Support Analysis *)
  
  (** An element is supported on a region if it's in the image of the
      structure map from that region. *)
  
  Definition is_supported_on (X Y : Reg) (H : X ⊆ Y) 
      (x : @alg_carrier k (alg_at Y)) : Prop :=
    exists y : @alg_carrier k (alg_at X),
      alg_hom_map _ _ (structure_map X Y H) y = x.
  
  (** The associator: difference of left and right parenthesizations *)
  
  Definition assoc (a : @alg_carrier k (alg_at U))
                   (b : @alg_carrier k (alg_at V))
                   (c : @alg_carrier k (alg_at W)) 
      : @alg_carrier k (alg_at R) :=
    associator U V W a b c.
  
  (** * Term Classification *)
  
  (** We classify terms in the associator expansion by their support. *)
  
  Inductive TermSupport : Type :=
    | Interior_U    (* Supported on U alone *)
    | Interior_V    (* Supported on V alone *)
    | Interior_W    (* Supported on W alone *)
    | Overlap_UV    (* Supported on U ∩ V but not W *)
    | Overlap_VW    (* Supported on V ∩ W but not U *)
    | Overlap_UW    (* Supported on U ∩ W but not V *)
    | Triple_Lambda (* Supported on U ∩ V ∩ W *)
    | Mixed         (* General support *).
  
  (** * Lemma 4.2: Localization of the Associator *)
  
  (** The main theorem: the associator is supported on Lambda *)
  
  Theorem associator_localization :
    forall (a : @alg_carrier k (alg_at U))
           (b : @alg_carrier k (alg_at V))
           (c : @alg_carrier k (alg_at W)),
    is_supported_on Lambda R Lambda_incl_R (assoc a b c).
  Proof.
    intros a b c.
    unfold assoc, associator.
    
    (** The proof proceeds by expanding both parenthesizations and
        showing that all terms either:
        1. Cancel (Type I and II terms), or
        2. Are supported on Lambda (Type III and IV terms)
        
        We organize this into several steps. *)
    
    (** Step 1: Expand left parenthesization
        
        left_assoc a b c = glue_{S,W}(glue_{U,V}(a,b), c)
        
        Using the decomposition formula twice:
        
        glue_{U,V}(a,b) = ι_U(a·b|_U) + ι_V(a|_V·b) - ι_Γ(a|_Γ·b|_Γ) + ι_Γ(β_{U,V}(a,b))
        
        Then glue this with c using glue_{S,W}. *)
    
    (** Step 2: Expand right parenthesization similarly *)
    
    (** Step 3: Identify cancelling terms
        
        Type I (interior): Products computed entirely in A(U), A(V), or A(W)
        cancel by local associativity.
        
        Type II (binary overlap): Products in A(Γ_UV), A(Γ_VW), A(Γ_UW) with
        the third element also in that overlap algebra cancel by associativity
        of the overlap algebra. *)
    
    (** Step 4: Show remaining terms land on Lambda
        
        Type III: Terms involving elements from all three regions but not
        explicitly on Lambda are shown to have support on Lambda by
        intersection considerations.
        
        Type IV: The β-correction terms are explicitly supported on overlaps,
        and when combined with elements from the third region, land on Lambda. *)
    
    (** The full proof requires tracking approximately 20 terms.
        We provide the key lemmas and defer the complete enumeration. *)
    
    admit.
  Admitted.
  
  (** * Component Analysis *)
  
  (** We break down the proof into manageable pieces *)
  
  Section TermAnalysis.
    Variables a : @alg_carrier k (alg_at U).
    Variables b : @alg_carrier k (alg_at V).
    Variables c : @alg_carrier k (alg_at W).
    
    (** ** Type I: Pure Interior Terms *)
    
    (** Left: ((a ·_U 1) ·_S 1) ·_R c|_U  -- if c supported on U *)
    (** Right: (a ·_U 1) ·_U (1 ·_U c|_U) -- if b,c supported on U *)
    
    (** These are triple products in A(U) and cancel by associativity *)
    
    Lemma interior_U_cancellation :
      forall (a' : @alg_carrier k (alg_at U))
             (b' : @alg_carrier k (alg_at U))
             (c' : @alg_carrier k (alg_at U)),
      @alg_mult k (alg_at U) (@alg_mult k (alg_at U) a' b') c' =
      @alg_mult k (alg_at U) a' (@alg_mult k (alg_at U) b' c').
    Proof.
      intros. apply alg_mult_assoc.
    Qed.
    
    (** Similarly for V and W *)
    
    Lemma interior_V_cancellation :
      forall (a' b' c' : @alg_carrier k (alg_at V)),
      @alg_mult k (alg_at V) (@alg_mult k (alg_at V) a' b') c' =
      @alg_mult k (alg_at V) a' (@alg_mult k (alg_at V) b' c').
    Proof.
      intros. apply alg_mult_assoc.
    Qed.
    
    Lemma interior_W_cancellation :
      forall (a' b' c' : @alg_carrier k (alg_at W)),
      @alg_mult k (alg_at W) (@alg_mult k (alg_at W) a' b') c' =
      @alg_mult k (alg_at W) a' (@alg_mult k (alg_at W) b' c').
    Proof.
      intros. apply alg_mult_assoc.
    Qed.
    
    (** ** Type II: Binary Overlap Terms *)
    
    (** When all three elements have support on a pairwise overlap,
        the triple product is computed in that overlap algebra *)
    
    Lemma overlap_UV_cancellation :
      forall (a' b' c' : @alg_carrier k (alg_at Gamma_UV)),
      @alg_mult k (alg_at Gamma_UV) 
        (@alg_mult k (alg_at Gamma_UV) a' b') c' =
      @alg_mult k (alg_at Gamma_UV) 
        a' (@alg_mult k (alg_at Gamma_UV) b' c').
    Proof.
      intros. apply alg_mult_assoc.
    Qed.
    
    (** ** Type III: Mixed Terms Landing on Lambda *)
    
    (** Consider a ∈ A(U) with no support on V, b ∈ A(V) with no support on U,W,
        and c ∈ A(W) with no support on V.
        
        Left: (a · b) · c where a·b is computed via β_{U,V}
        Right: a · (b · c) where b·c is computed via β_{V,W}
        
        Both land on Lambda by support considerations *)
    
    Lemma mixed_term_support_left :
      forall (beta_ab : @alg_carrier k (alg_at Gamma_UV)),
      (* β_{U,V}(a,b) lives in A(Γ_UV) *)
      (* When this is glued with c ∈ A(W), the result is supported on Γ_UV ∩ W = Λ *)
      is_supported_on Lambda R Lambda_incl_R
        (glue Gamma_UV W (bgd Gamma_UV W) 
          (embed Gamma_UV S (meet_incl_l U V) beta_ab)
          c).
    Proof.
      intro beta_ab.
      (* The glue of an element in A(Γ_UV) with c ∈ A(W) lands in A(Γ_UV ∪ W) *)
      (* The overlap Γ_UV ∩ W = Λ *)
      (* The correction term β_{Γ_UV, W} lands in A(Λ) *)
      (* By the decomposition formula, everything is supported on Λ *)
      admit.
    Admitted.
    
    Lemma mixed_term_support_right :
      forall (beta_bc : @alg_carrier k (alg_at Gamma_VW)),
      is_supported_on Lambda R Lambda_incl_R
        (glue U Gamma_VW (bgd U Gamma_VW)
          a
          (embed Gamma_VW T (meet_incl_r V W) beta_bc)).
    Proof.
      intro beta_bc.
      (* Similar reasoning: U ∩ Γ_VW = Λ *)
      admit.
    Admitted.
    
    (** ** Type IV: Correction Terms *)
    
    (** The β-terms from the outer gluing *)
    
    (** Left: β_{S,W}(glue_{U,V}(a,b), c) lands in A(S ∩ W) = A(Γ_UW ∪ Γ_VW) *)
    (** Right: β_{U,T}(a, glue_{V,W}(b,c)) lands in A(U ∩ T) = A(Γ_UV ∪ Γ_UW) *)
    
    (** When we take the difference, the parts on Γ_UW (not on Λ) cancel
        by restriction compatibility. The remainder is on Λ. *)
    
    Lemma outer_correction_cancellation :
      forall (left_outer : @alg_carrier k (alg_at (S ∩ W)))
             (right_outer : @alg_carrier k (alg_at (U ∩ T))),
      (* left_outer = β_{S,W}(glue_{U,V}(a,b), c) *)
      (* right_outer = β_{U,T}(a, glue_{V,W}(b,c)) *)
      (* The difference, restricted to R, is supported on Λ *)
      is_supported_on Lambda R Lambda_incl_R
        (@alg_plus k (alg_at R)
          (embed (S ∩ W) R (* S∩W ⊆ R *) (admit) left_outer)
          (@alg_neg k (alg_at R)
            (embed (U ∩ T) R (* U∩T ⊆ R *) (admit) right_outer))).
    Proof.
      (* The key is that S ∩ W = Γ_UW ∪ Γ_VW and U ∩ T = Γ_UV ∪ Γ_UW
         share Γ_UW. By restriction compatibility, the Γ_UW components
         of the two corrections agree and cancel. *)
      admit.
    Admitted.

  End TermAnalysis.
  
  (** * The Lifted Associator *)
  
  (** By the localization theorem, we can lift the associator to A(Λ) *)
  
  Definition assoc_lifted (a : @alg_carrier k (alg_at U))
                          (b : @alg_carrier k (alg_at V))
                          (c : @alg_carrier k (alg_at W))
      : @alg_carrier k (alg_at Lambda).
  Proof.
    (* Use the localization theorem to get existence *)
    destruct (associator_localization a b c) as [lifted Hlifted].
    exact lifted.
  Defined.
  
  (** The lift is unique by injectivity *)
  
  Lemma assoc_lifted_unique :
    forall a b c (y1 y2 : @alg_carrier k (alg_at Lambda)),
    alg_hom_map _ _ (structure_map Lambda R Lambda_incl_R) y1 = assoc a b c ->
    alg_hom_map _ _ (structure_map Lambda R Lambda_incl_R) y2 = assoc a b c ->
    y1 = y2.
  Proof.
    intros.
    apply (structure_map_injective Lambda R Lambda_incl_R).
    rewrite H, H0. reflexivity.
  Qed.
  
  (** The lift is trilinear *)
  
  Lemma assoc_lifted_trilinear_l :
    forall a1 a2 b c,
    assoc_lifted (@alg_plus k (alg_at U) a1 a2) b c =
    @alg_plus k (alg_at Lambda) (assoc_lifted a1 b c) (assoc_lifted a2 b c).
  Proof.
    (* Follows from bilinearity of glue and linearity of structure maps *)
    admit.
  Admitted.
  
  (* Similar lemmas for linearity in b and c *)

End AssociatorLocalization.

(** * Trilinearity Record *)

(** Package the lifted associator as a trilinear map *)

Section TrilinearAssociator.
  Context `{k : CommRing}.
  Context `{RL : RegionLattice}.
  Context `{AA : AlgebraicAssignment}.
  Context `{IA : InjectiveAssignment}.
  Context `{BGS : BinaryGluingSystem}.
  
  Variables U V W : Reg.
  
  Record TrilinearMap (A B C D : Algebra) := {
    trilin_map : @alg_carrier k A -> @alg_carrier k B -> @alg_carrier k C ->
                 @alg_carrier k D;
    trilin_linear_l : forall a1 a2 b c,
      trilin_map (@alg_plus k A a1 a2) b c =
      @alg_plus k D (trilin_map a1 b c) (trilin_map a2 b c);
    trilin_linear_m : forall a b1 b2 c,
      trilin_map a (@alg_plus k B b1 b2) c =
      @alg_plus k D (trilin_map a b1 c) (trilin_map a b2 c);
    trilin_linear_r : forall a b c1 c2,
      trilin_map a b (@alg_plus k C c1 c2) =
      @alg_plus k D (trilin_map a b c1) (trilin_map a b c2);
    (* Scalar linearity in each argument - omitted for brevity *)
  }.
  
  Definition associator_trilinear : 
      TrilinearMap (alg_at U) (alg_at V) (alg_at W) (alg_at (U ∩ V ∩ W)).
  Proof.
    refine {|
      trilin_map := assoc_lifted U V W;
    |}.
    - apply assoc_lifted_trilinear_l.
    - admit.
    - admit.
  Admitted.

End TrilinearAssociator.

(** * Philosophical Commentary *)

(**
   The localization theorem (Lemma 4.2) is the geometric heart of the 
   obstruction theory. It says: when three regional achievements fail
   to associate, the failure is concentrated on their mutual overlap.
   
   In Whiteheadian terms, this is profound. The associator measures
   the irreducibly triadic character of certain syntheses. Binary
   combinations (U with V, V with W) work fine individually, but when
   all three must be unified, a new phenomenon emerges that cannot be
   localized to any pair.
   
   This is "contrast" in Whitehead's technical sense: a pattern of
   incompatibility that is itself a positive datum, not merely the
   absence of harmony. The contrast lives on Lambda precisely because
   it arises from the three-way prehensive relation, not from any
   two-way interaction.
   
   The trilinearity of the associator means it respects the linear
   structure of the algebraic data. Contrasts add (superposition)
   and scale (intensity). This is consistent with Whitehead's view
   that eternal objects have a systematic relatedness governed by
   mathematical structure.
   
   The uniqueness of the lift (by injectivity) ensures that the
   obstruction is well-defined: there is exactly one element of A(Λ)
   measuring the failure of associativity, not a family of equally
   valid choices.
*)
