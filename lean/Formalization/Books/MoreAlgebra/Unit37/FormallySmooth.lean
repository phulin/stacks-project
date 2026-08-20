import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.MoreAlgebra.Unit36.TopologicalRings
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.RingHom.Smooth

/-!
# More Algebra, Chapter 37: Formally smooth maps of topological rings

This file records the lifting definition and the formal-smoothness interfaces from the source
section.  The underlying ring-map predicate is kept separate from Mathlib's algebraic
`RingHom.FormallySmooth` predicate, while the adic and completion constructions use Mathlib's
canonical ideals, completions, and tensor products.
-/

namespace Formalization.Books.MoreAlgebra.Unit37

open scoped TensorProduct
open Formalization.Books.MoreAlgebra.Unit36

noncomputable section

universe u v w

/-! ## The lifting definition -/

/-- Formal smoothness of a continuous map between linearly topologized topological rings.

The square-zero test object is given the discrete topology, and the quotient is given the
quotient topology induced by its canonical projection.  Thus the two continuity hypotheses in
the quantified diagram are exactly the two topological-ring-map conditions in the source. -/
def FormallySmooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    (f : R →+* S) : Prop :=
  Continuous f ∧
    ∀ {A : Type (max u v)} [CommRing A] (J : Ideal A) (_hJ : J ^ 2 = ⊥),
      letI : TopologicalSpace A := ⊥
      letI : TopologicalSpace (A ⧸ J) :=
        Formalization.Books.Topology.Unit29.quotientRingTopology (Ideal.Quotient.mk J)
      ∀ (g : R →+* A) (ψ : S →+* A ⧸ J),
        Continuous g →
          Continuous ψ →
            ψ.comp f = (Ideal.Quotient.mk J).comp g →
              ∃ lift : S →+* A,
                Continuous lift ∧
                  (Ideal.Quotient.mk J).comp lift = ψ ∧ lift.comp f = g

/-! ## Adic shorthand and the topology-independence lemma -/

/-- Formal smoothness for the `m`-adic topology on the source and the `n`-adic topology on the
target. -/
def FormallySmoothForIdeals
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S) : Prop :=
  letI : TopologicalSpace R := IAdicRingTopology R m
  letI : NonarchimedeanRing R := m.nonarchimedean
  letI : IsLinearTopology R R := m.isLinearTopology
  letI : TopologicalSpace S := IAdicRingTopology S n
  letI : NonarchimedeanRing S := n.nonarchimedean
  letI : IsLinearTopology S S := n.isLinearTopology
  FormallySmooth f

/-- The source's shorthand: the topology on the source is discrete and only the target ideal is
recorded in the name of the property. -/
def FormallySmoothForIdeal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (n : Ideal S) : Prop :=
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  letI : IsLinearTopology R R := by infer_instance
  letI : TopologicalSpace S := IAdicRingTopology S n
  letI : NonarchimedeanRing S := n.nonarchimedean
  letI : IsLinearTopology S S := n.isLinearTopology
  FormallySmooth f

/-- Algebraic formal smoothness implies topological formal smoothness for every compatible
linear/pre-adic choice of topologies. -/
private noncomputable def formallySmooth_of_ringHom_formallySmooth_aux
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    (f : R →+* S) (hf : RingHom.FormallySmooth f)
    (hcont : Continuous f)
    (hS : IsPreAdicTopologicalRing S) :
    { _h : FormallySmooth f // True } := by
  let _ : Algebra R S := f.toAlgebra
  exact ⟨by
    constructor
    · exact hcont
    · intro A _ J hJ
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := discreteTopology_bot A
      let : TopologicalSpace (A ⧸ J) :=
        Formalization.Books.Topology.Unit29.quotientRingTopology (Ideal.Quotient.mk J)
      have hqopen : IsOpen ({0} : Set (A ⧸ J)) := by
        rw [isOpen_coinduced]
        exact isOpen_discrete _
      intro g ψ hg hψ hcomm
      obtain ⟨I, hI, hIbasis⟩ := hS
      have hψ0 : ψ ⁻¹' ({0} : Set (A ⧸ J)) ∈ nhds (0 : S) :=
        hψ.continuousAt.preimage_mem_nhds (hqopen.mem_nhds (by simp))
      obtain ⟨k, hk, hkI⟩ := hIbasis.mem_iff.mp hψ0
      let : Algebra R A := g.toAlgebra
      let ψa : S →ₐ[R] A ⧸ J :=
        { ψ with
          commutes' := fun r => by
            change ψ (f r) = Ideal.Quotient.mk J (g r)
            exact DFunLike.congr_fun hcomm r }
      let : Algebra.FormallySmooth R S := hf.toAlgebra
      obtain ⟨lift, hlift⟩ :=
        Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψa
      have hJmap : ∀ x ∈ I ^ k, lift x ∈ J := by
        intro x hx
        have hx0 : ψ x = 0 := by
          have := hkI hx
          simpa only [Set.mem_preimage, Set.mem_singleton_iff] using this
        have heq := DFunLike.congr_fun hlift x
        have hmk : Ideal.Quotient.mk J (lift x) = ψ x := by
          simpa [ψa] using heq
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        rw [hmk, hx0]
      have hker : I ^ (k + k) ≤ RingHom.ker lift := by
        rw [pow_add, Ideal.mul_le]
        intro x hx y hy
        rw [RingHom.mem_ker, map_mul]
        have hxy : lift x * lift y ∈ J ^ 2 :=
          by simpa [pow_two] using Ideal.mul_mem_mul (hJmap x hx) (hJmap y hy)
        rw [hJ] at hxy
        exact hxy
      refine ⟨lift.toRingHom, ?_, ?_, ?_⟩
      · apply continuous_of_continuousAt_zero lift
        rw [continuousAt_def]
        simp only [map_zero]
        rw [nhds_discrete A]
        change Filter.Tendsto lift (nhds (0 : S)) (pure (0 : A))
        rw [Filter.tendsto_pure]
        filter_upwards [hIbasis.mem_iff.mpr ⟨k + k, trivial, subset_rfl⟩] with x hx
        exact RingHom.mem_ker.mp (hker hx)
      · exact congrArg AlgHom.toRingHom hlift
      · apply RingHom.ext
        intro r
        change lift (algebraMap R S r) = algebraMap R A r
        exact lift.commutes r, trivial⟩

theorem formallySmooth_of_ringHom_formallySmooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    (f : R →+* S) (hf : RingHom.FormallySmooth f)
    (hcont : Continuous f)
    (hS : IsPreAdicTopologicalRing S) :
    FormallySmooth f :=
  (formallySmooth_of_ringHom_formallySmooth_aux f hf hcont hS).1

private noncomputable def continuous_of_square_zero_quotient_aux
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (m : Ideal R) (J : Ideal A) (hJ : J ^ 2 = ⊥) (g : R →+* A)
    (hquot : @Continuous R (A ⧸ J)
      (IAdicRingTopology R m)
      (@Formalization.Books.Topology.Unit29.quotientRingTopology A (A ⧸ J)
        _ _ (⊥ : TopologicalSpace A) (Ideal.Quotient.mk J))
      ((Ideal.Quotient.mk J).comp g)) :
    { _h : @Continuous R A (IAdicRingTopology R m) (⊥ : TopologicalSpace A) g // True } := by
  letI : TopologicalSpace R := IAdicRingTopology R m
  letI : NonarchimedeanRing R := m.nonarchimedean
  letI : IsLinearTopology R R := m.isLinearTopology
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : TopologicalSpace (A ⧸ J) :=
    Formalization.Books.Topology.Unit29.quotientRingTopology (Ideal.Quotient.mk J)
  refine ⟨?_, trivial⟩
  have hqopen : IsOpen ({0} : Set (A ⧸ J)) := by
    rw [isOpen_coinduced]
    exact isOpen_discrete _
  have hzero : ((Ideal.Quotient.mk J).comp g) ⁻¹' ({0} : Set (A ⧸ J)) ∈
      nhds (0 : R) :=
    hquot.continuousAt.preimage_mem_nhds (hqopen.mem_nhds (by simp))
  obtain ⟨k, hk, hkI⟩ := (iAdicRingTopology_hasBasis R m).mem_iff.mp hzero
  have hJmap : ∀ x ∈ m ^ k, g x ∈ J := by
    intro x hx
    have hx0 : Ideal.Quotient.mk J (g x) = 0 := by
      have := hkI hx
      change Ideal.Quotient.mk J (g x) = 0 at this
      exact this
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hx0
  have hker : m ^ (k + k) ≤ RingHom.ker g := by
    rw [pow_add, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker, map_mul]
    have hxy : g x * g y ∈ J ^ 2 :=
      by simpa [pow_two] using Ideal.mul_mem_mul (hJmap x hx) (hJmap y hy)
    rw [hJ] at hxy
    exact hxy
  apply continuous_of_continuousAt_zero g
  rw [continuousAt_def]
  simp only [map_zero]
  rw [nhds_discrete A]
  change Filter.Tendsto g (nhds (0 : R)) (pure (0 : A))
  rw [Filter.tendsto_pure]
  filter_upwards [(iAdicRingTopology_hasBasis R m).mem_iff.mpr
    ⟨k + k, trivial, subset_rfl⟩] with x hx
  exact RingHom.mem_ker.mp (hker hx)

private theorem continuous_of_square_zero_quotient
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (m : Ideal R) (J : Ideal A) (hJ : J ^ 2 = ⊥) (g : R →+* A)
    (hquot : @Continuous R (A ⧸ J)
      (IAdicRingTopology R m)
      (@Formalization.Books.Topology.Unit29.quotientRingTopology A (A ⧸ J)
        _ _ (⊥ : TopologicalSpace A) (Ideal.Quotient.mk J))
      ((Ideal.Quotient.mk J).comp g)) :
    @Continuous R A (IAdicRingTopology R m) (⊥ : TopologicalSpace A) g :=
  (continuous_of_square_zero_quotient_aux m J hJ g hquot).1

/-- For adic topologies, changing the source topology to the discrete topology does not change
formal smoothness. -/
private noncomputable def formallySmooth_iff_discrete_source_aux
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    { _h : FormallySmoothForIdeals f m n ↔ FormallySmoothForIdeal f n // True } := by
  refine ⟨?_, trivial⟩
  unfold FormallySmoothForIdeals FormallySmoothForIdeal
  constructor
  · intro h
    let : TopologicalSpace R := IAdicRingTopology R m
    let : NonarchimedeanRing R := m.nonarchimedean
    let : IsLinearTopology R R := m.isLinearTopology
    let : TopologicalSpace S := IAdicRingTopology S n
    let : NonarchimedeanRing S := n.nonarchimedean
    let : IsLinearTopology S S := n.isLinearTopology
    refine ⟨?_, ?_⟩
    · let : TopologicalSpace R := ⊥
      let : DiscreteTopology R := discreteTopology_bot R
      exact continuous_of_discreteTopology
    · intro A _ J hJ g ψ hg hψ hcomm
      have hquot : @Continuous R (A ⧸ J)
          (IAdicRingTopology R m)
          (@Formalization.Books.Topology.Unit29.quotientRingTopology A (A ⧸ J)
            _ _ (⊥ : TopologicalSpace A) (Ideal.Quotient.mk J))
          ((Ideal.Quotient.mk J).comp g) := by
        rw [← hcomm]
        exact @Continuous.comp R S (A ⧸ J)
          (IAdicRingTopology R m)
          (IAdicRingTopology S n)
          (@Formalization.Books.Topology.Unit29.quotientRingTopology A (A ⧸ J)
            _ _ (⊥ : TopologicalSpace A) (Ideal.Quotient.mk J))
          f ψ hψ hcont
      have hg' := continuous_of_square_zero_quotient m J hJ g hquot
      exact h.2 J hJ g ψ hg' hψ hcomm
  · intro h
    let : TopologicalSpace R := ⊥
    let : DiscreteTopology R := discreteTopology_bot R
    let : IsLinearTopology R R := by infer_instance
    let : TopologicalSpace S := IAdicRingTopology S n
    let : NonarchimedeanRing S := n.nonarchimedean
    let : IsLinearTopology S S := n.isLinearTopology
    refine ⟨hcont, ?_⟩
    intro A _ J hJ g ψ hg hψ hcomm
    have hg' : @Continuous R A (⊥ : TopologicalSpace R) (⊥ : TopologicalSpace A) g := by
      let : TopologicalSpace R := ⊥
      let : DiscreteTopology R := discreteTopology_bot R
      exact @continuous_of_discreteTopology R (⊥ : TopologicalSpace R)
        (discreteTopology_bot R) A (⊥ : TopologicalSpace A) g
    exact h.2 J hJ g ψ hg' hψ hcomm

theorem formallySmooth_iff_discrete_source
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    FormallySmoothForIdeals f m n ↔ FormallySmoothForIdeal f n :=
  (formallySmooth_iff_discrete_source_aux f m n hcont).1

/-- The source's notation for formal smoothness in the `n`-adic topology. -/
theorem formallySmoothForIdeal_iff_formallySmoothForIdeals
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    FormallySmoothForIdeal f n ↔ FormallySmoothForIdeals f m n := by
  exact (formallySmooth_iff_discrete_source f m n hcont).symm

/-! ## Completions -/

/-- The extension of an ideal to its adic completion. -/
noncomputable def adicCompletionIdeal
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal (AdicCompletion I R) :=
  I.map (algebraMap R (AdicCompletion I R))

private theorem adicCompletion_factorPow_eval
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsTwoSided]
    {i j : ℕ} (hij : i ≤ j) (x : AdicCompletion m R) :
    Ideal.Quotient.factorPow m hij (AdicCompletion.evalₐ m j x) =
      AdicCompletion.evalₐ m i x := by
  let hj : (m ^ j • (⊤ : Submodule R R)) ≤ m ^ j :=
    le_of_eq (Ideal.mul_top _)
  let hi : (m ^ i • (⊤ : Submodule R R)) ≤ m ^ i :=
    le_of_eq (Ideal.mul_top _)
  have hfac : ∀ (y : R ⧸ (m ^ j • (⊤ : Submodule R R))),
      Ideal.Quotient.factorPow m hij (Submodule.factor hj y) =
        Submodule.factor hi (AdicCompletion.transitionMap m R hij y) := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ r => rfl
  rw [← AdicCompletion.factor_eval_eq_evalₐ m x hj]
  rw [← AdicCompletion.factor_eval_eq_evalₐ m x hi]
  rw [hfac]
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply]
  apply congrArg (fun z => (Submodule.factor hi) z)
  exact x.2 hij

/-- A completed ring map induced by a continuous map of finitely generated adic rings.

The existence theorem below is the completion universal property needed to choose the canonical
map.  The choice is exposed as a definition so later statements can use the completed map rather
than carrying an existential witness. -/
private noncomputable def exists_adicCompletionMap_aux
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (_hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    { _h : ∃ fhat : AdicCompletion m R →+* AdicCompletion n S,
        fhat.comp (algebraMap R (AdicCompletion m R)) =
          (algebraMap S (AdicCompletion n S)).comp f // True } := by
  refine ⟨?_, trivial⟩
  have hpower : ∀ k : ℕ, ∃ l : ℕ, m ^ l ≤ Ideal.comap f (n ^ k) := by
    intro k
    have hnk : ((n ^ k : Ideal S) : Set S) ∈
        @nhds S (IAdicRingTopology S n) 0 :=
      (iAdicRingTopology_hasBasis S n).mem_iff.mpr ⟨k, trivial, subset_rfl⟩
    have hpre : f ⁻¹' ((n ^ k : Ideal S) : Set S) ∈
        @nhds R (IAdicRingTopology R m) 0 :=
      @ContinuousAt.preimage_mem_nhds R S (IAdicRingTopology R m)
        (IAdicRingTopology S n) f 0 ((n ^ k : Ideal S) : Set S)
        (@Continuous.continuousAt R S (IAdicRingTopology R m)
          (IAdicRingTopology S n) f 0 hcont) (by
            simpa only [map_zero] using hnk)
    obtain ⟨l, -, hl⟩ :=
      (iAdicRingTopology_hasBasis R m).mem_iff.mp hpre
    refine ⟨l, ?_⟩
    intro x hx
    change f x ∈ n ^ k
    exact hl hx
  let c : ℕ → ℕ := fun k => Classical.choose (hpower k)
  have hc : ∀ k : ℕ, m ^ c k ≤ Ideal.comap f (n ^ k) := fun k =>
    Classical.choose_spec (hpower k)
  let l : ℕ → ℕ := fun k => Nat.rec (c 0) (fun i r => max (c (i + 1)) r) k
  have hcl : ∀ k : ℕ, c k ≤ l k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        simp [l, le_max_left (c (k + 1)) (l k)]
  have hlstep : ∀ k : ℕ, l k ≤ l (k + 1) := by
    intro k
    simp [l, le_max_right (c (k + 1)) (l k)]
  have hlmono : Monotone l := monotone_nat_of_le_succ hlstep
  have hll : ∀ k : ℕ, m ^ l k ≤ Ideal.comap f (n ^ k) := by
    intro k
    exact le_trans (Ideal.pow_le_pow_right (hcl k)) (hc k)
  have htwo : ∀ k : ℕ, (m ^ l k).IsTwoSided := by
    intro k
    exact ⟨fun b hb => by simpa [mul_comm] using (m ^ l k).mul_mem_left b hb⟩
  have hm : m.IsTwoSided := by
    exact ⟨fun b hb => by simpa [mul_comm] using m.mul_mem_left b hb⟩
  let qmap : ∀ k : ℕ, (R ⧸ m ^ l k) →+* (S ⧸ n ^ k) := fun k =>
    by
      letI : (m ^ l k).IsTwoSided := htwo k
      exact Ideal.Quotient.lift (m ^ l k) ((Ideal.Quotient.mk (n ^ k)).comp f) (by
        intro x hx
        change Ideal.Quotient.mk (n ^ k) (f x) = 0
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr ((hll k) hx))
  let F : ∀ k : ℕ, AdicCompletion m R →+* S ⧸ n ^ k := fun k =>
    (qmap k).comp (AdicCompletion.evalₐ m (l k)).toRingHom
  have hF : ∀ {i j : ℕ} (hij : i ≤ j),
      (Ideal.Quotient.factorPow n hij).comp (F j) = F i := by
    intro i j hij
    have hli : l i ≤ l j := hlmono hij
    have hquot :
        (Ideal.Quotient.factorPow n hij).comp (qmap j) =
          (qmap i).comp (Ideal.Quotient.factorPow m hli) := by
      apply RingHom.ext
      intro x
      obtain ⟨r, hr⟩ := @Ideal.Quotient.mk_surjective R _ (m ^ l j) (htwo j) x
      rw [← hr]
      simp [qmap]
    ext x
    change (Ideal.Quotient.factorPow n hij)
        (qmap j (AdicCompletion.evalₐ m (l j) x)) =
      qmap i (AdicCompletion.evalₐ m (l i) x)
    have heval := @adicCompletion_factorPow_eval R _ m hm (l i) (l j) hli x
    rw [← heval]
    exact DFunLike.congr_fun hquot (AdicCompletion.evalₐ m (l j) x)
  have hN : ∀ k : ℕ, n ^ k ≤ Ideal.comap (algebraMap S (AdicCompletion n S))
      (adicCompletionIdeal n ^ k) := by
    intro k x hx
    change algebraMap S (AdicCompletion n S) x ∈ adicCompletionIdeal n ^ k
    rw [show adicCompletionIdeal n ^ k =
        (n ^ k).map (algebraMap S (AdicCompletion n S)) by
      simp [adicCompletionIdeal, Ideal.map_pow]]
    exact Ideal.mem_map_of_mem _ hx
  let tmap : ∀ k : ℕ, (S ⧸ n ^ k) →+*
      (AdicCompletion n S ⧸ adicCompletionIdeal n ^ k) := fun k =>
    by
      apply Ideal.Quotient.lift (n ^ k)
        ((Ideal.Quotient.mk (adicCompletionIdeal n ^ k)).comp
          (algebraMap S (AdicCompletion n S)))
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr ((hN k) hx)
  have htmap : ∀ {i j : ℕ} (hij : i ≤ j),
      (Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (tmap j) =
        (tmap i).comp (Ideal.Quotient.factorPow n hij) := by
    intro i j hij
    apply RingHom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := n ^ j) x
    change Ideal.Quotient.mk (adicCompletionIdeal n ^ i)
        (algebraMap S (AdicCompletion n S) s) =
      Ideal.Quotient.mk (adicCompletionIdeal n ^ i)
        (algebraMap S (AdicCompletion n S) s)
    rfl
  let FT : ∀ k : ℕ, AdicCompletion m R →+*
      (AdicCompletion n S ⧸ adicCompletionIdeal n ^ k) := fun k =>
    (tmap k).comp (F k)
  have hFT : ∀ {i j : ℕ} (hij : i ≤ j),
      (Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (FT j) = FT i := by
    intro i j hij
    calc
      (Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (FT j) =
          ((Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (tmap j)).comp
            (F j) := by rfl
      _ = ((tmap i).comp (Ideal.Quotient.factorPow n hij)).comp (F j) := by
        rw [htmap hij]
      _ = (tmap i).comp ((Ideal.Quotient.factorPow n hij).comp (F j)) := by
        rw [RingHom.comp_assoc]
      _ = (tmap i).comp (F i) := by rw [hF hij]
      _ = FT i := by rfl
  let hcomplete : IsAdicComplete (adicCompletionIdeal n) (AdicCompletion n S) := by
    exact (IsAdicComplete.map_algebraMap_iff n
      (AdicCompletion n S)).mpr (AdicCompletion.isAdicComplete hn)
  let fhat : AdicCompletion m R →+* AdicCompletion n S :=
    @IsAdicComplete.liftRingHom (AdicCompletion m R) (AdicCompletion n S) _ _
      (adicCompletionIdeal n) hcomplete FT hFT
  let G : ∀ k : ℕ, R →+*
      (AdicCompletion n S ⧸ adicCompletionIdeal n ^ k) := fun k =>
    (tmap k).comp ((Ideal.Quotient.mk (n ^ k)).comp f)
  have hG : ∀ {i j : ℕ} (hij : i ≤ j),
      (Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (G j) = G i := by
    intro i j hij
    calc
      (Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (G j) =
          ((Ideal.Quotient.factorPow (adicCompletionIdeal n) hij).comp (tmap j)).comp
            ((Ideal.Quotient.mk (n ^ j)).comp f) := by rfl
      _ = ((tmap i).comp (Ideal.Quotient.factorPow n hij)).comp
            ((Ideal.Quotient.mk (n ^ j)).comp f) := by rw [htmap hij]
      _ = (tmap i).comp ((Ideal.Quotient.factorPow n hij).comp
            ((Ideal.Quotient.mk (n ^ j)).comp f)) := by rw [RingHom.comp_assoc]
      _ = (tmap i).comp ((Ideal.Quotient.mk (n ^ i)).comp f) := by
        have hmk :
            (Ideal.Quotient.factorPow n hij).comp ((Ideal.Quotient.mk (n ^ j)).comp f) =
              (Ideal.Quotient.mk (n ^ i)).comp f := by
          apply RingHom.ext
          intro x
          simp
        rw [hmk]
      _ = G i := by rfl
  have hfg : ∀ k : ℕ,
      (Ideal.Quotient.mk (adicCompletionIdeal n ^ k)).comp
          (fhat.comp (algebraMap R (AdicCompletion m R))) = G k := by
    intro k
    rw [← RingHom.comp_assoc,
      @IsAdicComplete.mk_comp_liftRingHom (AdicCompletion m R) (AdicCompletion n S) _ _
        (adicCompletionIdeal n) hcomplete FT hFT k]
    ext x
    simp [FT, F, G, tmap, qmap]
  have hfg' : ∀ k : ℕ,
      (Ideal.Quotient.mk (adicCompletionIdeal n ^ k)).comp
          ((algebraMap S (AdicCompletion n S)).comp f) = G k := by
    intro k
    ext x
    simp [G, tmap]
  refine ⟨fhat, ?_⟩
  have h₁ : fhat.comp (algebraMap R (AdicCompletion m R)) =
      @IsAdicComplete.liftRingHom R (AdicCompletion n S) _ _
        (adicCompletionIdeal n) hcomplete G hG :=
    @IsAdicComplete.eq_liftRingHom R (AdicCompletion n S) _ _
      (adicCompletionIdeal n) hcomplete G hG
      (fhat.comp (algebraMap R (AdicCompletion m R))) hfg
  have h₂ : (algebraMap S (AdicCompletion n S)).comp f =
      @IsAdicComplete.liftRingHom R (AdicCompletion n S) _ _
        (adicCompletionIdeal n) hcomplete G hG :=
    @IsAdicComplete.eq_liftRingHom R (AdicCompletion n S) _ _
      (adicCompletionIdeal n) hcomplete G hG
      ((algebraMap S (AdicCompletion n S)).comp f) hfg'
  exact h₁.trans h₂.symm

theorem exists_adicCompletionMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    ∃ fhat : AdicCompletion m R →+* AdicCompletion n S,
      fhat.comp (algebraMap R (AdicCompletion m R)) =
        (algebraMap S (AdicCompletion n S)).comp f :=
  (exists_adicCompletionMap_aux m n f hm hn hcont).1

noncomputable def adicCompletionMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    AdicCompletion m R →+* AdicCompletion n S :=
  Classical.choose (exists_adicCompletionMap m n f hm hn hcont)

theorem adicCompletionMap_comp_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    (adicCompletionMap m n f hm hn hcont).comp
        (algebraMap R (AdicCompletion m R)) =
      (algebraMap S (AdicCompletion n S)).comp f := by
  exact Classical.choose_spec (exists_adicCompletionMap m n f hm hn hcont)

/-- Formal smoothness is unchanged by passing to either adic completion.  The three entries are,
respectively, the original map, the map into the target completion, and the map between both
completions. -/
theorem formallySmooth_completion_tfae
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    List.TFAE
      [ FormallySmoothForIdeal f n,
        FormallySmoothForIdeal
          ((algebraMap S (AdicCompletion n S)).comp f)
          (adicCompletionIdeal n),
        FormallySmoothForIdeal
          (adicCompletionMap m n f hm hn hcont)
          (adicCompletionIdeal n) ] := by
  sorry

/-! ## The stronger lifting property for adic targets -/

/-- The quotient used in the compatible two-index system in the proof of continuous lifting. -/
abbrev adicLiftingQuotient
    {A : Type u} [CommRing A] (J I : Ideal A) (n m : ℕ) : Type u :=
  A ⧸ (J ^ n ⊔ I ^ m)

/-- The canonical transition map between two quotients in the two-index system. -/
def adicLiftingQuotientMap
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {K L : Ideal A} (h : K ≤ L) : (A ⧸ K) →ₐ[R] (A ⧸ L) :=
  Ideal.Quotient.factorₐ R h

/-- The transition that lowers the `J`-exponent in the two-index quotient system. -/
def adicLiftingQuotient_stepJ
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
      adicLiftingQuotient J I n (m + 1) :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl)

/-- The transition that lowers the `I`-exponent in the two-index quotient system. -/
def adicLiftingQuotient_stepI
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
      adicLiftingQuotient J I (n + 1) m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- The `J`-transition in the lower-right square of the two-index system. -/
def adicLiftingQuotient_JTransition
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) m →ₐ[R] adicLiftingQuotient J I n m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl)

/-- The `I`-transition in the lower-left square of the two-index system. -/
def adicLiftingQuotient_ITransition
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I n (m + 1) →ₐ[R] adicLiftingQuotient J I n m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- The quotient-system assertion used in the proof of continuous lifting: for square-zero `J`
and positive indices, each elementary square has a surjective map to its fibre product with
square-zero kernel. -/
theorem exists_adicLiftingQuotient_square_zero
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (hJ : J ^ 2 = ⊥) (n m : ℕ) (hn : 1 ≤ n) (_hm : 1 ≤ m) :
    ∃ q : adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
        AlgHom.pullback
          (adicLiftingQuotient_ITransition (R := R) J I n m)
          (adicLiftingQuotient_JTransition (R := R) J I n m),
      Function.Surjective q ∧
        (RingHom.ker q.toRingHom) ^ 2 = ⊥ ∧
        (AlgHom.pullbackFst
            (adicLiftingQuotient_ITransition (R := R) J I n m)
            (adicLiftingQuotient_JTransition (R := R) J I n m)).comp q =
          adicLiftingQuotient_stepJ (R := R) J I n m ∧
        (AlgHom.pullbackSnd
            (adicLiftingQuotient_ITransition (R := R) J I n m)
            (adicLiftingQuotient_JTransition (R := R) J I n m)).comp q =
          adicLiftingQuotient_stepI (R := R) J I n m := by
  let K : Ideal A := J ^ (n + 1) ⊔ I ^ (m + 1)
  let L : Ideal A := J ^ n ⊔ I ^ (m + 1)
  let M : Ideal A := J ^ (n + 1) ⊔ I ^ m
  let C : Ideal A := J ^ n ⊔ I ^ m
  have hKL : K ≤ L := by
    exact sup_le_sup (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl
  have hKM : K ≤ M := by
    exact sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ m))
  have hJnL : J ^ n ≤ L := by
    exact le_sup_left
  have hImM : I ^ m ≤ M := by
    exact le_sup_right
  have hJn : J ^ n ≤ J := by
    simpa only [pow_one] using (Ideal.pow_le_pow_right (I := J) hn)
  have hLsq : L ^ 2 ≤ K := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    obtain ⟨aJ, haJ, aI, haI, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨bJ, hbJ, bI, hbI, rfl⟩ := Submodule.mem_sup.mp hb
    change (aJ + aI) * (bJ + bI) ∈ J ^ (n + 1) ⊔ I ^ (m + 1)
    simp only [add_mul, mul_add]
    apply Ideal.add_mem
    · apply Ideal.add_mem
      · have hzero : aJ * bJ = 0 := by
          have hmem : aJ * bJ ∈ J ^ 2 :=
            by
              simpa only [pow_two] using
                (Ideal.mul_mem_mul (I := J) (J := J) (hJn haJ) (hJn hbJ))
          rw [hJ] at hmem
          exact hmem
        rw [hzero]
        exact Ideal.zero_mem _
      · exact Ideal.mem_sup_right ((I ^ (m + 1)).mul_mem_right bJ haI)
    · apply Ideal.add_mem
      · exact Ideal.mem_sup_right ((I ^ (m + 1)).mul_mem_left aJ hbI)
      · exact Ideal.mem_sup_right ((I ^ (m + 1)).mul_mem_left aI hbI)
  let p : A →ₐ[R] (A ⧸ L) × (A ⧸ M) :=
    (Ideal.Quotient.mkₐ R L).prod (Ideal.Quotient.mkₐ R M)
  have hp : ∀ a : A, p a ∈ AlgHom.pullback
      (adicLiftingQuotient_ITransition (R := R) J I n m)
      (adicLiftingQuotient_JTransition (R := R) J I n m) := by
    intro a
    change adicLiftingQuotient_ITransition (R := R) J I n m (Ideal.Quotient.mk L a) =
      adicLiftingQuotient_JTransition (R := R) J I n m (Ideal.Quotient.mk M a)
    simp only [adicLiftingQuotient_ITransition, adicLiftingQuotient_JTransition,
      adicLiftingQuotientMap]
    change Ideal.Quotient.mk C a = Ideal.Quotient.mk C a
    rfl
  let q₀ : A →ₐ[R] AlgHom.pullback
      (adicLiftingQuotient_ITransition (R := R) J I n m)
      (adicLiftingQuotient_JTransition (R := R) J I n m) :=
    { toRingHom := p.toRingHom.codRestrict _ hp
      commutes' := by
        intro r
        apply Subtype.ext
        change p (algebraMap R A r) = _
        apply Prod.ext
        · change Ideal.Quotient.mk L (algebraMap R A r) =
            Ideal.Quotient.mk L (algebraMap R A r)
          rfl
        · change Ideal.Quotient.mk M (algebraMap R A r) =
            Ideal.Quotient.mk M (algebraMap R A r)
          rfl }
  have hq₀K : ∀ a : A, a ∈ K → q₀ a = 0 := by
    intro a ha
    apply Subtype.ext
    apply Prod.ext
    · apply (Ideal.Quotient.eq_zero_iff_mem).mpr
      exact hKL ha
    · apply (Ideal.Quotient.eq_zero_iff_mem).mpr
      exact hKM ha
  let q : A ⧸ K →ₐ[R] AlgHom.pullback
      (adicLiftingQuotient_ITransition (R := R) J I n m)
      (adicLiftingQuotient_JTransition (R := R) J I n m) :=
    Ideal.Quotient.liftₐ K q₀ hq₀K
  have hqcomp : q.comp (Ideal.Quotient.mkₐ R K) = q₀ := by
    exact Ideal.Quotient.liftₐ_comp K q₀ hq₀K
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := L) z.1.1
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := M) z.1.2
    have hab : Ideal.Quotient.mk C a = Ideal.Quotient.mk C b := by
      have hab' := z.prop
      change adicLiftingQuotient_ITransition (R := R) J I n m z.1.1 =
        adicLiftingQuotient_JTransition (R := R) J I n m z.1.2 at hab'
      rw [← ha, ← hb] at hab'
      change Ideal.Quotient.mk C a = Ideal.Quotient.mk C b at hab'
      exact hab'
    have habmem : a - b ∈ C :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := C) a b).mp hab
    obtain ⟨c, hcJ, hcI, hcab⟩ := (Submodule.mem_sup.mp habmem)
    refine ⟨Ideal.Quotient.mk K (a - c), ?_⟩
    apply Subtype.ext
    have hqval : q (Ideal.Quotient.mk K (a - c)) = q₀ (a - c) := by
      change (q.comp (Ideal.Quotient.mkₐ R K)) (a - c) = q₀ (a - c)
      exact DFunLike.congr_fun hqcomp (a - c)
    rw [hqval]
    apply Prod.ext
    · change Ideal.Quotient.mk L (a - c) = z.1.1
      rw [← ha]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := L) _ _).mpr
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        L.neg_mem (hJnL hcJ)
    · change Ideal.Quotient.mk M (a - c) = z.1.2
      rw [← hb]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := M) _ _).mpr
      have hsub : (a - c) - b = hcI := by
        calc
          (a - c) - b = a - b - c := by abel
          _ = hcI := by rw [← hcab.2]; abel
      rw [hsub]
      exact hImM hcab.1
  · apply le_antisymm
    · rw [pow_two, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := K) x
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := K) y
      rw [← ha] at hx
      rw [← hb] at hy
      have hxa : q₀ a = 0 := by
        have hx' := RingHom.mem_ker.mp hx
        have hqxa : q (Ideal.Quotient.mk K a) = q₀ a := by
          change (q.comp (Ideal.Quotient.mkₐ R K)) a = q₀ a
          exact DFunLike.congr_fun hqcomp a
        change q (Ideal.Quotient.mk K a) = 0 at hx'
        rw [hqxa] at hx'
        exact hx'
      have hya : q₀ b = 0 := by
        have hy' := RingHom.mem_ker.mp hy
        have hqyb : q (Ideal.Quotient.mk K b) = q₀ b := by
          change (q.comp (Ideal.Quotient.mkₐ R K)) b = q₀ b
          exact DFunLike.congr_fun hqcomp b
        change q (Ideal.Quotient.mk K b) = 0 at hy'
        rw [hqyb] at hy'
        exact hy'
      have haL : a ∈ L := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        exact congrArg (fun z => z.1) (Subtype.ext_iff.mp hxa)
      have haM : a ∈ M := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        exact congrArg (fun z => z.2) (Subtype.ext_iff.mp hxa)
      have hbL : b ∈ L := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        exact congrArg (fun z => z.1) (Subtype.ext_iff.mp hya)
      have hbM : b ∈ M := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        exact congrArg (fun z => z.2) (Subtype.ext_iff.mp hya)
      rw [← ha, ← hb]
      have habmem : a * b ∈ K := hLsq (by
        simpa only [pow_two] using
          (Ideal.mul_mem_mul (I := L) (J := L) haL hbL))
      have hmk : Ideal.Quotient.mk K (a * b) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr habmem
      simpa only [map_mul, Submodule.mem_bot] using hmk
    · exact bot_le
  · apply AlgHom.ext
    intro a
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := K) a
    rw [← hb]
    change (AlgHom.pullbackFst
        (adicLiftingQuotient_ITransition (R := R) J I n m)
        (adicLiftingQuotient_JTransition (R := R) J I n m))
        (q (Ideal.Quotient.mk K b)) =
      adicLiftingQuotient_stepJ (R := R) J I n m
        (Ideal.Quotient.mk K b)
    have hqval : q (Ideal.Quotient.mk K b) = q₀ b := by
      change (q.comp (Ideal.Quotient.mkₐ R K)) b = q₀ b
      rw [hqcomp]
    rw [hqval]
    rfl
  · apply AlgHom.ext
    intro a
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := K) a
    rw [← hb]
    change (AlgHom.pullbackSnd
        (adicLiftingQuotient_ITransition (R := R) J I n m)
        (adicLiftingQuotient_JTransition (R := R) J I n m))
        (q (Ideal.Quotient.mk K b)) =
      adicLiftingQuotient_stepI (R := R) J I n m
        (Ideal.Quotient.mk K b)
    have hqval : q (Ideal.Quotient.mk K b) = q₀ b := by
      change (q.comp (Ideal.Quotient.mkₐ R K)) b = q₀ b
      rw [hqcomp]
    rw [hqval]
    rfl

/-- A continuous lifting statement for an adic target and a closed quotient ideal. -/
theorem exists_continuous_lift
    {R : Type u} {S : Type v} {A : Type (max u v)} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (n : Ideal S) (hf : FormallySmoothForIdeal f n)
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsAdicTopologicalRing A)
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (hJclosed : IsClosed (J : Set A))
    (hJpower : ∃ (I : Ideal A) (t : ℕ),
      IsIdealOfDefinition A I ∧ 1 ≤ t ∧ J ^ t ≤ I)
    (g : R →+* A)
    (hg : @Continuous R A (⊥ : TopologicalSpace R) inferInstance g)
    (ψ : S →+* A ⧸ J)
    (hψ : @Continuous S (A ⧸ J)
      (IAdicRingTopology S n)
      (Formalization.Books.Topology.Unit29.quotientRingTopology
        (Ideal.Quotient.mk J)) ψ)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk J).comp g) :
    ∃ lift : S →+* A,
      @Continuous S A (IAdicRingTopology S n) inferInstance lift ∧
        (Ideal.Quotient.mk J).comp lift = ψ ∧ lift.comp f = g := by
  sorry

/-! ## Permanence properties -/

/-- Enlarging the target ideal preserves formal smoothness in the adic shorthand. -/
theorem formallySmoothForIdeal_of_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) {n n' : Ideal S} (hnn' : n ≤ n') :
    FormallySmoothForIdeal f n → FormallySmoothForIdeal f n' := by
  intro hf
  unfold FormallySmoothForIdeal at hf ⊢
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := discreteTopology_bot R
  let : IsLinearTopology R R := by infer_instance
  let : TopologicalSpace S := IAdicRingTopology S n'
  let : NonarchimedeanRing S := n'.nonarchimedean
  let : IsLinearTopology S S := n'.isLinearTopology
  refine ⟨continuous_of_discreteTopology, ?_⟩
  intro A _ J hJ g ψ hg hψ hcomm
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : TopologicalSpace (A ⧸ J) :=
    Formalization.Books.Topology.Unit29.quotientRingTopology (Ideal.Quotient.mk J)
  have hdisc : Formalization.Books.Topology.Unit29.quotientRingTopology
      (Ideal.Quotient.mk J) = (⊥ : TopologicalSpace (A ⧸ J)) := by
    apply le_antisymm
    · exact bot_le
    · intro s hs
      exact @isOpen_discrete (A ⧸ J) (⊥ : TopologicalSpace (A ⧸ J))
        (discreteTopology_bot (A ⧸ J)) s
  let : DiscreteTopology (A ⧸ J) := ⟨hdisc⟩
  let : IsTopologicalRing A := by infer_instance
  let : IsTopologicalRing (A ⧸ J) := by
    apply Formalization.Books.Topology.Unit29.topologicalRing_surjective_quotient
    exact Ideal.Quotient.mk_surjective
  have hqopen : IsOpen ({0} : Set (A ⧸ J)) := by
    rw [isOpen_coinduced]
    exact isOpen_discrete _
  have hzero : ψ ⁻¹' ({0} : Set (A ⧸ J)) ∈ nhds (0 : S) :=
    hψ.continuousAt.preimage_mem_nhds (hqopen.mem_nhds (by simp))
  obtain ⟨k, -, hkpow⟩ :=
    (iAdicRingTopology_hasBasis S n').mem_iff.mp hzero
  have hpow_all : ∀ k : ℕ, n ^ k ≤ n' ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ, Ideal.mul_le]
        intro x hx y hy
        exact Ideal.mul_mem_mul (ih hx) (hnn' hy)
  have hpow := hpow_all k
  have hzero' : ψ ⁻¹' ({0} : Set (A ⧸ J)) ∈
      @nhds S (IAdicRingTopology S n) 0 :=
    (iAdicRingTopology_hasBasis S n).mem_iff.mpr ⟨k, trivial, fun x hx =>
      hkpow (hpow hx)⟩
  have hψ' : @Continuous S (A ⧸ J)
      (IAdicRingTopology S n) _ ψ := by
    let : TopologicalSpace S := IAdicRingTopology S n
    let : IsTopologicalRing S := by infer_instance
    apply continuous_of_continuousAt_zero ψ
    rw [continuousAt_def]
    simp only [map_zero]
    rw [nhds_discrete (A ⧸ J)]
    change Filter.Tendsto ψ (nhds (0 : S)) (pure (0 : A ⧸ J))
    rw [Filter.tendsto_pure]
    filter_upwards [hzero'] with x hx
    exact hx
  obtain ⟨lift, hlift, hliftψ, hliftg⟩ :=
    hf.2 J hJ g ψ hg hψ' hcomm
  refine ⟨lift, ?_, hliftψ, hliftg⟩
  have hquot : @Continuous S (A ⧸ J)
      (IAdicRingTopology S n') _ ((Ideal.Quotient.mk J).comp lift) := by
    rw [hliftψ]
    exact hψ
  exact continuous_of_square_zero_quotient n' J hJ lift hquot

/-- Composition of formally smooth continuous maps of linearly topologized rings is formally
smooth. -/
theorem formallySmooth_comp
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsTopologicalRing T]
    [IsLinearTopology R R] [IsLinearTopology S S] [IsLinearTopology T T]
    (f : R →+* S) (g : S →+* T)
    (hf : FormallySmooth f) (hg : FormallySmooth g) :
    FormallySmooth (g.comp f) := by
  sorry

/-- The target ideal after tensor-product base change. -/
noncomputable def baseChangeIdeal
    {R : Type u} {S : Type v} {R' : Type w} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Ideal (S ⊗[R] R') := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  exact n.map (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)

/-- Formal smoothness in the target-ideal shorthand is preserved by arbitrary base change. -/
theorem formallySmooth_baseChange
    {R : Type u} {S : Type v} {R' : Type w} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S)
    (hf : FormallySmoothForIdeal f n) :
    FormallySmoothForIdeal
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (baseChangeIdeal f g n) := by
  sorry

/-! ## Descent along a split base change -/

/-- The ring map `R → R'` is a module retraction: `R` is a direct summand of `R'` as an
`R`-module.  The complementary summand is only an `R`-module; it is not asserted to be an ideal
of `R'`. -/
def IsModuleRetract
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] (g : R →+* R') : Prop :=
  letI : Algebra R R' := g.toAlgebra
  ∃ r : R' →ₗ[R] R,
    r.comp (Algebra.linearMap R R') = LinearMap.id

/-- Formal smoothness descends from a split tensor-product base change. -/
theorem formallySmooth_of_moduleRetract
    {R : Type u} {S : Type v} {R' : Type w} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S)
    (hRetract : IsModuleRetract g)
    (hf : FormallySmoothForIdeal
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (baseChangeIdeal f g n)) :
    FormallySmoothForIdeal f n := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit37
