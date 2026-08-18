import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Connected.Basic

/-!
# Exercises, Chapter 6: Specialization and connected components

The source's closed-point, specialization/generalization, connectedness, and
connected-component notions are expressed with Mathlib's canonical topology
predicates and the prime-spectrum order API.
-/

noncomputable section

universe u

open Set Topology TopologicalSpace

namespace Formalization.Books.Exercises.Unit06

/-! ## Closed points and specialization -/

/-- A point is closed exactly when its singleton is closed. -/
theorem closed_point_iff_closed_singleton {X : Type u} [TopologicalSpace X] (x : X) :
    closure ({x} : Set X) = {x} ↔ IsClosed ({x} : Set X) := by
  constructor
  · intro h
    rw [← h]
    exact isClosed_closure
  · intro h
    exact h.closure_eq

/-- Closed points of an affine spectrum correspond to maximal ideals. -/
theorem spectrum_closed_point_iff_maximal {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    IsClosed ({p} : Set (PrimeSpectrum A)) ↔ p.asIdeal.IsMaximal := by
  exact PrimeSpectrum.isClosed_singleton_iff_isMaximal p

/-- In the spectrum, specialization/generalization is inclusion of prime
ideals.  The displayed relation is oriented as `p` generalizing `q`. -/
theorem spectrum_generalization_iff_ideal_inclusion {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) :
    p ⤳ q ↔ p.asIdeal ≤ q.asIdeal := by
  exact (PrimeSpectrum.le_iff_specializes p q).symm

/-- A prime is closed exactly when it has no proper specialization. -/
theorem spectrum_closed_point_iff_no_proper_specialization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    IsClosed ({p} : Set (PrimeSpectrum A)) ↔
      ∀ q : PrimeSpectrum A, p ⤳ q → q = p := by
  exact ⟨
    fun hp q hq =>
      Set.mem_singleton_iff.mp (hp.closure_eq ▸ (specializes_iff_mem_closure.mp hq)),
    fun h =>
      (closed_point_iff_closed_singleton p).mp
        (Set.Subset.antisymm
          (fun q hq =>
            Set.mem_singleton_iff.mpr (h q (specializes_iff_mem_closure.mpr hq)))
          subset_closure)⟩

/-- Maximal ideals are the primes with no proper specialization. -/
theorem spectrum_maximal_iff_no_proper_specialization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal.IsMaximal ↔
      ∀ q : PrimeSpectrum A, p ⤳ q → q = p := by
  exact (spectrum_closed_point_iff_maximal p).symm.trans
    (spectrum_closed_point_iff_no_proper_specialization p)

/-- Minimal primes are exactly the points with no proper generalization. -/
theorem spectrum_minimal_prime_iff_no_proper_generalization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal ∈ minimalPrimes A ↔
      ∀ q : PrimeSpectrum A, q ⤳ p → q = p := by
  exact ⟨
    fun hp q hq =>
      Set.mem_singleton_iff.mp
        ((PrimeSpectrum.stableUnderGeneralization_singleton (R := A) (x := p)).mpr hp
          hq (Set.mem_singleton p)),
    fun h =>
      (PrimeSpectrum.stableUnderGeneralization_singleton (R := A) (x := p)).mp (by
        intro x y hyx hx
        have hx' : x = p := Set.mem_singleton_iff.mp hx
        subst x
        exact Set.mem_singleton_iff.mpr (h y hyx))⟩

/-- A generic point of a reducible spectrum is a generic point of one of its
irreducible components, exactly at a minimal prime. -/
theorem spectrum_generic_point_iff_minimal_prime {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) :
    p.asIdeal ∈ minimalPrimes A ↔
      ∃ C : Set (PrimeSpectrum A),
        C ∈ irreducibleComponents (PrimeSpectrum A) ∧
          IsGenericPoint p C := by
  constructor
  · intro hp
    refine ⟨PrimeSpectrum.zeroLocus (p.asIdeal : Set A), ?_, ?_⟩
    · rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact Set.mem_image_of_mem _ hp
    · rw [isGenericPoint_def, PrimeSpectrum.closure_singleton]
  · rintro ⟨C, hC, hpC⟩
    rw [← PrimeSpectrum.vanishingIdeal_singleton]
    apply (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes (R := A)).2
    rw [hpC.def]
    exact hC

/-! ## Disjoint closed subsets -/

/-- Two vanishing sets are disjoint exactly when the sum of their ideals is
the unit ideal. -/
theorem zeroLocus_disjoint_iff_sup_eq_top {A : Type u} [CommRing A]
    (I J : Ideal A) :
    Disjoint (PrimeSpectrum.zeroLocus (I : Set A))
      (PrimeSpectrum.zeroLocus (J : Set A)) ↔ I ⊔ J = ⊤ := by
  rw [Set.disjoint_iff_inter_eq_empty, ← PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_empty_iff_eq_top]

/-! ## Connected spaces and components -/

/-- The source's connected-space definition is the canonical `ConnectedSpace`
class, equivalently connectedness of the whole space. -/
theorem connected_space_iff_connected_univ {X : Type u} [TopologicalSpace X] :
    ConnectedSpace X ↔ IsConnected (Set.univ : Set X) := by
  exact connectedSpace_iff_univ

/-- For a nonzero ring, disconnectedness of the spectrum is equivalent to a
nontrivial product decomposition of the ring. -/
theorem spectrum_disconnected_iff_product {A : Type u} [CommRing A] [Nontrivial A] :
    ¬ ConnectedSpace (PrimeSpectrum A) ↔
      ∃ (B C : Type u) (_ : CommRing B) (_ : CommRing C),
        Nontrivial B ∧ Nontrivial C ∧ Nonempty (A ≃+* B × C) := by
  constructor
  · intro h
    have hcl : ∃ s : Set (PrimeSpectrum A),
        IsClopen s ∧ s ≠ ∅ ∧ s ≠ Set.univ := by
      by_contra! hs
      apply h
      rw [connectedSpace_iff_clopen]
      refine ⟨inferInstance, ?_⟩
      intro s hs'
      by_cases hs_empty : s = ∅
      · exact Or.inl hs_empty
      · exact Or.inr (hs s hs' (Set.nonempty_iff_ne_empty.mpr hs_empty))
    rcases hcl with ⟨s, hs, hs0, hsu⟩
    obtain ⟨e, he, hse⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hs
    have he0 : e ≠ 0 := by
      intro he0
      apply hs0
      rw [hse, he0]
      simp
    have he1 : e ≠ 1 := by
      intro he1
      apply hsu
      rw [hse, he1]
      simp
    have hspan₁ : Ideal.span ({e} : Set A) ≠ ⊤ := by
      intro htop
      have hunit : IsUnit e := Ideal.span_singleton_eq_top.mp htop
      exact he1 ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he)
    have hspan₂ : Ideal.span ({1 - e} : Set A) ≠ ⊤ := by
      intro htop
      have hunit : IsUnit (1 - e) := Ideal.span_singleton_eq_top.mp htop
      have hone : 1 - e = 1 :=
        (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he.one_sub
      have h' : (1 : A) + 0 = 1 + e := by
        simpa using (sub_eq_iff_eq_add.mp hone)
      have heq : e = 0 := (add_left_cancel h').symm
      exact he0 heq
    refine ⟨A ⧸ Ideal.span ({e} : Set A), A ⧸ Ideal.span ({1 - e} : Set A),
      inferInstance, inferInstance, Ideal.Quotient.nontrivial_iff.mpr hspan₁,
      Ideal.Quotient.nontrivial_iff.mpr hspan₂, ?_⟩
    have heq : e * (1 - e) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    exact ⟨(AlgEquiv.prodQuotientOfIsIdempotentElem A he he.one_sub
      (by simp) heq).toRingEquiv⟩
  · rintro ⟨B, C, hBcomm, hCcomm, hB, hC, ⟨e⟩⟩
    let _ : CommRing B := hBcomm
    let _ : CommRing C := hCcomm
    intro hconn
    have hsum : ConnectedSpace (PrimeSpectrum B ⊕ PrimeSpectrum C) :=
      (PrimeSpectrum.primeSpectrumProdHomeo (R := B) (S := C)).connectedSpace_iff.mp
        ((PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mp hconn)
    have hcl := (connectedSpace_iff_clopen.mp hsum).2
      (Set.range (Sum.inl : PrimeSpectrum B → PrimeSpectrum B ⊕ PrimeSpectrum C))
      isClopen_range_inl
    rcases hcl with hcl | hcl
    · exact (Set.range_nonempty _).ne_empty hcl
    · let c : PrimeSpectrum C := Classical.choice (inferInstance : Nonempty (PrimeSpectrum C))
      have hc : Sum.inr c ∈ Set.range (Sum.inl : PrimeSpectrum B → PrimeSpectrum B ⊕ PrimeSpectrum C) := by
        rw [hcl]
        exact mem_univ _
      rcases hc with ⟨b, hb⟩
      cases hb

/-- Mathlib's `connectedComponent` contains its defining point, is connected,
and is closed. -/
theorem connected_component_basic_properties {X : Type u} [TopologicalSpace X] (x : X) :
    x ∈ connectedComponent x ∧
      IsConnected (connectedComponent x) ∧
        IsClosed (connectedComponent x) := by
  exact ⟨mem_connectedComponent, isConnected_connectedComponent,
    isClosed_connectedComponent⟩

/-- The canonical connected component is maximal among connected subsets that
contain its point. -/
theorem connected_component_is_maximal {X : Type u} [TopologicalSpace X] (x : X)
    {T : Set X} (hT : IsConnected T) (hx : x ∈ T) :
    T ⊆ connectedComponent x := by
  exact hT.subset_connectedComponent hx

/-! ## Stability and the infinite-product warning -/

/-- Connected components of an affine spectrum are stable under
generalization. -/
theorem spectrum_connected_component_stable_under_generalization
    {A : Type u} [CommRing A] (x : PrimeSpectrum A) :
    StableUnderGeneralization (connectedComponent x) := by
  intro y z hyz hz
  have hu : IsConnected (connectedComponent x ∪ closure ({z} : Set (PrimeSpectrum A))) :=
    IsConnected.union ⟨y, hz, specializes_iff_mem_closure.mp hyz⟩
      isConnected_connectedComponent isConnected_singleton.closure
  have hsub : connectedComponent x ∪ closure ({z} : Set (PrimeSpectrum A)) ⊆
      connectedComponent x :=
    hu.subset_connectedComponent (mem_union_left _ mem_connectedComponent)
  exact hsub (mem_union_right _ (subset_closure (mem_singleton z)))

/-- For a Noetherian ring, connected components of the spectrum are open. -/
theorem spectrum_connected_component_is_open_of_noetherian
    {A : Type u} [CommRing A] [IsNoetherianRing A] (x : PrimeSpectrum A) :
    IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents (PrimeSpectrum A)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let T : Set (Set (PrimeSpectrum A)) :=
    {Z | Z ∈ irreducibleComponents (PrimeSpectrum A) ∧
      Disjoint Z (connectedComponent x)}
  have hTfin : T.Finite := hfin.subset (fun Z hZ => hZ.1)
  have hCcompl : (connectedComponent x)ᶜ = ⋃₀ T := by
    apply subset_antisymm
    · intro y hy
      let Z := irreducibleComponent y
      have hZ : Z ∈ irreducibleComponents (PrimeSpectrum A) :=
        irreducibleComponent_mem_irreducibleComponents y
      have hdisj : Disjoint Z (connectedComponent x) := by
        rw [Set.disjoint_iff_inter_eq_empty]
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        apply hy
        have hZsub : Z ⊆ connectedComponent z :=
          hZ.1.isConnected.subset_connectedComponent hz.1
        have heq : connectedComponent z = connectedComponent x :=
          (connectedComponent_eq hz.2).symm
        exact heq ▸ hZsub (mem_irreducibleComponent)
      exact mem_sUnion_of_mem mem_irreducibleComponent ⟨hZ, hdisj⟩
    · intro y hy
      rcases mem_sUnion.mp hy with ⟨Z, hZT, hyZ⟩
      intro hyC
      exact Set.disjoint_left.mp hZT.2 hyZ hyC
  have hclosed : IsClosed (connectedComponent x)ᶜ := by
    rw [hCcompl, Set.sUnion_eq_biUnion]
    exact hTfin.isClosed_biUnion (fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1)
  simpa only [compl_compl] using (isOpen_compl_iff.mpr hclosed)

/-- The infinite product of copies of `𝔽₂` used in the source warning. -/
abbrev infiniteBooleanProductRing : Type := ℕ → ZMod 2

/-- This infinite product has infinitely many points, all of which are
closed; it is the source's counterexample to openness of components without
Noetherian hypotheses. -/
theorem infinite_boolean_product_spectrum_warning :
    Infinite (PrimeSpectrum infiniteBooleanProductRing) ∧
      ∀ p : PrimeSpectrum infiniteBooleanProductRing,
        IsClosed ({p} : Set (PrimeSpectrum infiniteBooleanProductRing)) := by
  sorry

/-- The same infinite product has a connected component which is not open,
so the Noetherian openness conclusion cannot be extended to arbitrary rings. -/
theorem infinite_boolean_product_has_nonopen_connected_component :
    ∃ p : PrimeSpectrum infiniteBooleanProductRing,
      connectedComponent p = {p} ∧
        ¬ IsOpen (connectedComponent p) := by
  sorry

end Formalization.Books.Exercises.Unit06
