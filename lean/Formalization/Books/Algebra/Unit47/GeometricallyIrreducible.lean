import Formalization.Books.Fields.Unit26.Transcendence
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Maps.Basic

/-!
# Commutative Algebra, Chapter 47: Geometrically irreducible algebras

The source's geometric irreducibility predicate is expressed using Mathlib's
`IrreducibleSpace` on prime spectra.  Finite separable extensions, separable
closures, algebraically closed subextensions, rational function fields, and
separable closures use the canonical APIs from the earlier algebra and fields
chapters.
-/

namespace Formalization.Books.Algebra.Unit47

open Set
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Geometric irreducibility -/

/-- An algebra over a field is geometrically irreducible when every field base
change has irreducible spectrum. -/
def IsGeometricallyIrreducible (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    IrreducibleSpace (PrimeSpectrum (K ⊗[k] S))

/-- The source's introductory unique-minimal-prime formulation of geometric
irreducibility. -/
theorem isGeometricallyIrreducible_iff_unique_minimalPrime
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyIrreducible.{u, v, w} k S ↔
      ∀ (K : Type w) [Field K] [Algebra k K],
        ∃! p : PrimeSpectrum (K ⊗[k] S),
          p.asIdeal ∈ minimalPrimes (K ⊗[k] S) := by
  constructor
  · intro h K _ _
    have hK : IrreducibleSpace (PrimeSpectrum (K ⊗[k] S)) := h K
    have hnil : (nilradical (K ⊗[k] S)).IsPrime :=
      PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hK
    have hmin : nilradical (K ⊗[k] S) ∈ minimalPrimes (K ⊗[k] S) ∧
        ∀ p : Ideal (K ⊗[k] S), p ∈ minimalPrimes (K ⊗[k] S) →
          p = nilradical (K ⊗[k] S) := by
      rw [minimalPrimes_eq_minimals]
      constructor
      · change Minimal Ideal.IsPrime (nilradical (K ⊗[k] S))
        exact ⟨hnil, fun q hq _ => @nilradical_le_prime _ _ q hq⟩
      · intro p hp
        change Minimal Ideal.IsPrime p at hp
        exact (hp.eq_of_le hnil (@nilradical_le_prime _ _ p hp.1)).symm
    refine ⟨⟨nilradical (K ⊗[k] S), hnil⟩, hmin.1, ?_⟩
    intro q hq
    cases q with
    | mk q hqprime =>
      have hqeq := hmin.2 q hq
      subst q
      rfl
  · intro h K _ _
    obtain ⟨p, hp, hpu⟩ := h K
    have hunique : ∀ q : Ideal (K ⊗[k] S), q ∈ minimalPrimes (K ⊗[k] S) →
        q = p.asIdeal := by
      intro q hq
      have hqprime : q.IsPrime := hq.isPrime
      have heq : (⟨q, hqprime⟩ : PrimeSpectrum (K ⊗[k] S)) = p :=
        hpu ⟨q, hqprime⟩ hq
      exact congrArg PrimeSpectrum.asIdeal heq
    have hnil : nilradical (K ⊗[k] S) = p.asIdeal := by
      rw [nilradical_eq_sInf]
      apply le_antisymm
      · simpa only [nilradical_eq_sInf] using
          (@nilradical_le_prime _ _ p.asIdeal hp.isPrime)
      · rw [le_sInf_iff]
        intro q hq
        obtain ⟨r, hr, hrq⟩ := @Ideal.exists_minimalPrimes_le _ _ _ q hq bot_le
        exact (hunique r hr).symm ▸ hrq
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    rw [hnil]
    exact hp.isPrime

/-- The fibre of an algebra map at a point of the base spectrum. -/
def irreducibleFiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) : Prop :=
  IrreducibleSpace (PrimeSpectrum (S ⊗[R] p.asIdeal.ResidueField))

/-- An open map with irreducible fibres over a dense set has irreducible
spectrum when the base spectrum is irreducible. -/
theorem irreducibleSpectrum_of_openMap_of_dense_irreducibleFiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)))
    (h : Dense {p : PrimeSpectrum R | irreducibleFiber (S := S) p}) :
    IrreducibleSpace (PrimeSpectrum S) := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  have hfiber : {p : PrimeSpectrum R | irreducibleFiber (S := S) p} ⊆
      {p : PrimeSpectrum R | IsPreirreducible (f ⁻¹' {p})} := by
    intro p hp
    let e : f ⁻¹' {p} ≃ₜ PrimeSpectrum (S ⊗[R] p.asIdeal.ResidueField) :=
      (PrimeSpectrum.preimageHomeomorphFiber R S p).trans
        (PrimeSpectrum.homeomorphOfRingEquiv
          (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv)
    have he : IrreducibleSpace (f ⁻¹' {p}) :=
      (e.irreducibleSpace_iff).mpr hp
    have hsub : IsIrreducible (f ⁻¹' {p}) :=
      @IsIrreducible.of_subtype _ _ _ he
    exact hsub.isPreirreducible
  have hpre : IsPreirreducible (f ⁻¹' (Set.univ : Set (PrimeSpectrum R))) :=
    (hR.isIrreducible_univ.isPreirreducible).preimage_of_dense_isPreirreducible_fiber
      f hopen (by
        intro p hp
        apply (closure_mono (show {p : PrimeSpectrum R |
            irreducibleFiber (S := S) p} ⊆
            (Set.univ : Set (PrimeSpectrum R)) ∩
              {p : PrimeSpectrum R | IsPreirreducible (f ⁻¹' {p})} from
          fun p hp => ⟨by simp, hfiber hp⟩)) (h p))
  have hne : (f ⁻¹' (Set.univ : Set (PrimeSpectrum R))).Nonempty := by
    obtain ⟨p, hp⟩ := h.nonempty
    let e : f ⁻¹' {p} ≃ₜ PrimeSpectrum (S ⊗[R] p.asIdeal.ResidueField) :=
      (PrimeSpectrum.preimageHomeomorphFiber R S p).trans
        (PrimeSpectrum.homeomorphOfRingEquiv
          (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv)
    obtain ⟨q, hq⟩ := (show IrreducibleSpace
      (PrimeSpectrum (S ⊗[R] p.asIdeal.ResidueField)) from hp).toNonempty
    exact ⟨(e.symm ⟨q, hq⟩).1, by simp⟩
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (PrimeSpectrum S))
  exact ⟨by simpa only [preimage_univ] using hne,
    by simpa only [preimage_univ] using hpre⟩

/-- Flat finite-presentation maps satisfy the dense irreducible-fibre
criterion. -/
theorem flat_fibres_irreducible
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hR : IrreducibleSpace (PrimeSpectrum R)) [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    (h : Dense {p : PrimeSpectrum R | irreducibleFiber (S := S) p}) :
    IrreducibleSpace (PrimeSpectrum S) := by
  exact irreducibleSpectrum_of_openMap_of_dense_irreducibleFiber hR
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation h

/-- Over a separably closed field, the tensor product of two algebras with
irreducible spectra again has irreducible spectrum. -/
theorem separablyClosed_tensorProduct_irreducible
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k]
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  sorry

/-! ## Testing after field extensions -/

/-- Irreducibility after every finite separable extension of the base field. -/
def IsIrreducibleAfterFiniteSeparableBaseChange
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S] : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'],
    IrreducibleSpace (PrimeSpectrum (k' ⊗[k] S))

/-- The four equivalent tests for geometric irreducibility: arbitrary field
extensions, finite separable extensions, a separable closure, and an
algebraic closure. -/
theorem isGeometricallyIrreducible_iff_finiteSeparable_iff_separableClosure_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    (IsGeometricallyIrreducible k S ↔
        IsIrreducibleAfterFiniteSeparableBaseChange k S) ∧
      (IsIrreducibleAfterFiniteSeparableBaseChange k S ↔
        IrreducibleSpace
          (PrimeSpectrum (SeparableClosure k ⊗[k] S))) ∧
      (IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] S)) ↔
        IrreducibleSpace
          (PrimeSpectrum (AlgebraicClosure k ⊗[k] S))) := by
  sorry

/-- Over a separably closed field, geometric irreducibility is ordinary
irreducibility of the spectrum. -/
theorem isGeometricallyIrreducible_iff_irreducibleSpectrum
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [IsSepClosed k] :
    IsGeometricallyIrreducible k S ↔
      IrreducibleSpace (PrimeSpectrum S) := by
  have htests :=
    isGeometricallyIrreducible_iff_finiteSeparable_iff_separableClosure_iff_algebraicClosure
      (k := k) (S := S)
  constructor
  · intro h
    have h' := htests.1.mp h
    have hk := h' k
    exact (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid k S).toRingEquiv).irreducibleSpace_iff.mp hk
  · intro hS
    apply htests.1.mpr
    intro K _ _ _ _
    exact separablyClosed_tensorProduct_irreducible
      (R := K) (S := S) inferInstance hS

/-! ## Permanence properties -/

/-- Geometric irreducibility descends to every subalgebra over the base. -/
theorem isGeometricallyIrreducible_subalgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyIrreducible k S) :
    ∀ A : Subalgebra k S, IsGeometricallyIrreducible k A := by
  sorry

/-- Geometric irreducibility of all finite-type subalgebras implies geometric
irreducibility of the ambient algebra. -/
theorem isGeometricallyIrreducible_of_finiteType_subalgebras
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : ∀ A : Subalgebra k S, Algebra.FiniteType k A →
      IsGeometricallyIrreducible k A) :
    IsGeometricallyIrreducible k S := by
  sorry

/-- A directed colimit of geometrically irreducible algebras is geometrically
irreducible. -/
theorem isGeometricallyIrreducible_directLimit
    {k : Type u} [Field k] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)]
    (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
    [DirectedSystem A (f · · ·)]
    (hA : ∀ i, IsGeometricallyIrreducible k (A i)) :
    IsGeometricallyIrreducible k (DirectLimit A f) := by
  sorry

/-! ## Irreducible components after base change -/

/-- A function induces a bijection on irreducible components when its images
give the corresponding components. -/
def InducesBijectionOnIrreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∃ e : irreducibleComponents X ≃ irreducibleComponents Y,
    ∀ C : irreducibleComponents X, f '' C.1 = (e C).1

/-- The canonical inclusion of the left tensor factor. -/
noncomputable def tensorLeftRingHom
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] : R →+* R ⊗[k] S :=
  Algebra.TensorProduct.includeLeftRingHom

/-- Tensoring with a geometrically irreducible algebra induces a bijection on
irreducible components. -/
theorem geometricallyIrreducible_baseChange_components
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (hS : IsGeometricallyIrreducible k S) :
    InducesBijectionOnIrreducibleComponents
      (PrimeSpectrum.comap
        (tensorLeftRingHom (k := k) (R := R) (S := S))) := by
  sorry

/-! ## Geometrically irreducible field extensions -/

/-- A field extension whose base is algebraically closed in the top field is
geometrically irreducible. -/
theorem fieldExtension_geometricallyIrreducible_of_algebraicallyClosedIn
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (h : Formalization.Books.Fields.Unit26.AlgebraicallyClosedIn k K) :
    IsGeometricallyIrreducible k K := by
  sorry

/-- Geometric irreducibility is transitive in a tower of field extensions and
algebras. -/
theorem geometricallyIrreducible_transitive
    {k K S : Type*} [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra K S] [Algebra k S]
    [IsScalarTower k K S]
    (hK : IsGeometricallyIrreducible k K)
    (hS : IsGeometricallyIrreducible K S) :
    IsGeometricallyIrreducible k S := by
  sorry

/-- Geometric irreducibility of a field extension is equivalent to that of
the corresponding one-variable rational-function extension. -/
theorem geometricallyIrreducible_iff_rationalFunctionField
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible k K ↔
      letI : Algebra
          (Formalization.Books.Fields.Unit26.rationalFunctionField k
            (ULift.{u} (Fin 1)))
          (Formalization.Books.Fields.Unit26.rationalFunctionField K
            (ULift.{u} (Fin 1))) :=
        Formalization.Books.Fields.Unit26.rationalFunctionFieldExtensionAlgebra
          k K (ULift.{u} (Fin 1))
      IsGeometricallyIrreducible
        (Formalization.Books.Fields.Unit26.rationalFunctionField k
          (ULift.{u} (Fin 1)))
        (Formalization.Books.Fields.Unit26.rationalFunctionField K
          (ULift.{u} (Fin 1))) := by
  sorry

/-- Adjoining a transcendental variable preserves geometric irreducibility
of a field extension. -/
theorem geometricallyIrreducible_add_transcendental
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]
    (hLM : IsGeometricallyIrreducible M L) (x : K)
    (hx : Transcendental L x) :
    let Lx := IntermediateField.adjoin L ({x} : Set K)
    let Mx := IntermediateField.adjoin M ({x} : Set K)
    let hMx : Mx ≤ Lx.restrictScalars M := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y = x := by simpa using hy
      subst y
      change x ∈ Lx
      exact IntermediateField.subset_adjoin L ({x} : Set K) (by simp)
    IsGeometricallyIrreducible Mx (IntermediateField.extendScalars hMx) := by
  sorry

/-- A field extension is geometrically irreducible exactly when every
separable element of the top field lies in the base field. -/
theorem geometricallyIrreducible_iff_separableElements_in_base
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible k K ↔
      ∀ α : K, IsSeparable k α → α ∈ (algebraMap k K).range := by
  sorry

/-- Passing from a field to the subfield of elements separably algebraic over
the base makes the remaining extension geometrically irreducible; finite
generation makes this intermediate extension finite. -/
theorem separableClosure_geometricallyIrreducible
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible (separableClosure k K) K ∧
      (Algebra.EssFiniteType k K →
        Module.Finite k (separableClosure k K)) := by
  sorry

/-! ## Galois orbits of primes -/

/-- The action of a base-field automorphism on the prime spectrum of a tensor
product, acting on the first tensor factor. -/
noncomputable def galoisTensorPrimeAction
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (σ : L ≃ₐ[k] L) :
    PrimeSpectrum (L ⊗[k] K) → PrimeSpectrum (L ⊗[k] K) :=
  PrimeSpectrum.comap
    (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k K)).toRingHom

/-- The separable-closure Galois group acts transitively on the primes of the
tensor product with any field extension. -/
theorem galois_orbit_tensorProduct_primes
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [IsSepClosure k L] :
    ∀ p q : PrimeSpectrum (L ⊗[k] K),
      ∃ σ : L ≃ₐ[k] L, galoisTensorPrimeAction σ p = q := by
  sorry

end

end Formalization.Books.Algebra.Unit47
