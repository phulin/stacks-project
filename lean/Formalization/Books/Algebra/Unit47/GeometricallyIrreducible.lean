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

universe u v w z

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
  /-
  Proof roadmap for the prove stage.

  1. Work throughout with
     `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical` from
     `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.  First isolate a
     private field-factor lemma before this declaration: if `E` is a field
     over a separably closed `k` and `T` has irreducible spectrum, then
     `E ⊗[k] T` has prime nilradical.
  2. Prove that lemma by writing the two elements in the prime-ideal test as
     finite sums with `TensorProduct.exists_sum_tmul_eq`
     (`Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean`).  Pass to the
     finitely generated subfield of `E` and to the finitely generated
     subalgebra of `T` containing the displayed coefficients.  Quotient the
     latter by its unique minimal prime and embed it in its fraction field.
     Tensor inclusions stay injective by
     `TensorProduct.map_injective_of_flat_flat`; pull nilpotence back along
     those injections.
  3. In the resulting two-field case use
     `separableClosure.separableClosure_eq_bot` and
     `IsSepClosed.separableClosure_eq_bot_iff` from
     `Mathlib/FieldTheory/IsSepClosed.lean`.  The separable parts are the
     base field; the remaining algebraic parts are purely inseparable by
     `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`.  Apply
     `Formalization.Books.Algebra.Unit46.
       tensorProduct_spectrum_homeomorph_of_isPurelyInseparable`
     (`Formalization/Books/Algebra/Unit46/UniversalHomeomorphisms.lean`) to
     discard those parts, and use
     `IntermediateField.LinearDisjoint.isDomain'` from
     `Mathlib/FieldTheory/LinearDisjoint.lean` for the separable/transcendental
     remainder.  This proves the field-factor nilradical is prime, not that
     the tensor product is reduced (the latter is false over an imperfect
     separably closed field).
  4. Apply the field-factor lemma to each generic point of `R`.  The map
     `PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))` is open by
     `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`
     (`Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`), and its fiber over
     `p` is identified with the spectrum over `p.asIdeal.ResidueField` by
     `PrimeSpectrum.preimageHomeomorphFiber` plus
     `Algebra.TensorProduct.cancelBaseChange` and `comm`.
     Feed these irreducible fibers and `hR` to
     `IsIrreducible.preimage_of_isPreirreducible_fiber` (as in
     `irreducibleSpectrum_of_openMap_of_dense_irreducibleFiber` above), and
     use the nonempty fiber over a generic point to finish.
  -/
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
    (IsGeometricallyIrreducible.{u, v, u} k S ↔
        IsIrreducibleAfterFiniteSeparableBaseChange k S) ∧
      (IsIrreducibleAfterFiniteSeparableBaseChange k S ↔
        IrreducibleSpace
          (PrimeSpectrum (SeparableClosure k ⊗[k] S))) ∧
      (IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] S)) ↔
        IrreducibleSpace
          (PrimeSpectrum (AlgebraicClosure k ⊗[k] S))) := by
  /-
  Proof roadmap for the prove stage.  The explicit `.{u, v, u}` is
  intentional: `IsIrreducibleAfterFiniteSeparableBaseChange` quantifies over
  `Type u`; leaving the third universe implicit made the left side a
  logically unrelated (and possibly vacuous) test universe.

  * Arbitrary -> finite separable is direct specialization.
  * For finite separable -> `SeparableClosure`, use
    `TensorProduct.exists_sum_tmul_eq` on the two elements occurring in the
    nilradical-primality test.  All first-factor coefficients lie in one
    `IntermediateField.adjoin k` of a finite set.  Its finite-dimensional
    instance comes from `IntermediateField.adjoin.finiteDimensional`, and its
    separability follows from `mem_separableClosure_iff` together with
    `IntermediateField.isSeparable_adjoin_iff_isSeparable`.  Lift both
    elements to this finite subextension; the induced tensor map is injective
    by `TensorProduct.map_injective_of_flat_flat`, so the nilpotent product
    can be tested there.
  * Conversely embed each finite separable `k'` in `SeparableClosure k` with
    `IsSepClosed.lift` (`Mathlib/FieldTheory/IsSepClosed.lean`).  The tensor
    map is injective by the same flatness lemma, and the contraction of the
    prime nilradical is the source nilradical (prove the equality elementwise
    with `mem_nilradical` and injectivity).
  * To pass from the separable-closure test to an arbitrary `K : Type u`,
    put `K` and `SeparableClosure k` into `AlgebraicClosure K`: give the
    latter its `k`-algebra by composition and use `IsSepClosed.lift` for the
    separable closure.  Apply
    `separablyClosed_tensorProduct_irreducible` over `SeparableClosure k` to
    the already irreducible `SeparableClosure k ⊗[k] S`, transport through
    `Algebra.TensorProduct.cancelBaseChange`, and descend along the injective
    map `K ⊗[k] S -> AlgebraicClosure K ⊗[k] S`.
  * For the last equivalence, set `L := SeparableClosure k` and
    `Omega := AlgebraicClosure k`, algebraize the map
    `IsSepClosed.lift : L ->_k Omega`, and install the scalar tower.  Since
    `L` is separably closed and `Omega/L` is algebraic,
    `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed` supplies
    `IsPurelyInseparable L Omega`.  Use Unit 46's
    `tensorProduct_spectrum_homeomorph_of_isPurelyInseparable` on
    `L ⊗[k] S`, then `Algebra.TensorProduct.cancelBaseChange` to identify the
    target with `Omega ⊗[k] S`; irreducibility is preserved by the resulting
    homeomorphism.
  -/
  sorry

/-- Over a separably closed field, geometric irreducibility is ordinary
irreducibility of the spectrum. -/
theorem isGeometricallyIrreducible_iff_irreducibleSpectrum
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [IsSepClosed k] :
    IsGeometricallyIrreducible.{u, v, u} k S ↔
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
    (hS : IsGeometricallyIrreducible.{u, v, w} k S) :
    ∀ A : Subalgebra k S, IsGeometricallyIrreducible.{u, v, w} k A := by
  /-
  Proof roadmap.  Keep the same base-change universe `w` on the hypothesis
  and conclusion (the previous two independent implicit universes made the
  statement false/vacuous in small universes).  Introduce `A` and a field
  `K : Type w`.  Let

    `m := Algebra.TensorProduct.map (AlgHom.id k K) A.val`.

  Its underlying linear map is injective by
  `Module.Flat.lTensor_preserves_injective_linearMap A.val.toLinearMap
    Subtype.val_injective`; this is exactly the pattern in
  `Unit43.isGeometricallyReduced_subalgebra`
  (`Formalization/Books/Algebra/Unit43/GeometricallyReduced.lean`).  Convert
  `hS K` to primality of the target nilradical.  Prove
  `Ideal.comap m.toRingHom (nilradical (K ⊗[k] S)) =
    nilradical (K ⊗[k] A)` elementwise using `mem_nilradical`: the reverse
  implication uses injectivity of `m`.  The comap is prime by
  `Ideal.IsPrime.comap`; rewrite by this equality and convert back with
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.
  -/
  intro A K _ _
  let m := Algebra.TensorProduct.map (AlgHom.id k K) A.val
  have hm : Function.Injective m :=
    Module.Flat.lTensor_preserves_injective_linearMap A.val.toLinearMap Subtype.val_injective
  have htarget : (nilradical (K ⊗[k] S)).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp (hS K)
  have hcomap : Ideal.comap m.toRingHom (nilradical (K ⊗[k] S)) =
      nilradical (K ⊗[k] A) := by
    ext x
    rw [Ideal.mem_comap, mem_nilradical, mem_nilradical]
    exact IsNilpotent.map_iff hm
  have hcomapprime : (Ideal.comap m.toRingHom (nilradical (K ⊗[k] S))).IsPrime := by
    refine ⟨Ideal.comap_ne_top m.toRingHom htarget.1, ?_⟩
    intro x y hxy
    have hxy' : m x * m y ∈ nilradical (K ⊗[k] S) := by
      change m (x * y) ∈ nilradical (K ⊗[k] S) at hxy
      rwa [map_mul] at hxy
    have hcases := htarget.2 hxy'
    rcases hcases with hx | hy
    · left
      change m x ∈ nilradical (K ⊗[k] S)
      exact hx
    · right
      change m y ∈ nilradical (K ⊗[k] S)
      exact hy
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  rw [← hcomap]
  exact hcomapprime

/-- Geometric irreducibility of all finite-type subalgebras implies geometric
irreducibility of the ambient algebra. -/
theorem isGeometricallyIrreducible_of_finiteType_subalgebras
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : ∀ A : Subalgebra k S, Algebra.FiniteType k A →
      IsGeometricallyIrreducible.{u, v, w} k A) :
    IsGeometricallyIrreducible.{u, v, w} k S := by
  /-
  Proof roadmap.  Fix `K : Type w` and use
  `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`.  For the
  multiplicative clause, suppose `x * y` is nilpotent in `K ⊗[k] S`.

  1. Apply `TensorProduct.exists_sum_tmul_eq` separately to `x` and `y`.
     Let `A : Subalgebra k S` be `Algebra.adjoin k` of the union of the two
     finite sets of right-hand coefficients.  Establish
     `Algebra.FiniteType k A` with `Subalgebra.fg_adjoin_finset` and
     `Subalgebra.fg_iff_finiteType`.
  2. Form explicit lifts `xA yA : K ⊗[k] A` by the same finite sums.  The map
     `m := Algebra.TensorProduct.map (AlgHom.id k K) A.val` is injective by
     `TensorProduct.map_injective_of_flat_flat`, exactly as in
     `Unit43.exists_finiteType_subalgebras_of_nonzero_zeroDivisor_tensorProduct`
     (`Formalization/Books/Algebra/Unit43/GeometricallyReduced.lean`).
     Therefore `(xA * yA)` is nilpotent because its image is `x * y`.
  3. Apply the prime nilradical supplied by `(hS A hA) K`; it says `xA` or
     `yA` is nilpotent.  Mapping forward gives the required disjunction for
     `x,y`.
  4. For `nilradical != top`, use the finite-type algebra `A = bot` and its
     geometrically irreducible base change, or equivalently inject its
     nontrivial tensor product into `K ⊗[k] S`.  Do not infer this merely from
     `CommRing`, which permits the trivial ring.
  -/
  sorry

/-- A directed colimit of geometrically irreducible algebras is geometrically
irreducible. -/
theorem isGeometricallyIrreducible_directLimit
    {k : Type u} [Field k] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)]
    (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
    [DirectedSystem A (f · · ·)]
    (hA : ∀ i, IsGeometricallyIrreducible.{u, w, z} k (A i)) :
    IsGeometricallyIrreducible.{u, max v w, z} k (DirectLimit A f) := by
  /-
  Proof roadmap.  The result's algebra universe is `max v w`, while the
  field-test universe `z` is deliberately shared with every `hA i`.
  Follow `Unit43.isGeometricallyReduced_directLimit`
  (`Formalization/Books/Algebra/Unit43/GeometricallyReduced.lean`) verbatim
  through its representation infrastructure:

  * for fixed `K : Type z`, define `fL`, the compatible linear directed
    system, `ea := Module.DirectLimit.linearEquiv ...`,
    `e := TensorProduct.directLimitRight fL K`, and
    `F := e.symm.trans (TensorProduct.congr (LinearEquiv.refl k K) ea)`;
  * define
    `phi i := Algebra.TensorProduct.map (AlgHom.id k K)
      (DirectLimit.Algebra.of A f i)`;
  * copy the three claims named `hphi`, `hphif`, and `hrep` from Unit 43:
    `hrep` represents every element at one stage, and directedness moves two
    representatives to a common stage.

  Convert the goal to primality of the nilradical.  Represent `x` and `y` at
  one stage `i`.  If their product is nilpotent in the colimit tensor, apply
  `F.symm` to the zero power and use
  `Module.DirectLimit.of.zero_exact` to obtain a later `j` where the product
  power is zero.  The prime nilradical from `hA j K` makes one of the two
  images nilpotent; `hphif` maps that conclusion back to the colimit.  Prove
  properness similarly: an equality `0 = 1` in the colimit becomes such an
  equality at a later stage via `DirectLimit.exists_eq_one`, contradicting
  the nonempty spectrum supplied by `hA` there.

  Known dead end: `TensorProduct.directLimitRight` is only a linear
  equivalence, not a ring equivalence.  Use it only to transfer zero
  equalities; do all powers and products through `phi`.
  -/
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
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (hS : IsGeometricallyIrreducible.{u, w, v} k S) :
    InducesBijectionOnIrreducibleComponents
      (PrimeSpectrum.comap
        (tensorLeftRingHom (k := k) (R := R) (S := S))) := by
  /-
  Proof roadmap.  Put
  `f := PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))`; the displayed map is
  definitionally the same map as `f`.

  * `PrimeSpectrum.continuous_comap` gives continuity, and
    `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`
    (`Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`) gives openness.
  * For `p : PrimeSpectrum R`, compose
    `PrimeSpectrum.preimageHomeomorphFiber R (R ⊗[k] S) p` with the spectrum
    homeomorphism induced by the ring equivalence assembled from
    `Algebra.TensorProduct.comm` and
    `Algebra.TensorProduct.cancelBaseChange`.  The resulting fiber is
    `PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S)`, irreducible by
    `hS p.asIdeal.ResidueField`; this is why the repaired hypothesis uses
    the universe of `R` as its third level.
  * The same homeomorphism and `.toNonempty` show every fiber is nonempty,
    hence `f` is surjective.  This avoids trying to synthesize a global
    faithfully-flat instance in the possible trivial-base branch.
  * Apply
    `irreducibleComponentsEquivOfIsPreirreducibleFiber f
      (PrimeSpectrum.continuous_comap _) hopen hfiber hsurj`
    from `Mathlib/Topology/Irreducible.lean`.  That order is an equivalence
    from base components to total components; take `.symm.toEquiv` for the
    `e` required here.  Its inverse is defined by image, so
    `Set.image_preimage_eq _ hsurj` (or the generated simp lemma) proves
    `f '' C.1 = (e C).1`.
  -/
  sorry

/-! ## Geometrically irreducible field extensions -/

/-- A field extension whose base is algebraically closed in the top field is
geometrically irreducible. -/
theorem fieldExtension_geometricallyIrreducible_of_algebraicallyClosedIn
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (h : Formalization.Books.Fields.Unit26.AlgebraicallyClosedIn k K) :
    IsGeometricallyIrreducible.{u, u, u} k K := by
  /-
  Proof roadmap.  Factor the field criterion needed here and by
  `geometricallyIrreducible_iff_separableElements_in_base` into a private
  lemma placed immediately before this declaration; the later public theorem
  should simply expose that helper.  Its statement is the same equivalence
  with the explicit `.{u,u,u}` universe levels.

  Apply the helper.  Given `alpha : K` and `halpha : IsSeparable k alpha`,
  `halpha.isIntegral.isAlgebraic` supplies the hypothesis expected by `h`.
  Obtain `y : k` with `algebraMap k K y = alpha`, and return
  `⟨y, that_equality⟩` as membership in the range.  The source hypothesis is
  stronger than necessary (it controls every algebraic element), but it is a
  valid sufficient hypothesis and should not be weakened in this theorem.
  -/
  sorry

/-- Geometric irreducibility is transitive in a tower of field extensions and
algebras. -/
theorem geometricallyIrreducible_transitive
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra K S] [Algebra k S]
    [IsScalarTower k K S]
    (hK : IsGeometricallyIrreducible.{u, v, u} k K)
    (hS : IsGeometricallyIrreducible.{v, w, max u v} K S) :
    IsGeometricallyIrreducible.{u, w, u} k S := by
  /-
  Proof roadmap.  Fix `F : Type u` over `k` and put `B := F ⊗[k] K`, with
  the right-factor `K`-algebra structure
  `Algebra.TensorProduct.rightAlgebra`.  Then `hK F` makes `PrimeSpectrum B`
  irreducible.  Apply
  `geometricallyIrreducible_baseChange_components` over `K`, with `R := B`
  and the repaired `hS`: residue fields of `B` live in `Type (max u v)`,
  exactly its third universe parameter.  The component equivalence sends a
  singleton set of components of `B` to a singleton set of components of
  `B ⊗[K] S`; use `irreducibleComponents_eq_singleton` (both directions in
  `Mathlib/Topology/Irreducible.lean`) to obtain irreducibility of that
  spectrum.

  Finally transport along the canonical algebra equivalence
  `(F ⊗[k] K) ⊗[K] S ≃ F ⊗[k] S`, built from
  `Algebra.TensorProduct.cancelBaseChange`, `comm`, and the supplied
  `IsScalarTower k K S`.  Use
  `PrimeSpectrum.homeomorphOfRingEquiv ... .irreducibleSpace_iff` for the
  final assembly.
  -/
  sorry

/-- Geometric irreducibility of a field extension is equivalent to that of
the corresponding one-variable rational-function extension. -/
theorem geometricallyIrreducible_iff_rationalFunctionField
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible.{u, u, u} k K ↔
      letI : Algebra
          (Formalization.Books.Fields.Unit26.rationalFunctionField k
            (ULift.{u} (Fin 1)))
          (Formalization.Books.Fields.Unit26.rationalFunctionField K
            (ULift.{u} (Fin 1))) :=
        Formalization.Books.Fields.Unit26.rationalFunctionFieldExtensionAlgebra
          k K (ULift.{u} (Fin 1))
      IsGeometricallyIrreducible.{u, u, u}
        (Formalization.Books.Fields.Unit26.rationalFunctionField k
          (ULift.{u} (Fin 1)))
        (Formalization.Books.Fields.Unit26.rationalFunctionField K
          (ULift.{u} (Fin 1))) := by
  /-
  Proof roadmap.  Use the private field criterion described at
  `fieldExtension_geometricallyIrreducible_of_algebraicallyClosedIn` to
  replace both sides by triviality of the relative separable closure.  More
  explicitly, `mem_separableClosure_iff` and `IntermediateField.mem_bot`
  turn the elementwise range condition into
  `separableClosure k K = bot`, and similarly after adjoining the variable.

  Prove one focused private field lemma:

    `separableClosure k K = bot` iff
    `separableClosure (rationalFunctionField k I)
      (rationalFunctionField K I) = bot`

  for the coefficient-extension algebra and a nonempty singleton `I`.
  Clear denominators with `IsFractionRing` and
  `IsFractionRing.ringHom_ext`; use
  `rationalFunctionFieldExtensionMap` and
  `rationalFunctionFieldExtensionAlgebra` from
  `Formalization/Books/Fields/Unit26/Transcendence.lean` to keep the algebra
  map definitionally aligned.  Separability of the cleared element is
  transported with `Polynomial.Separable.map` and `minpoly.algHom_eq`.
  Specializing the variable (after choosing a value avoiding the finitely
  many nonzero denominator/discriminant polynomials) recovers a separable
  coefficient in `K`; conversely map a forbidden separable coefficient into
  the rational-function field with `isSeparable_algebraMap` and
  `IsSeparable.tower_top`.

  Instantiate this lemma with `I := ULift.{u} (Fin 1)` and close both sides
  with the criterion.  Known dead end: Unit 26's
  `AlgebraicallyClosedIn` controls all algebraic elements and is too strong
  for this equivalence in imperfect characteristic; the proof must use the
  separable-closure condition, so purely inseparable coefficient extensions
  remain allowed.
  -/
  sorry

/-- Adjoining a transcendental variable preserves geometric irreducibility
of a field extension. -/
theorem geometricallyIrreducible_add_transcendental
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]
    (hLM : IsGeometricallyIrreducible.{u, u, u} M L) (x : K)
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
    IsGeometricallyIrreducible.{u, u, u}
      Mx (IntermediateField.extendScalars hMx) := by
  /-
  Proof roadmap.  Let `I := ULift.{u} (Fin 1)` and let both `I`-indexed
  families be constantly `x`.  From `hx` obtain algebraic independence over
  `L` with `algebraicIndependent_unique_type_iff`; obtain transcendence over
  `M` by `hx.of_tower_top M`, then algebraic independence there as well.
  Their `AlgebraicIndependent.aevalEquivField` maps

    `rationalFunctionField L I ≃_L Lx` and
    `rationalFunctionField M I ≃_M Mx`.

  Rewrite the ranges of the constant families as `{x}` to identify the
  targets with the `Lx` and `Mx` in the statement.  Check that the square of
  the two coefficient-extension maps commutes by
  `IsFractionRing.ringHom_ext`, reducing it to
  `MvPolynomial.map` on polynomials; this square also identifies the induced
  top algebra with `IntermediateField.extendScalars hMx`.

  Apply `geometricallyIrreducible_iff_rationalFunctionField` to `hLM`.
  Transport geometric irreducibility across the compatible base and top
  algebra equivalences: for each test field, use
  `Algebra.TensorProduct.congr` and
  `PrimeSpectrum.homeomorphOfRingEquiv ... .irreducibleSpace_iff`.
  The transported result is exactly the let-bound conclusion after the
  commuting-square equality is substituted.
  -/
  sorry

/-- A field extension is geometrically irreducible exactly when every
separable element of the top field lies in the base field. -/
theorem geometricallyIrreducible_iff_separableElements_in_base
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible.{u, u, u} k K ↔
      ∀ α : K, IsSeparable k α → α ∈ (algebraMap k K).range := by
  /-
  Proof roadmap for the private helper reused above, followed here by `exact`
  that helper.

  Forward direction:
  * for separable `alpha`, set `E := IntermediateField.adjoin k {alpha}`;
    `IntermediateField.adjoin.finiteDimensional` and
    `IntermediateField.isSeparable_adjoin_iff_isSeparable` make `E/k` a
    finite separable extension;
  * the finite-separable test theorem above makes `E ⊗[k] K` irreducible,
    while `Unit43.isReduced_tensorProduct_of_separable_extension`
    (`Formalization/Books/Algebra/Unit43/GeometricallyReduced.lean`) makes it
    reduced.  Hence it is a domain; because `E/k` is algebraic,
    `Algebra.TensorProduct.isField_of_isAlgebraic` upgrades it to a field;
  * the multiplication map from `E ⊗[k] K` to `K` is therefore injective.
    Translate that with
    `IntermediateField.linearDisjoint_iff'` and
    `Subalgebra.linearDisjoint_iff_injective`.  Restrict the right field from
    `top` to `E` via `IntermediateField.LinearDisjoint.of_le_right`, then use
    `IntermediateField.LinearDisjoint.eq_bot_of_self`; `alpha ∈ E = bot`
    is precisely the required range statement.

  Reverse direction:
  * by the finite-separable test theorem it suffices to prove that
    `E ⊗[k] K` is irreducible for every finite separable `E/k`;
  * use `IntermediateField.LinearDisjoint.isField_of_forall`
    (`Mathlib/FieldTheory/LinearDisjoint.lean`).  For arbitrary embeddings of
    `E` and `K` in a common field, pass to an algebraic closure and the normal
    closure of the image of `E`.  Every element in its intersection with the
    image of `K` is separable over `k`; pull it back through the embedding of
    `K`, apply the assumed range condition, and get intersection `bot`;
  * apply `IntermediateField.LinearDisjoint.of_inf_eq_bot` to the finite
    Galois normal closure, then
    `IntermediateField.LinearDisjoint.of_le_left` to the image of `E`.
    `isField_of_forall` now makes `E ⊗[k] K` a field, so its spectrum is
    irreducible.

  Keep normal-closure universe choices in `Type u` (all three fields in this
  declaration are explicitly in that universe); otherwise `isField_of_forall`
  introduces an avoidable `max` mismatch.
  -/
  sorry

/-- Passing from a field to the subfield of elements separably algebraic over
the base makes the remaining extension geometrically irreducible; finite
generation makes this intermediate extension finite. -/
theorem separableClosure_geometricallyIrreducible
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsGeometricallyIrreducible.{u, u, u} (separableClosure k K) K ∧
      (Algebra.EssFiniteType k K →
        Module.Finite k (separableClosure k K)) := by
  /-
  Proof roadmap.  For the first conjunct apply
  `geometricallyIrreducible_iff_separableElements_in_base` with base
  `L := separableClosure k K`.  The exact reusable fact
  `separableClosure.separableClosure_eq_bot k K`
  (`Mathlib/FieldTheory/SeparableClosure.lean`) says that an element of `K`
  separable over `L` lies in `bot : IntermediateField L K`; unfold
  `IntermediateField.mem_bot` to produce membership in
  `(algebraMap L K).range`.

  For the finite conjunct, introduce the `Algebra.EssFiniteType k K`
  instance and obtain
  `Module.Finite k (algebraicClosure k K)` from
  `Formalization.Books.Fields.Unit26.
    relative_algebraic_closure_finite_of_finitely_generated`
  (`Formalization/Books/Fields/Unit26/Transcendence.lean`).  The inclusion
  `separableClosure k K <= algebraicClosure k K` sends a separable element to
  an algebraic one via `IsSeparable.isIntegral.isAlgebraic`.  Regard this
  inclusion as a `k`-linear map and apply `Module.Finite.of_injective` with
  `Subtype.val_injective` to inherit module finiteness.
  -/
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
  /-
  Proof roadmap.  Add the focused imports
  `Mathlib.FieldTheory.Galois.Profinite` and
  `Mathlib.RingTheory.Invariant.Profinite`.  Put `G := Gal(L/k)` and
  `B := L ⊗[k] K`, viewed as a `K`-algebra through
  `Algebra.TensorProduct.includeRight`.

  1. Define the `MulSemiringAction G B` by
     `sigma • z := Algebra.TensorProduct.map sigma.toAlgHom (AlgHom.id k K) z`;
     prove the laws by `Algebra.TensorProduct.ext'` and `map_tmul`.  The action
     commutes with `K`, again by tensor extensionality.
  2. Install the Krull/profinite instances from
     `InfiniteGalois.continuousMulEquivToLimit`; `IsSepClosure.isGalois`
     supplies `IsGalois k L`.  Prove `ContinuousSMul G B` using the discrete
     criterion: after `TensorProduct.exists_sum_tmul_eq`, the stabilizer of a
     tensor contains the finite intersection of the open stabilizers of its
     finitely many `L`-coefficients.  These are open by
     `krullTopology_mem_nhds_one_iff_of_isGalois`.
  3. Build `Algebra.IsInvariant K B G`.  Rewrite a fixed tensor using a
     finite `k`-linearly independent family of right coefficients (choose a
     basis of their finite span); coefficient comparison says every left
     coefficient is fixed by `Gal(L/k)`.  Use
     `InfiniteGalois.mem_range_algebraMap_iff_fixed` from
     `Mathlib/FieldTheory/Galois/Infinite.lean`, and move those scalars across
     `TensorProduct.smul_tmul` to show the tensor is in the image of `K`.
  4. Both `p.asIdeal` and `q.asIdeal` contract to `bot : Ideal K`: the
     right-factor inclusion is injective by
     `Algebra.TensorProduct.includeRight_injective`, and a proper prime of a
     field has bottom contraction.  Therefore their `Ideal.under K` agree.
     Apply
     `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`
     (`Mathlib/RingTheory/Invariant/Profinite.lean`) to obtain `sigma` with
     the two ideals in one orbit.
  5. Convert pointwise ideal smul to `PrimeSpectrum.comap` and finish with
     `PrimeSpectrum.ext`.  Check the orientation: pointwise `sigma • p`
     is comap by the inverse tensor automorphism, whereas
     `galoisTensorPrimeAction sigma p` is comap by `sigma`; replace the orbit
     witness by `sigma.symm` before the final equality.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit47
