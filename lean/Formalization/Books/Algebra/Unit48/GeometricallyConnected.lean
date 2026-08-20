import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Formalization.Books.Algebra.Unit21.OpenAndClosed

/-!
# Commutative Algebra, Chapter 48: Geometrically connected algebras

The source's geometric connectedness predicate is expressed using Mathlib's
`ConnectedSpace` on prime spectra.  The finite separable base-change test,
subalgebra and directed-colimit permanence statements, and the idempotent and
connected-component formulations of arbitrary base change are recorded with
the canonical algebra and topology APIs.
-/

namespace Formalization.Books.Algebra.Unit48

open scoped TensorProduct

universe u v w x

noncomputable section

private theorem nontrivial_of_connected_primeSpectrum
    (R : Type*) [CommRing R] (hR : ConnectedSpace (PrimeSpectrum R)) :
    Nontrivial R := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  obtain ⟨p⟩ := hR.toNonempty
  apply p.isPrime.ne_top
  ext r
  constructor
  · intro
    trivial
  · intro
    rw [Subsingleton.elim r 0]
    exact p.asIdeal.zero_mem

/-! ## Tensor products over a separably closed field -/

/-- Over a separably closed field, the tensor product of two algebras with
connected spectra has connected spectrum. -/
theorem separablyClosed_tensorProduct_connected
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k]
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  /-
  Proof roadmap (the finite-type reduction avoids any circular appeal to
  geometric connectedness).

  * First recover `Nontrivial R` and `Nontrivial S` with
    `nontrivial_of_connected_primeSpectrum`.  Use
    `Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents`
    throughout.
  * Establish the following local finite-type-left claim.  If
    `A : Subalgebra k R` is `A.FG` and `PrimeSpectrum A` is connected, then
    `PrimeSpectrum (A ⊗[k] S)` is connected.  For the projection
    `f := PrimeSpectrum.comap (algebraMap A (A ⊗[k] S))`, use
    `PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field` from
    `Mathlib.RingTheory.Spectrum.Prime.Chevalley`.  The nonzero vector space
    `S` is faithfully flat over `k`; the base-change instance in
    `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` makes `f` surjective.
  * In that claim, install `IsJacobsonRing A` using
    `Formalization.Books.Algebra.Unit35.finiteType_algebra_over_field_isJacobson` from
    `Formalization.Books.Algebra.Unit35.JacobsonRings`, then turn it into
    `JacobsonSpace (PrimeSpectrum A)` with
    `Formalization.Books.Algebra.Unit35.jacobson_iff_primeSpectrum_isJacobsonSpace`.
    For a closed point
    `p`, give `p.asIdeal.ResidueField` its composite `k`-algebra structure.
    Its finiteness follows from `A.FG`,
    `Ideal.ResidueField.algebraMap_residueField_surjective`, and
    `finite_of_finite_type_of_isJacobsonRing`; hence it is algebraic over
    `k` and therefore purely inseparable by
    `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed` in
    `Mathlib.FieldTheory.PurelyInseparable.Basic`.
  * Identify the fiber over `p` with the spectrum of
    `p.asIdeal.ResidueField ⊗[k] S` by composing
    `PrimeSpectrum.preimageHomeomorphFiber` from
    `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` with
    `Algebra.TensorProduct.cancelBaseChange` from
    `Mathlib.RingTheory.TensorProduct.Maps`.  Its connectedness is transported
    from `hS` using
    `Formalization.Books.Algebra.Unit46.tensorProduct_spectrum_homeomorph_of_isPurelyInseparable`
    in
    `Formalization.Books.Algebra.Unit46.UniversalHomeomorphisms`.
  * To finish the local claim, apply `connectedSpace_iff_clopen`.  For a
    clopen partition upstairs, its two images under the open surjection `f`
    are open and cover the connected base.  A closed point cannot lie in
    both images because its fiber is connected.  If their intersection were
    nonempty, `nonempty_inter_closedPoints` from
    `Mathlib.Topology.JacobsonSpace` would supply such a closed point.  Thus
    the images are disjoint and one is empty, so the original clopen is empty
    or universal.
  * Finally take an idempotent `e : R ⊗[k] S`.  Apply
    `exists_fg_and_mem_baseChange` from
    `Mathlib.RingTheory.Adjoin.FGBaseChange` to
    `Algebra.TensorProduct.comm k R S e`, obtaining an FG subalgebra
    `A : Subalgebra k R` and a lift `z : A ⊗[k] S`.  The inclusion
    `A ⊗[k] S → R ⊗[k] S` is injective by
    `Module.Flat.rTensor_preserves_injective_linearMap`; use this both to show
    `z` is idempotent and to push `z = 0` or `z = 1` back to `e`.  The same
    injectivity plus the idempotent criterion shows `PrimeSpectrum A` is
    connected, so the local claim applies.
  -/
  sorry

/-! ## Geometric connectedness -/

/-- An algebra over a field is geometrically connected when every field base
change has connected spectrum. -/
def IsGeometricallyConnected (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

/-- Specializing geometric connectedness at a field in the same universe. -/
theorem IsGeometricallyConnected.connectedSpace_tensorProduct
    {k : Type u} {S : Type v} {K : Type w} [Field k] [CommRing S]
    [Algebra k S] [Field K] [Algebra k K]
    (hS : IsGeometricallyConnected.{u, v, w} k S) :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S)) := by
  exact hS K

/-- A geometrically connected algebra has connected spectrum. -/
theorem IsGeometricallyConnected.connectedSpace
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyConnected.{u, v, u} k S) :
    ConnectedSpace (PrimeSpectrum S) := by
  have h := hS.connectedSpace_tensorProduct (K := k)
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.lid k S).toRingEquiv).connectedSpace_iff.mp h

/-- A geometrically connected algebra has no nontrivial idempotents after
any field base change in the universe quantified over by the predicate. -/
theorem IsGeometricallyConnected.isIdempotentElem_eq_zero_or_one
    {k : Type u} {S : Type v} {K : Type w} [Field k] [CommRing S]
    [Algebra k S] [Field K] [Algebra k K]
    (hS : IsGeometricallyConnected.{u, v, w} k S)
    {e : K ⊗[k] S} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let _ : ConnectedSpace (PrimeSpectrum (K ⊗[k] S)) :=
    hS.connectedSpace_tensorProduct
  let _ : Nontrivial (K ⊗[k] S) :=
    nontrivial_of_connected_primeSpectrum _ inferInstance
  exact (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents
    (K ⊗[k] S)).mp inferInstance e he

/-- Geometric connectedness can be tested after finite separable extensions of
the base field. -/
theorem isGeometricallyConnected_iff_finiteSeparable
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyConnected.{u, v, w} k S ↔
      ∀ (k' : Type w) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [Algebra.IsSeparable k k'],
        ConnectedSpace (PrimeSpectrum (k' ⊗[k] S)) := by
  /-
  Proof roadmap.  The explicit `w` on both sides is essential: all finite
  intermediate fields below are subtypes of a field in `Type w`, so no
  universe-resizing argument is needed.

  * The forward implication is immediate by applying geometric connectedness
    to `k'`; the finite-dimensional and separable instances are unused in
    this direction.
  * Conversely, fix `K : Type w`.  Put
    `L := AlgebraicClosure K`, give `L` the composite `k`-algebra structure,
    and set `Omega := separableClosure k L`.  Use
    `separableClosure.isSepClosure` and explicitly install
    `IsSepClosure.sep_closed k` as `IsSepClosed Omega`.
  * Prove `PrimeSpectrum (Omega ⊗[k] S)` connected with the no-nontrivial-
    idempotents criterion.  For an idempotent, use
    `TensorProduct.exists_finset` (or tensor induction) to collect its finitely
    many `Omega` coefficients and let `E := IntermediateField.adjoin k C`.
    Because `Omega/k` is algebraic and separable,
    `IntermediateField.adjoin.finiteDimensional` and
    `IntermediateField.isSeparable_adjoin_iff_isSeparable` provide exactly
    the two instances required by the hypothesis for `E : Type w`.  Lift the
    idempotent to `E ⊗[k] S`; the map to `Omega ⊗[k] S` is injective by
    `Module.Flat.rTensor_preserves_injective_linearMap`, so it remains
    idempotent and is forced to be `0` or `1` by the finite-separable test.
  * The inclusion `Omega →+* L` makes `L` an `Omega`-algebra.  Apply
    `separablyClosed_tensorProduct_connected` over `Omega` to the field `L`
    and the connected `Omega`-algebra `Omega ⊗[k] S`.  Transport the result
    along `Algebra.TensorProduct.cancelBaseChange k Omega L L S` to obtain
    connectedness of `PrimeSpectrum (L ⊗[k] S)`.
  * Descend from `L` to `K`: the map
    `K ⊗[k] S → L ⊗[k] S` induced by the algebraic-closure embedding is
    injective by `Module.Flat.rTensor_preserves_injective_linearMap` (the
    right factor `S` is flat over the field `k`).  Pull a putative idempotent
    of `K ⊗[k] S` forward, use connectedness over `L`, and reflect the
    resulting equality.  This proves the required connectedness for the
    arbitrary `K`.
  -/
  sorry

/- The equivalence above records the source's following remark that it is
   enough to check finite separable field extensions separately. -/

/-- Over a separably closed field, geometric connectedness is ordinary
connectedness of the spectrum. -/
theorem isGeometricallyConnected_iff_connectedSpectrum
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    [IsSepClosed k] :
    IsGeometricallyConnected.{u, v, u} k R ↔
      ConnectedSpace (PrimeSpectrum R) := by
  /-
  Proof roadmap.

  * For the forward implication specialize geometric connectedness to
    `K := k`, then transport through
    `PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid k R).toRingEquiv`.
  * For the reverse implication, introduce an arbitrary field
    `K : Type u`.  Show `ConnectedSpace (PrimeSpectrum K)` with
    `Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents`
    and
    `IsIdempotentElem.iff_eq_zero_or_one`.  Then apply
    `separablyClosed_tensorProduct_connected (R := K) (S := R)` to this
    connectedness and the assumed connectedness of `PrimeSpectrum R`.
    No finite-dimensional, separability, or nontriviality hypothesis is
    missing here: a field supplies the first factor, while connected spectra
    already force the algebra factor to be nonzero when that fact is needed.
  -/
  sorry

/-! ## Permanence properties -/

/-- Geometric connectedness descends to every `k`-subalgebra. -/
theorem isGeometricallyConnected_subalgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyConnected.{u, v, w} k S) :
    ∀ A : Subalgebra k S, IsGeometricallyConnected.{u, v, w} k A := by
  intro A
  apply (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := A)).2
  intro k' _ _ _ _
  have hconn : ConnectedSpace (PrimeSpectrum (k' ⊗[k] S)) :=
    (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := S)).1 hS k'
  have : Nontrivial (k' ⊗[k] S) :=
    nontrivial_of_connected_primeSpectrum _ hconn
  have : Nontrivial S :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k k').mp inferInstance
  have : Nontrivial A := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    have h01 : (0 : S) = 1 := by
      exact congrArg Subtype.val (Subsingleton.elim (0 : A) 1)
    exact zero_ne_one h01
  have : Nontrivial (k' ⊗[k] A) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' A (Algebra.linearMap k A) (FaithfulSMul.algebraMap_injective k A)
  let φ : k' ⊗[k] A →ₐ[k'] k' ⊗[k] S :=
    Algebra.TensorProduct.map (AlgHom.id k' k') A.val
  have hφ : Function.Injective φ := by
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  apply (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).2
  intro e he
  have he' : IsIdempotentElem (φ e) := he.map φ
  rcases (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).1
    hconn (φ e) he' with hzero | hone
  · left
    apply hφ
    simpa using hzero
  · right
    apply hφ
    simpa using hone

/-- If all finitely generated `k`-subalgebras are geometrically connected,
then the ambient algebra is geometrically connected. -/
theorem isGeometricallyConnected_of_finiteType_subalgebras
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : ∀ A : Subalgebra k S, Algebra.FiniteType k A →
      IsGeometricallyConnected.{u, v, w} k A) :
    IsGeometricallyConnected.{u, v, w} k S := by
  have hfgBot : (⊥ : Subalgebra k S).FG := by
    refine ⟨∅, ?_⟩
    simp
  have hgeomBot : IsGeometricallyConnected.{u, v, w}
      k (⊥ : Subalgebra k S) :=
    hS ⊥ ((⊥ : Subalgebra k S).fg_iff_finiteType.mp hfgBot)
  apply (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := S)).2
  intro k' _ _ _ _
  have hconnBot : ConnectedSpace
      (PrimeSpectrum (k' ⊗[k] (⊥ : Subalgebra k S))) :=
    (isGeometricallyConnected_iff_finiteSeparable
      (k := k) (S := (⊥ : Subalgebra k S))).1 hgeomBot k'
  have : Nontrivial (k' ⊗[k] (⊥ : Subalgebra k S)) :=
    nontrivial_of_connected_primeSpectrum _ hconnBot
  have : Nontrivial (⊥ : Subalgebra k S) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k k').mp inferInstance
  have : Nontrivial S :=
    Function.Injective.nontrivial (α := (⊥ : Subalgebra k S)) (β := S)
      (f := fun a : (⊥ : Subalgebra k S) => (a : S)) Subtype.val_injective
  have : Nontrivial (k' ⊗[k] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' S (Algebra.linearMap k S) (FaithfulSMul.algebraMap_injective k S)
  apply (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).2
  intro e he
  obtain ⟨C, hC, heC⟩ := exists_fg_and_mem_baseChange e
  have : Nontrivial C := by
    apply nontrivial_of_ne (0 : C) 1
    intro h
    apply zero_ne_one (α := S)
    exact congrArg (fun x : C => (x : S)) h
  have hgeomC : IsGeometricallyConnected.{u, v, w} k C :=
    hS C (C.fg_iff_finiteType.mp hC)
  let φ : k' ⊗[k] C →ₐ[k'] k' ⊗[k] S :=
    Algebra.TensorProduct.map (AlgHom.id k' k') C.val
  have hφ : Function.Injective φ := by
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨z, rfl⟩ := heC
  have hz : IsIdempotentElem z := by
    apply hφ
    change (Algebra.TensorProduct.map (AlgHom.id k' k') C.val) (z * z) =
      (Algebra.TensorProduct.map (AlgHom.id k' k') C.val) z
    rw [map_mul]
    exact he.eq
  have : Nontrivial (k' ⊗[k] C) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' C (Algebra.linearMap k C) (FaithfulSMul.algebraMap_injective k C)
  rcases (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).1
    ((isGeometricallyConnected_iff_finiteSeparable (k := k) (S := C)).1 hgeomC k') z hz with
    hzero | hone
  · left
    simpa using congrArg φ hzero
  · right
    simpa using congrArg φ hone

/-- A directed colimit of geometrically connected `k`-algebras is
geometrically connected. -/
theorem isGeometricallyConnected_directLimit
    {k : Type u} [Field k] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)]
    (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
    [DirectedSystem A (f · · ·)]
    (hA : ∀ i, IsGeometricallyConnected.{u, w, x} k (A i)) :
    IsGeometricallyConnected.{u, max v w, x} k (DirectLimit A f) := by
  classical
  apply (isGeometricallyConnected_iff_finiteSeparable
    (k := k) (S := DirectLimit A f)).2
  intro k' _ _ _ _
  have hAi_nontrivial : ∀ i, Nontrivial (A i) := by
    intro i
    have hconn : ConnectedSpace (PrimeSpectrum (k' ⊗[k] A i)) :=
      (isGeometricallyConnected_iff_finiteSeparable
        (k := k) (S := A i)).1 (hA i) k'
    have : Nontrivial (k' ⊗[k] A i) :=
      nontrivial_of_connected_primeSpectrum _ hconn
    exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right k k').mp inferInstance
  have : Nontrivial (DirectLimit A f) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hAi_nontrivial i
    apply nontrivial_of_ne (0 : DirectLimit A f) 1
    intro hzero
    have hzero' : (⟦⟨i, (0 : A i)⟩⟧ : DirectLimit A f) =
        ⟦⟨i, (1 : A i)⟩⟧ := by
      simpa only [DirectLimit.zero_def i, DirectLimit.one_def i] using hzero
    obtain ⟨j, hij, hij', hval⟩ := Quotient.eq.mp hzero'
    exact (zero_ne_one : (0 : A j) ≠ 1) (by simp at hval)
  have : Nontrivial (k' ⊗[k] DirectLimit A f) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' (DirectLimit A f) (Algebra.linearMap k (DirectLimit A f))
        (FaithfulSMul.algebraMap_injective k (DirectLimit A f))
  have hstage : ∀ x : k' ⊗[k] DirectLimit A f, ∃ i z,
      Algebra.TensorProduct.map (AlgHom.id k' k') (DirectLimit.Algebra.of A f i) z = x := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, 0, by simp⟩
    · intro a b
      obtain ⟨i, b', hb'⟩ := DirectLimit.exists_eq_mk f b
      refine ⟨i, a ⊗ₜ[k] b', ?_⟩
      rw [Algebra.TensorProduct.map_tmul]
      change a ⊗ₜ[k] ⟦⟨i, b'⟩⟧ = a ⊗ₜ[k] b
      exact congrArg (fun z => a ⊗ₜ[k] z) hb'.symm
    · intro x y ihx ihy
      obtain ⟨i, xi, hxi⟩ := ihx
      obtain ⟨j, yj, hyj⟩ := ihy
      obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
      let xil := Algebra.TensorProduct.map
        (AlgHom.id k' k') (f i l hil) xi
      let yjl := Algebra.TensorProduct.map
        (AlgHom.id k' k') (f j l hjl) yj
      refine ⟨l, xil + yjl, ?_⟩
      rw [map_add]
      have hmap_i :
          (Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f l)).comp
            (Algebra.TensorProduct.map (AlgHom.id k' k') (f i l hil)) =
          Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f i) := by
        apply Algebra.TensorProduct.ext'
        intro a b
        simp
      have hmap_j :
          (Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f l)).comp
            (Algebra.TensorProduct.map (AlgHom.id k' k') (f j l hjl)) =
          Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f j) := by
        apply Algebra.TensorProduct.ext'
        intro a b
        simp
      have hxi' : Algebra.TensorProduct.map
          (AlgHom.id k' k') (DirectLimit.Algebra.of A f l) xil = x := by
        calc
          _ = ((Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f l)).comp
            (Algebra.TensorProduct.map (AlgHom.id k' k') (f i l hil))) xi := by rfl
          _ = (Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f i)) xi := by rw [hmap_i]
          _ = x := hxi
      have hyj' : Algebra.TensorProduct.map
          (AlgHom.id k' k') (DirectLimit.Algebra.of A f l) yjl = y := by
        calc
          _ = ((Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f l)).comp
            (Algebra.TensorProduct.map (AlgHom.id k' k') (f j l hjl))) yj := by rfl
          _ = (Algebra.TensorProduct.map (AlgHom.id k' k')
            (DirectLimit.Algebra.of A f j)) yj := by rw [hmap_j]
          _ = y := hyj
      rw [hxi', hyj']
  apply (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).2
  intro e he
  obtain ⟨i, z, hz⟩ := hstage e
  have : Nontrivial (k' ⊗[k] A i) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' (A i) (Algebra.linearMap k (A i))
        (FaithfulSMul.algebraMap_injective k (A i))
  let φ : k' ⊗[k] A i →ₐ[k'] k' ⊗[k] DirectLimit A f :=
    Algebra.TensorProduct.map (AlgHom.id k' k') (DirectLimit.Algebra.of A f i)
  have hxy : φ (z * z) = φ z := by
    rw [map_mul, hz, he.eq]
  have hstable : ∃ j hij, Algebra.TensorProduct.map
      (AlgHom.id k' k') (f i j hij) (z * z) =
      Algebra.TensorProduct.map (AlgHom.id k' k') (f i j hij) z := by
    let _ : DirectedSystem A (fun i j h => (f i j h).toLinearMap) :=
      { map_self := by
          intro i x
          change f i i le_rfl x = x
          exact DirectedSystem.map_self (f := fun i j h => f i j h) x
        map_map := by
          intro k j i hij hjk x
          change f j k hjk (f i j hij x) = f i k (hij.trans hjk) x
          exact DirectedSystem.map_map (f := fun i j h => f i j h) hij hjk x }
    let eA : Module.DirectLimit A (fun i j h => (f i j h).toLinearMap) ≃ₗ[k]
        DirectLimit A f :=
      Module.DirectLimit.linearEquiv A (fun i j h => (f i j h).toLinearMap)
    let E : k' ⊗[k] DirectLimit A f ≃ₗ[k]
        Module.DirectLimit (fun i => k' ⊗[k] A i)
          (fun i j h => LinearMap.lTensor k' (f i j h).toLinearMap) :=
      (TensorProduct.congr (LinearEquiv.refl k k') eA.symm).trans
        (TensorProduct.directLimitRight
          (fun i j h => (f i j h).toLinearMap) k')
    have heA (b : A i) :
        eA.symm (DirectLimit.Algebra.of A f i b) =
          Module.DirectLimit.of k ι A
            (fun i j h => (f i j h).toLinearMap) i b := by
      change eA.symm ⟦⟨i, b⟩⟧ = _
      exact Module.DirectLimit.linearEquiv_symm_mk _ _
    have hstage (q : k' ⊗[k] A i) :
        E (φ q) = Module.DirectLimit.of k ι
          (fun i => k' ⊗[k] A i)
          (fun i j h => LinearMap.lTensor k' (f i j h).toLinearMap) i q := by
      refine TensorProduct.induction_on q ?_ ?_ ?_
      · simp [E, φ, eA, DirectLimit.Algebra.of]
      · intro a b
        simp only [E, LinearEquiv.trans_apply, φ,
          TensorProduct.congr_tmul, Algebra.TensorProduct.map_tmul]
        rw [heA b]
        exact TensorProduct.directLimitRight_tmul_of
          (fun i j h => (f i j h).toLinearMap) k' a b
      · intro q₁ q₂ hq₁ hq₂
        simp only [map_add]
        rw [hq₁, hq₂]
    have hxy' := congrArg E hxy
    rw [hstage (z * z), hstage z] at hxy'
    obtain ⟨j, hij, hstageeq⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy'
    refine ⟨j, hij, ?_⟩
    change (LinearMap.lTensor k' (f i j hij).toLinearMap) (z * z) =
      (LinearMap.lTensor k' (f i j hij).toLinearMap) z
    exact hstageeq
  obtain ⟨j, hij, hzj_eq⟩ := hstable
  let zj := Algebra.TensorProduct.map (AlgHom.id k' k') (f i j hij) z
  have hzj : IsIdempotentElem zj := by
    change zj * zj = zj
    rw [← map_mul]
    exact hzj_eq
  have : Nontrivial (k' ⊗[k] A j) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' (A j) (Algebra.linearMap k (A j))
        (FaithfulSMul.algebraMap_injective k (A j))
  let φj : k' ⊗[k] A j →ₐ[k'] k' ⊗[k] DirectLimit A f :=
    Algebra.TensorProduct.map (AlgHom.id k' k') (DirectLimit.Algebra.of A f j)
  have hφstage_map :
      φj.comp (Algebra.TensorProduct.map (AlgHom.id k' k') (f i j hij)) = φ := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [φj, φ]
  have hφstage : φj zj = φ z := by
    calc
      φj zj = (φj.comp
        (Algebra.TensorProduct.map (AlgHom.id k' k') (f i j hij))) z := rfl
      _ = φ z := by rw [hφstage_map]
  rcases (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).1
      ((isGeometricallyConnected_iff_finiteSeparable
        (k := k) (S := A j)).1 (hA j) k') zj hzj with hzero | hone
  · left
    calc
      e = φ z := hz.symm
      _ = φj zj := hφstage.symm
      _ = φj 0 := congrArg φj hzero
      _ = 0 := map_zero φj
  · right
    calc
      e = φ z := hz.symm
      _ = φj zj := hφstage.symm
      _ = φj 1 := congrArg φj hone
      _ = 1 := map_one φj

/-! ## Base change and connected components -/

/-- The map on idempotents induced by the canonical inclusion of the left
tensor factor. -/
def tensorLeftIdempotentMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] :
    {e : R // IsIdempotentElem e} →
      {e : R ⊗[k] S // IsIdempotentElem e} :=
  fun e =>
    ⟨Algebra.TensorProduct.includeLeftRingHom e,
      e.property.map Algebra.TensorProduct.includeLeftRingHom⟩

/-- Tensoring with a nonzero geometrically connected algebra preserves the
idempotents and connected components of the other algebra. -/
theorem geometricallyConnected_baseChange_idempotents_bijective
    {k : Type u} {R : Type w} {S : Type v} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Nontrivial S]
    (hS : IsGeometricallyConnected.{u, v, w} k S) :
    Function.Bijective
      (tensorLeftIdempotentMap (k := k) (R := R) (S := S)) := by
  sorry

/-- Tensoring with a nonzero geometrically connected algebra preserves the
connected components of the other algebra. -/
theorem geometricallyConnected_baseChange_components_bijective
    {k : Type u} {R : Type w} {S : Type v} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Nontrivial S]
    (hS : IsGeometricallyConnected.{u, v, w} k S) :
    Function.Bijective
      ((PrimeSpectrum.continuous_comap
        (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[k] S)).connectedComponentsMap) := by
  sorry

/-- Tensoring with a nonzero geometrically connected algebra preserves the
idempotents and connected components of the other algebra. -/
theorem geometricallyConnected_baseChange_idempotents_and_components
    {k : Type u} {R : Type w} {S : Type v} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Nontrivial S]
    (hS : IsGeometricallyConnected.{u, v, w} k S) :
    Function.Bijective
        (tensorLeftIdempotentMap (k := k) (R := R) (S := S)) ∧
      Function.Bijective
        ((PrimeSpectrum.continuous_comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] S)).connectedComponentsMap) := by
  /-
  Proof roadmap.  Write `T := R ⊗[k] S` and
  `f : R →+* T := Algebra.TensorProduct.includeLeftRingHom`.

  * First prove `f = algebraMap R T` by extensionality and `simp`.  The
    `Nontrivial S` hypothesis makes the vector space `S` faithfully flat over
    `k`; the arbitrary-base-change instance in
    `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` then supplies
    `Module.FaithfullyFlat R T`.  Hence
    `PrimeSpectrum.comap_surjective_of_faithfullyFlat` (in
    `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`) gives surjectivity.
    Combine `RingHom.Flat.generalizingMap_comap` from
    `Mathlib.RingTheory.RingHom.Flat` with
    `PrimeSpectrum.isQuotientMap_of_generalizingMap` from
    `Mathlib.RingTheory.Spectrum.Prime.Topology` to get an
    `IsQuotientMap (PrimeSpectrum.comap f)` and thus an `IsCoinducing` map.
  * Prove every fiber connected.  For `p : PrimeSpectrum R`, give
    `p.asIdeal.ResidueField` its composite `k`-algebra structure and apply
    `hS` at this field (its universe is `w`, matching the explicit universe
    on `hS`).  Compose `PrimeSpectrum.preimageHomeomorphFiber R T p` with the
    spectrum homeomorphism induced by
    `Algebra.TensorProduct.cancelBaseChange k R
      p.asIdeal.ResidueField p.asIdeal.ResidueField S` to identify the
    set-theoretic fiber with
    `PrimeSpectrum (p.asIdeal.ResidueField ⊗[k] S)`, and transfer
    connectedness across that homeomorphism.
  * The component half is then exactly
    `Topology.IsCoinducing.connectedComponentsMap_bijective` from
    `Mathlib.Topology.Connected.TotallyDisconnected`, applied to the
    coinducing map and the connected-fiber result.  Normalize the proof term
    for continuity using proof irrelevance and the equality `f = algebraMap
    R T` before `simpa` closes the stated map.
  * For injectivity of `tensorLeftIdempotentMap`, use
    `FaithfulSMul.algebraMap_injective R T` and subtype extensionality.
  * For surjectivity, let `e : T` be idempotent and put
    `V := PrimeSpectrum.basicOpen e`.  It is clopen by
    `PrimeSpectrum.isClopen_iff`.  Connected fibers make `V` saturated: on
    each fiber its intersection is clopen, hence empty or the whole fiber.
    Set `U := PrimeSpectrum.comap f '' V`; saturation gives
    `(PrimeSpectrum.comap f) ⁻¹' U = V`.  The quotient-map equivalence
    `Topology.IsQuotientMap.isClopen_preimage` shows `U` is clopen.
  * Apply
    `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` (or the
    wrapper
    `Formalization.Books.Algebra.Unit21.existsUnique_idempotent_basicOpen_eq_of_isClopen`)
    to get
    an idempotent `a : R` with `U = PrimeSpectrum.basicOpen a`.  Pull this
    equality back using `PrimeSpectrum.comap_basicOpen`; comparison with
    `V` and `PrimeSpectrum.basicOpen_injOn_isIdempotentElem` yields
    `f a = e`.  Package `a` as the desired preimage under
    `tensorLeftIdempotentMap`.

  No `Nontrivial R` hypothesis is required: faithful flatness and the fiber
  argument also cover the zero ring, where both spectra and both component
  types are empty and both idempotent types are singletons.
  -/
  exact ⟨geometricallyConnected_baseChange_idempotents_bijective hS,
    geometricallyConnected_baseChange_components_bijective hS⟩

end

end Formalization.Books.Algebra.Unit48
