import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Flat.Basic
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

universe u v w

noncomputable section

/-! ## Tensor products over a separably closed field -/

/-- Over a separably closed field, the tensor product of two algebras with
connected spectra has connected spectrum. -/
theorem separablyClosed_tensorProduct_connected
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k]
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  sorry

/-! ## Geometric connectedness -/

/-- An algebra over a field is geometrically connected when every field base
change has connected spectrum. -/
def IsGeometricallyConnected (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

/-- Geometric connectedness can be tested after finite separable extensions of
the base field. -/
theorem isGeometricallyConnected_iff_finiteSeparable
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyConnected k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [Algebra.IsSeparable k k'],
        ConnectedSpace (PrimeSpectrum (k' ⊗[k] S)) := by
  sorry

/- The equivalence above records the source's following remark that it is
   enough to check finite separable field extensions separately. -/

/-- Over a separably closed field, geometric connectedness is ordinary
connectedness of the spectrum. -/
theorem isGeometricallyConnected_iff_connectedSpectrum
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    [IsSepClosed k] :
    IsGeometricallyConnected k R ↔ ConnectedSpace (PrimeSpectrum R) := by
  sorry

/-! ## Permanence properties -/

/-- Geometric connectedness descends to every `k`-subalgebra. -/
theorem isGeometricallyConnected_subalgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyConnected k S) :
    ∀ A : Subalgebra k S, IsGeometricallyConnected k A := by
  intro A
  apply (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := A)).2
  intro k' _ _ _ _
  have hconnS0 : ConnectedSpace (PrimeSpectrum S) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid k S).toRingEquiv).connectedSpace_iff.mp
      ((isGeometricallyConnected_iff_finiteSeparable (k := k) (S := S)).1 hS k)
  haveI : Nontrivial S := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    obtain ⟨p⟩ := hconnS0.toNonempty
    apply p.isPrime.ne_top
    ext x
    constructor
    · intro
      trivial
    · intro
      rw [Subsingleton.elim x 0]
      exact p.asIdeal.zero_mem
  haveI : Nontrivial A := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    have h01 : (0 : S) = 1 := by
      exact congrArg Subtype.val (Subsingleton.elim (0 : A) 1)
    exact zero_ne_one h01
  haveI : Nontrivial (k' ⊗[k] A) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' A (Algebra.linearMap k A) (FaithfulSMul.algebraMap_injective k A)
  let φ : k' ⊗[k] A →ₐ[k'] k' ⊗[k] S :=
    Algebra.TensorProduct.map (AlgHom.id k' k') A.val
  have hφ : Function.Injective φ := by
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  apply (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).2
  intro e he
  haveI : Nontrivial (k' ⊗[k] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' S (Algebra.linearMap k S) (FaithfulSMul.algebraMap_injective k S)
  have hconn : ConnectedSpace (PrimeSpectrum (k' ⊗[k] S)) :=
    (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := S)).1 hS k'
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
      IsGeometricallyConnected k A) :
    IsGeometricallyConnected k S := by
  have hfgBot : (⊥ : Subalgebra k S).FG := by
    refine ⟨∅, ?_⟩
    simp
  have hgeomBot : IsGeometricallyConnected k (⊥ : Subalgebra k S) :=
    hS ⊥ ((⊥ : Subalgebra k S).fg_iff_finiteType.mp hfgBot)
  have hconnBot : ConnectedSpace (PrimeSpectrum (⊥ : Subalgebra k S)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid k (⊥ : Subalgebra k S)).toRingEquiv).connectedSpace_iff.mp
      ((isGeometricallyConnected_iff_finiteSeparable
        (k := k) (S := (⊥ : Subalgebra k S))).1 hgeomBot k)
  haveI : Nontrivial (⊥ : Subalgebra k S) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    obtain ⟨p⟩ := hconnBot.toNonempty
    apply p.isPrime.ne_top
    ext x
    constructor
    · intro
      trivial
    · intro
      rw [Subsingleton.elim x 0]
      exact p.asIdeal.zero_mem
  haveI : Nontrivial S :=
    Function.Injective.nontrivial (α := (⊥ : Subalgebra k S)) (β := S)
      (f := fun x : (⊥ : Subalgebra k S) => (x : S)) Subtype.val_injective
  apply (isGeometricallyConnected_iff_finiteSeparable (k := k) (S := S)).2
  intro k' _ _ _ _
  haveI : Nontrivial (k' ⊗[k] S) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
      k k' S (Algebra.linearMap k S) (FaithfulSMul.algebraMap_injective k S)
  apply (Formalization.Books.Algebra.Unit21.primeSpectrum_connected_iff_no_nontrivial_idempotents _).2
  intro e he
  obtain ⟨C, hC, heC⟩ := exists_fg_and_mem_baseChange e
  haveI : Nontrivial C := by
    apply nontrivial_of_ne (0 : C) 1
    intro h
    apply zero_ne_one (α := S)
    exact congrArg (fun x : C => (x : S)) h
  have hgeomC : IsGeometricallyConnected k C :=
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
  haveI : Nontrivial (k' ⊗[k] C) :=
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
    (hA : ∀ i, IsGeometricallyConnected k (A i)) :
    IsGeometricallyConnected k (DirectLimit A f) := by
  classical
  have hAi_nontrivial : ∀ i, Nontrivial (A i) := by
    intro i
    have hconn : ConnectedSpace (PrimeSpectrum (A i)) :=
      (PrimeSpectrum.homeomorphOfRingEquiv
        (Algebra.TensorProduct.lid k (A i)).toRingEquiv).connectedSpace_iff.mp
        ((isGeometricallyConnected_iff_finiteSeparable
          (k := k) (S := A i)).1 (hA i) k)
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    obtain ⟨p⟩ := hconn.toNonempty
    apply p.isPrime.ne_top
    ext x
    constructor
    · intro
      trivial
    · intro
      rw [Subsingleton.elim x 0]
      exact p.asIdeal.zero_mem
  haveI : Nontrivial (DirectLimit A f) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    haveI := hAi_nontrivial i
    apply nontrivial_of_ne (0 : DirectLimit A f) 1
    intro hzero
    have hzero' : (⟦⟨i, (0 : A i)⟩⟧ : DirectLimit A f) =
        ⟦⟨i, (1 : A i)⟩⟧ := by
      simpa only [DirectLimit.zero_def i, DirectLimit.one_def i] using hzero
    obtain ⟨j, hij, hij', hval⟩ := Quotient.eq.mp hzero'
    exact (zero_ne_one : (0 : A j) ≠ 1) (by simpa using hval)
  apply (isGeometricallyConnected_iff_finiteSeparable
    (k := k) (S := DirectLimit A f)).2
  intro k' _ _ _ _
  haveI : Nontrivial (k' ⊗[k] DirectLimit A f) :=
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
  haveI : Nontrivial (k' ⊗[k] A i) :=
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
  haveI : Nontrivial (k' ⊗[k] A j) :=
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
theorem geometricallyConnected_baseChange_idempotents_and_components
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Nontrivial S]
    (hS : IsGeometricallyConnected k S) :
    Function.Bijective
        (tensorLeftIdempotentMap (k := k) (R := R) (S := S)) ∧
      Function.Bijective
        ((PrimeSpectrum.continuous_comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] S)).connectedComponentsMap) := by
  sorry

end

end Formalization.Books.Algebra.Unit48
