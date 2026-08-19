import Formalization.Books.Algebra.Unit12.TensorProducts
import Formalization.Books.Algebra.Unit63
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Commutative Algebra, Chapter 65: relative assassin

The source works with subsets of spectra.  We use `PrimeSpectrum` points and the
exact-annihilator associated-prime set from Chapter 63.  The scalar-extension
orientation `N ⊗[R] M` keeps the `S`-action on the first tensor factor; it is
canonically equivalent to the source's displayed `M ⊗[R] N` orientation.
-/

namespace Formalization.Books.Algebra.Unit65

open Set
open scoped TensorProduct

noncomputable section

universe u v w z

/-! ## Scalar extension and fibres -/

/- The tensor product of an `S`-module with an `R`-algebra `A` is naturally a
   module over `S ⊗[R] A`.  Mathlib supplies the action once the commuting
   scalar actions are installed; this proposition is the only fibre-specific
   compatibility interface needed below. -/
theorem tensorProductScalar_smulCommClass
    {R S A N : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    letI : Module S (N ⊗[R] A) := TensorProduct.leftModule
    letI : Module A (N ⊗[R] A) :=
      Formalization.Books.Algebra.Unit12.tensorProductBModule
        R A N A
    SMulCommClass S A (N ⊗[R] A) := by
  letI : Module S (N ⊗[R] A) := TensorProduct.leftModule
  letI : Module A (N ⊗[R] A) :=
    Formalization.Books.Algebra.Unit12.tensorProductBModule R A N A
  refine ⟨?_⟩
  intro s a z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro n b
    change s • (TensorProduct.comm R N A).symm
        (a • (TensorProduct.comm R N A) (n ⊗ₜ[R] b)) =
      (TensorProduct.comm R N A).symm
        (a • (TensorProduct.comm R N A) ((s • n) ⊗ₜ[R] b))
    simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul']
    change s • (n ⊗ₜ[R] (a • b)) = (s • n) ⊗ₜ[R] (a • b)
    rfl
  · intro x y hx hy
    simp [smul_add, hx, hy]

/- Restriction of scalars along the displayed algebra map. -/
theorem inducedModule_isScalarTower
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] :
    letI : Module R N := Module.compHom N (algebraMap R S)
    IsScalarTower R S N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  exact ⟨fun r s n => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

/- The transported `A`-action on `N ⊗[R] A` is compatible with the base
   `R`-action. -/
theorem tensorProductScalar_isScalarTower_right
    {R S A N : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    letI : Module S (N ⊗[R] A) := TensorProduct.leftModule
    letI : Module A (N ⊗[R] A) :=
      Formalization.Books.Algebra.Unit12.tensorProductBModule
        R A N A
    IsScalarTower R A (N ⊗[R] A) := by
  letI : Module S (N ⊗[R] A) := TensorProduct.leftModule
  letI : Module A (N ⊗[R] A) :=
    Formalization.Books.Algebra.Unit12.tensorProductBModule R A N A
  refine ⟨?_⟩
  intro r a z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro n b
    change (TensorProduct.comm R N A).symm
        ((r • a) • (TensorProduct.comm R N A) (n ⊗ₜ[R] b)) =
      r • (TensorProduct.comm R N A).symm
        (a • (TensorProduct.comm R N A) (n ⊗ₜ[R] b))
    simp [Algebra.smul_def, TensorProduct.smul_tmul']
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_assoc]
  · intro x y hx hy
    simp [smul_add, hx, hy]

/- The canonical module structure on the base-changed module. -/
@[instance_reducible] noncomputable def tensorProductScalarModule
    {R S A N : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    Module (S ⊗[R] A) (N ⊗[R] A) := by
  letI : Module S (N ⊗[R] A) := TensorProduct.leftModule
  letI : Module A (N ⊗[R] A) :=
    Formalization.Books.Algebra.Unit12.tensorProductBModule R A N A
  letI : IsScalarTower R S (N ⊗[R] A) :=
    TensorProduct.isScalarTower_left
  letI : IsScalarTower R A (N ⊗[R] A) :=
    tensorProductScalar_isScalarTower_right
      (R := R) (S := S) (A := A) (N := N)
  letI : SMulCommClass S A (N ⊗[R] A) :=
    tensorProductScalar_smulCommClass (R := R) (S := S) (A := A) (N := N)
  exact TensorProduct.Algebra.module

/- The module in the quotient-ring half of the fibre diagram. -/
theorem relativeFiber_isTorsionBySet
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] p.asIdeal.ResidueField) :=
      TensorProduct.leftModule
    Module.IsTorsionBySet S (N ⊗[R] p.asIdeal.ResidueField)
      (p.asIdeal.map (algebraMap R S)) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
    inducedModule_isScalarTower (R := R) (S := S) (N := N)
  letI : Module S (N ⊗[R] p.asIdeal.ResidueField) :=
    TensorProduct.leftModule
  rw [Module.isTorsionBySet_iff_subseteq_ker_lsmul]
  refine (Ideal.map_le_iff_le_comap).2 ?_
  intro r hr
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro n k
    change (algebraMap R S r) • (n ⊗ₜ[R] k) = 0
    rw [TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul S]
    rw [TensorProduct.smul_tmul]
    rw [← IsScalarTower.algebraMap_smul p.asIdeal.ResidueField,
      Ideal.algebraMap_residueField_eq_zero.mpr hr, zero_smul]
    simp
  · intro x y hx hy
    change (algebraMap R S r) • (x + y) = 0
    change (algebraMap R S r) • x = 0 at hx
    change (algebraMap R S r) • y = 0 at hy
    simp [smul_add, hx, hy]

@[instance_reducible] noncomputable def relativeFiberQuotientModule
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    Module (S ⧸ p.asIdeal.map (algebraMap R S))
      (N ⊗[R] p.asIdeal.ResidueField) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
  letI : Module S (N ⊗[R] p.asIdeal.ResidueField) :=
    TensorProduct.leftModule
  exact (relativeFiber_isTorsionBySet (R := R) (S := S) (N := N) p).module

/- The associated-prime set of a fibre module, with its canonical fibre-ring
   module structure. -/
noncomputable def relativeFiberAssociatedPrimes
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    Set (PrimeSpectrum (S ⊗[R] p.asIdeal.ResidueField)) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
  letI : Module (S ⊗[R] p.asIdeal.ResidueField)
      (N ⊗[R] p.asIdeal.ResidueField) :=
    tensorProductScalarModule (R := R) (S := S)
      (A := p.asIdeal.ResidueField) (N := N)
  exact Formalization.Books.Algebra.Unit63.associatedPrimes
    (S ⊗[R] p.asIdeal.ResidueField)
    (N ⊗[R] p.asIdeal.ResidueField)

noncomputable def relativeFiberAssociatedPrimesImage
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    Set (PrimeSpectrum S) :=
  PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom :
        S →+* S ⊗[R] p.asIdeal.ResidueField) ''
    relativeFiberAssociatedPrimes (R := R) (S := S) (N := N) p

/-! ## The six sets -/

/- `A`: the associated primes in the fibre over the contraction of `q`. -/
def relativeAssassinA
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
  exact {q |
    letI : Module S
        (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) :=
      TensorProduct.leftModule
    q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)}

/- `A'`: the image of the associated-prime set of the fibre ring. -/
def relativeAssassinA'
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) := by
  exact {q |
    ∃ p : PrimeSpectrum R,
      p = PrimeSpectrum.comap (algebraMap R S) q ∧
        q ∈ relativeFiberAssociatedPrimesImage
          (R := R) (S := S) (N := N) p}

/- `A_fin`: use the contraction of `q` as the prime defining `N / pN`. -/
def relativeAssassinAFin
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  {q |
    q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes S
      (N ⧸
        ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map
          (algebraMap R S) • (⊤ : Submodule S N)))}

/- `A'_fin`: allow any prime of `R` in the quotient construction. -/
def relativeAssassinAFin'
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  {q |
    ∃ p : PrimeSpectrum R,
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⧸
          (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))}

/- `B`: allow an arbitrary `R`-module witness.  The universe parameter `z`
   makes the declaration reusable at any chosen module universe. -/
def relativeAssassinB
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
  exact {q |
    ∃ (M : Type z) (hMadd : AddCommGroup M) (hMmodule : Module R M),
      letI := hMadd
      letI := hMmodule
      letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⊗[R] M)}

/- `B_fin`: the witness in `B` is required to be finite over `R`. -/
def relativeAssassinBFin
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
  exact {q |
    ∃ (M : Type z) (hMadd : AddCommGroup M) (hMmodule : Module R M)
        (hMfinite : Module.Finite R M),
      letI := hMadd
      letI := hMmodule
      letI := hMfinite
      letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⊗[R] M)}

/- The source names `A` itself as the relative assassin. -/
def relativeAssassin
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Set (PrimeSpectrum S) :=
  relativeAssassinA (R := R) (S := S) (N := N)

/- The source warns that this notion is most useful when the fibre rings are
   Noetherian (for example, for a finite-type ring map).  This is a scope
   warning rather than an extra hypothesis on the definition. -/

/-! ## Comparing the six sets -/

theorem relativeAssassinA_eq_A'
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] :
    relativeAssassinA (R := R) (S := S) (N := N) =
      relativeAssassinA' (R := R) (S := S) (N := N) := by
  sorry

theorem compare_relative_assassins
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] :
    relativeAssassinAFin (R := R) (S := S) (N := N) ⊆
        relativeAssassinA (R := R) (S := S) (N := N) ∧
      relativeAssassinBFin (R := R) (S := S) (N := N) ⊆
        relativeAssassinB (R := R) (S := S) (N := N) ∧
      relativeAssassinAFin (R := R) (S := S) (N := N) ⊆
        relativeAssassinAFin' (R := R) (S := S) (N := N) ∧
      relativeAssassinAFin' (R := R) (S := S) (N := N) ⊆
        relativeAssassinBFin (R := R) (S := S) (N := N) ∧
      relativeAssassinA (R := R) (S := S) (N := N) ⊆
        relativeAssassinB (R := R) (S := S) (N := N) := by
  sorry

theorem relative_assassins_eq_of_noetherian_target
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [IsNoetherianRing S] :
    relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinAFin (R := R) (S := S) (N := N) ∧
      relativeAssassinB (R := R) (S := S) (N := N) =
        relativeAssassinBFin (R := R) (S := S) (N := N) := by
  sorry

theorem relative_assassins_eq_of_flat
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinAFin (R := R) (S := S) (N := N) ∧
      relativeAssassinAFin (R := R) (S := S) (N := N) =
        relativeAssassinAFin' (R := R) (S := S) (N := N) ∧
      relativeAssassinB (R := R) (S := S) (N := N) =
        relativeAssassinBFin (R := R) (S := S) (N := N) := by
  sorry

theorem relative_assassins_all_eq_of_noetherian_of_flat
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [IsNoetherianRing R]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinA' (R := R) (S := S) (N := N) ∧
      relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinAFin (R := R) (S := S) (N := N) ∧
      relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinAFin' (R := R) (S := S) (N := N) ∧
      relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinB (R := R) (S := S) (N := N) ∧
      relativeAssassinA (R := R) (S := S) (N := N) =
        relativeAssassinBFin (R := R) (S := S) (N := N) := by
  sorry

/-! ## Bourbaki's lemma and its fibre form -/

theorem bourbaki_associatedPrimes
    {R : Type u} {S : Type v} {M : Type z} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
    (⋃ p : {p : PrimeSpectrum R //
        p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M},
      Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⧸ (p.1.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] M) := by
  sorry

theorem bourbaki_associatedPrimes_eq_of_noetherian
    {R : Type u} {S : Type v} {M : Type z} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
    (⋃ p : {p : PrimeSpectrum R //
        p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M},
      Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⧸ (p.1.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))) =
      Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] M) := by
  sorry

theorem post_bourbaki_associatedPrimes
    {R : Type u} {S : Type v} {K : Type z} {N : Type w}
    [CommRing R] [CommRing S] [Field K] [IsDomain R]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] K) := TensorProduct.leftModule
    letI : Module (S ⊗[R] K) (N ⊗[R] K) :=
      tensorProductScalarModule (R := R) (S := S) (A := K) (N := N)
    Formalization.Books.Algebra.Unit63.associatedPrimes S N =
        Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] K) ∧
      Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] K) =
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeLeftRingHom :
              S →+* S ⊗[R] K) ''
          Formalization.Books.Algebra.Unit63.associatedPrimes
            (S ⊗[R] K) (N ⊗[R] K) := by
  sorry

theorem bourbaki_associatedPrimes_fibres
    {R : Type u} {S : Type v} {M : Type z} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
    (⋃ p : {p : PrimeSpectrum R //
        p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M},
      relativeFiberAssociatedPrimesImage
        (R := R) (S := S) (N := N) p.1) ⊆
      Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] M) := by
  sorry

theorem bourbaki_associatedPrimes_fibres_eq_of_noetherian
    {R : Type u} {S : Type v} {M : Type z} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    (hN : letI : Module R N := Module.compHom N (algebraMap R S)
      Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] M) := TensorProduct.leftModule
    (⋃ p : {p : PrimeSpectrum R //
        p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M},
      relativeFiberAssociatedPrimesImage
        (R := R) (S := S) (N := N) p.1) =
      Formalization.Books.Algebra.Unit63.associatedPrimes S (N ⊗[R] M) := by
  sorry

/-! ## The fibre remark -/

theorem relativeFiber_associatedPrimes_quotient_eq
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] p.asIdeal.ResidueField) :=
      TensorProduct.leftModule
    letI : Module (S ⧸ p.asIdeal.map (algebraMap R S))
        (N ⊗[R] p.asIdeal.ResidueField) :=
      relativeFiberQuotientModule (R := R) (S := S) (N := N) p
    PrimeSpectrum.comap (Ideal.Quotient.mk (p.asIdeal.map (algebraMap R S))) ''
        Formalization.Books.Algebra.Unit63.associatedPrimes
          (S ⧸ p.asIdeal.map (algebraMap R S))
          (N ⊗[R] p.asIdeal.ResidueField) =
      Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⊗[R] p.asIdeal.ResidueField) := by
  sorry

theorem relative_assassin_fibre_remark
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] (p : PrimeSpectrum R) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N :=
      inducedModule_isScalarTower (R := R) (S := S) (N := N)
    letI : Module S (N ⊗[R] p.asIdeal.ResidueField) :=
      TensorProduct.leftModule
    letI : Module (S ⧸ p.asIdeal.map (algebraMap R S))
        (N ⊗[R] p.asIdeal.ResidueField) :=
      relativeFiberQuotientModule (R := R) (S := S) (N := N) p
    Formalization.Books.Algebra.Unit63.associatedPrimes S
          (N ⊗[R] p.asIdeal.ResidueField) =
        PrimeSpectrum.comap
            (Ideal.Quotient.mk (p.asIdeal.map (algebraMap R S))) ''
          Formalization.Books.Algebra.Unit63.associatedPrimes
            (S ⧸ p.asIdeal.map (algebraMap R S))
            (N ⊗[R] p.asIdeal.ResidueField) ∧
      Formalization.Books.Algebra.Unit63.associatedPrimes S
          (N ⊗[R] p.asIdeal.ResidueField) =
        relativeFiberAssociatedPrimesImage
          (R := R) (S := S) (N := N) p := by
  sorry

end

end Formalization.Books.Algebra.Unit65
