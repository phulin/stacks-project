import Formalization.Books.Algebra.Unit121.OrdersOfVanishing
import Formalization.Books.Algebra.Unit123.ZariskiMain
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 124: Applications of Zariski's Main Theorem
-/

namespace Formalization.Books.Algebra.Unit124

open Set
open scoped BigOperators TensorProduct

universe u v

noncomputable section

/- The preceding chapter defines order on fraction-field units.  This is the
   source-facing specialization to a nonzero element of the ring. -/
noncomputable def orderOfVanishingOfElement
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ∈ nonZeroDivisors R) : ℤ :=
  Formalization.Books.Algebra.Unit121.orderOfVanishing hnoetherian hdim
    (Formalization.Books.Algebra.Unit121.fractionUnit (R := R) (K := K) x 1 hx
      (nonZeroDivisors R).one_mem)

/-!
## One-dimensional quasi-finite extensions
-/

theorem quasi_finite_extension_dim_one
    {A B K L : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L]
    (f : A →+* B) (hinjective : Function.Injective f)
    (hfiniteType : RingHom.FiniteType f)
    (hcompat : (algebraMap K L).comp (algebraMap A K) =
      (algebraMap B L).comp f)
    (hKL : Function.Injective (algebraMap K L))
    (hdim : ringKrullDim A = 1) :
    ∃ hsemilocal : Finite (MaximalSpectrum B),
      letI := hsemilocal
      ∃ hmax : ∀ q : MaximalSpectrum B,
          IsLocalRing.maximalIdeal A = q.asIdeal.comap f,
        ∃ hlocal : ∀ q : MaximalSpectrum B,
            IsNoetherianRing
                (Formalization.Books.Algebra.Unit121.localizedFractionRingAt
                  (B := B) (L := L) q) ∧
              ringKrullDim
                  (Formalization.Books.Algebra.Unit121.localizedFractionRingAt
                    (B := B) (L := L) q) = 1,
          letI := Fintype.ofFinite (MaximalSpectrum B)
          ∀ (x : A) (_hxmem : x ∈ IsLocalRing.maximalIdeal A) (hx : x ≠ 0),
            let hxA : x ∈ nonZeroDivisors A :=
              mem_nonZeroDivisors_iff_ne_zero.mpr hx
            let hxB : f x ∈ nonZeroDivisors B :=
              mem_nonZeroDivisors_iff_ne_zero.mpr (by
                intro hfx
                apply hx
                apply hinjective
                simpa using hfx)
            let y : Lˣ :=
              Formalization.Books.Algebra.Unit121.fractionUnit
                (R := B) (K := L) (f x) 1 hxB
                (nonZeroDivisors B).one_mem
            ((Module.finrank K L : ℤ) *
                orderOfVanishingOfElement (R := A) (K := K)
                  (inferInstance : IsNoetherianRing A) hdim x hxA ≥
              ∑ q : MaximalSpectrum B,
                (Formalization.Books.Algebra.Unit121.residueFieldDegreeAt
                  f q (hmax q) : ℤ) *
                  Formalization.Books.Algebra.Unit121.localizedOrderOfVanishing
                    (B := B) (L := L) q (hlocal q).1 (hlocal q).2 y) ∧
              (Module.finrank K L : ℤ) *
                  orderOfVanishingOfElement (R := A) (K := K)
                    (inferInstance : IsNoetherianRing A) hdim x hxA =
                ∑ q : MaximalSpectrum B,
                  (Formalization.Books.Algebra.Unit121.residueFieldDegreeAt
                    f q (hmax q) : ℤ) *
                    Formalization.Books.Algebra.Unit121.localizedOrderOfVanishing
                      (B := B) (L := L) q (hlocal q).1 (hlocal q).2 y ↔
                RingHom.Finite f := by
  sorry

/-!
## Essentially finite-type local maps
-/

theorem essentially_finite_type_fibre_dim_zero
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hessentiallyFiniteType : RingHom.EssFiniteType f)
    (hresidue :
      letI : Algebra (IsLocalRing.maximalIdeal R).ResidueField
          (IsLocalRing.maximalIdeal S).ResidueField :=
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm).toAlgebra
      Module.Finite (IsLocalRing.maximalIdeal R).ResidueField
        (IsLocalRing.maximalIdeal S).ResidueField)
    (hfibre :
      ringKrullDim
          (S ⧸ (IsLocalRing.maximalIdeal R).map f) = 0) :
    letI : Algebra R S := f.toAlgebra
    ∃ (A : Subalgebra R S) (M : Submonoid A),
      Module.Finite R A ∧ IsLocalization M S := by
  sorry

/-!
## Completion at a quasi-finite prime
-/

theorem completion_at_quasi_finite_prime
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hqp : q.comap f = p)
    (hfiniteType : RingHom.FiniteType f)
    (hquasi :
      letI : Algebra R S := f.toAlgebra
      Algebra.QuasiFiniteAt R q) :
    letI : Algebra R S := f.toAlgebra
    ∃ (B : Type u) (hB : CommRing B)
        (hBalg : Algebra
          (Formalization.Books.Algebra.Unit97.primeCompletion R p inferInstance) B),
      letI : CommRing B := hB
      letI : Algebra
          (Formalization.Books.Algebra.Unit97.primeCompletion R p inferInstance) B := hBalg
      Nonempty
        (Formalization.Books.Algebra.Unit97.primeCompletion R p inferInstance ⊗[R] S ≃+*
          (Formalization.Books.Algebra.Unit97.primeCompletion S q inferInstance × B)) := by
  sorry

end

end Formalization.Books.Algebra.Unit124
