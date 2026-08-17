import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit70.BlowUpAlgebras
import Formalization.Books.MoreAlgebra.Unit08.FittingIdeals
import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More on Algebra, Chapter 27: Blowing up and flatness

This file formalizes the algebraic statements in the section
“Blowing up and flatness”.  Affine blowup charts and their power-torsion
ideals are the canonical constructions from Algebra, Chapter 70.  The
strict transform of a module is the quotient by the canonical scalar
power-torsion submodule from the Fitting-ideal chapter.
-/

namespace Formalization.Books.MoreAlgebra.Unit27

open Formalization.Books.Algebra.Unit50
open Formalization.Books.Algebra.Unit70
open Formalization.Books.Algebra.Unit78
open Formalization.Books.MoreAlgebra.Unit08
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Strict transforms -/

/-- The module obtained from `M` by base change to an affine blowup chart and
then quotienting by the power torsion of the chosen denominator.  This is the
source's strict transform; the explicit membership proof records that the
chosen denominator belongs to the blowup ideal. -/
abbrev strictTransformModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (a : R) (_ha : a ∈ I) : Type _ :=
  let T := affineBlowup I a
  let N := T ⊗[R] M
  let P : Submodule T N := scalarPowerTorsionSubmodule
    (R := T) (M := N) (algebraMap R T a)
  (@Submodule.hasQuotient T N inferInstance inferInstance inferInstance).Quotient P

/- The following ideal is the ring-theoretic version of the same construction
for an `R`-algebra.  It is the canonical `baseChangeTorsionIdeal` of
Algebra, Chapter 70, written with the existing `R`-algebra instance on `S`. -/
noncomputable def strictTransformTorsionIdeal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (a : R) : Ideal (S ⊗[R] affineBlowup I a) :=
  powerTorsionIdeal (S ⊗[R] affineBlowup I a)
    (algebraMap S (S ⊗[R] affineBlowup I a) (algebraMap R S a))

/- The quotient below is the strict transform of an algebra.  The module
variant uses the canonical extension-of-scalars tensor model described in
Algebra, Chapter 14, namely `(S ⊗[R] R') ⊗[S] M`. -/
abbrev strictTransformAlgebra
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (a : R) (_ha : a ∈ I) : Type _ :=
  (S ⊗[R] affineBlowup I a) ⧸ strictTransformTorsionIdeal (S := S) I a

/-- The strict transform of an `S`-module after the affine blowup of `R`.
The quotient is formed from the canonical base-change module and the
power-torsion of the image of the chosen denominator. -/
abbrev strictTransformModuleOver
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (I : Ideal R) (a : R) (_ha : a ∈ I) : Type _ :=
  let T := S ⊗[R] affineBlowup I a
  let N := T ⊗[S] M
  let P : Submodule T N := scalarPowerTorsionSubmodule
    (R := T) (M := N) (algebraMap S T (algebraMap R S a))
  (@Submodule.hasQuotient T N inferInstance inferInstance inferInstance).Quotient P

/- The quotient has its original `S ⊗[R] R'`-module structure.  Naming this
instance keeps typeclass inference stable through the reducible strict
transform abbreviation. -/
@[instance_reducible]
noncomputable def strictTransformModuleOverBaseModule
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (I : Ideal R) (a : R) (_ha : a ∈ I) :
    (let T := S ⊗[R] affineBlowup I a
     let N := T ⊗[S] M
     let P : Submodule T N := scalarPowerTorsionSubmodule
       (R := T) (M := N) (algebraMap S T (algebraMap R S a))
     Module T ((@Submodule.hasQuotient T N
       inferInstance inferInstance inferInstance).Quotient P)) := by
  let T := S ⊗[R] affineBlowup I a
  let N := T ⊗[S] M
  letI : Module T N := inferInstance
  let P : Submodule T N := scalarPowerTorsionSubmodule
    (R := T) (M := N) (algebraMap S T (algebraMap R S a))
  change Module T ((@Submodule.hasQuotient T N
    inferInstance inferInstance inferInstance).Quotient P)
  exact @Submodule.Quotient.module T N inferInstance inferInstance inferInstance P

/- The quotient by denominator power torsion is naturally a module over the
strict-transform algebra.  This interface is needed to state the source's
finite-presentation conclusion for the transformed `S`-module. -/
theorem strictTransformModuleOver_isTorsionBySet
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (I : Ideal R) (a : R) (ha : a ∈ I) :
    (let T := S ⊗[R] affineBlowup I a
     letI : Module T (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha) :=
       strictTransformModuleOverBaseModule (R := R) (S := S) (M := M) I a ha
     Module.IsTorsionBySet T
       (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha)
       (strictTransformTorsionIdeal (S := S) I a : Set T)) := by
  sorry

/-- The canonical quotient-ring action on the strict transform of an
`S`-module. -/
@[instance_reducible]
noncomputable def strictTransformModuleOverModule
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (I : Ideal R) (a : R) (ha : a ∈ I) :
    (let T := S ⊗[R] affineBlowup I a
     let Q := T ⧸ strictTransformTorsionIdeal (S := S) I a
     Module Q (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha)) := by
  let T := S ⊗[R] affineBlowup I a
  let N := T ⊗[S] M
  letI : Module T N := inferInstance
  let P : Submodule T N := scalarPowerTorsionSubmodule
    (R := T) (M := N) (algebraMap S T (algebraMap R S a))
  letI : Module T (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha) :=
    strictTransformModuleOverBaseModule (R := R) (S := S) (M := M) I a ha
  change Module (T ⧸ strictTransformTorsionIdeal (S := S) I a)
    ((@Submodule.hasQuotient T N
      inferInstance inferInstance inferInstance).Quotient P)
  exact (strictTransformModuleOver_isTorsionBySet
    (R := R) (S := S) (M := M) I a ha).module

/-! ## Flattening on an affine blowup -/

/- A valuation ring has a center on an `R`-algebra when the algebra admits a
local map to that valuation ring extending the given map into its fraction
field.  This is the source-facing center interface used for the affine chart
in the flattening statement. -/
def HasValuationCenter
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (A : ValuationSubring K) (B : Type*)
    [CommRing B] [Algebra R B]
    : Prop :=
  ∃ φ : B →+* A, IsLocalHom φ ∧
    ∀ r : R, ((φ (algebraMap R B r) : A) : K) = algebraMap R K r

/-- A weak flattening-by-affine-blowup theorem, with the four conclusions in
the source: finite generation of the blowup ideal, a valuation center, a
nonzero closed fibre, and flat/finitely presented strict transforms. -/
theorem flattenOnAffineBlowup
    {R S M K : Type*}
    [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    (A : ValuationSubring K)
    (hA : CenteredOn A (algebraMap R K).range) :
    ∃ (I : Ideal R) (a : R), ∃ ha : a ∈ I,
      I ≤ IsLocalRing.maximalIdeal R ∧
      a ≠ 0 ∧
      I.FG ∧
      HasValuationCenter (R := R) (K := K) A (affineBlowup I a) ∧
      (0 : fibreRingAtIdeal R (affineBlowup I a)
          (IsLocalRing.maximalIdeal R)) ≠
        (1 : fibreRingAtIdeal R (affineBlowup I a)
          (IsLocalRing.maximalIdeal R)) ∧
      (Module.Flat R (strictTransformAlgebra (S := S) I a ha) ∧
        Algebra.FinitePresentation R
          (strictTransformAlgebra (S := S) I a ha)) ∧
      (letI : Module (strictTransformAlgebra (S := S) I a ha)
          (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha) :=
        strictTransformModuleOverModule (R := R) (S := S) (M := M) I a ha
       letI : Module R (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha) :=
         Module.compHom (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha)
           (algebraMap R (strictTransformAlgebra (S := S) I a ha))
       Module.Flat R (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha) ∧
         Module.FinitePresentation (strictTransformAlgebra (S := S) I a ha)
           (strictTransformModuleOver (R := R) (S := S) (M := M) I a ha)) := by
  sorry

/-! ## Fitting ideals and affine blowups -/

/-- Blowing up the `k`th Fitting ideal makes that Fitting ideal the unit
ideal on the strict transform. -/
theorem blowupFittingIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) :
    ∀ (a : R) (ha : a ∈ fittingIdeal R M k),
      fittingIdeal
          (affineBlowup (fittingIdeal R M k) a)
          (strictTransformModule (M := M) (fittingIdeal R M k) a ha) k =
        ⊤ := by
  sorry

/-- If a finite module is free of rank `k` away from the vanishing locus of
its `k`th Fitting ideal, the corresponding affine blowup strict transform is
finite locally free of rank `k`. -/
theorem blowupFittingIdeal_locallyFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ)
    (hfree : ∀ p : PrimeSpectrum R,
      ¬ fittingIdeal R M k ≤ p.asIdeal →
        Nonempty
          (LocalizedModule.AtPrime p.asIdeal M ≃ₗ[Localization.AtPrime p.asIdeal]
            (Fin k →₀ Localization.AtPrime p.asIdeal))) :
    ∀ (a : R) (ha : a ∈ fittingIdeal R M k),
      FiniteLocallyFreeOfRank
        (affineBlowup (fittingIdeal R M k) a)
        (strictTransformModule (M := M) (fittingIdeal R M k) a ha) k := by
  sorry

/-! ## The module blowup theorem -/

/-- If `M` is finite locally free of rank `r` after inverting `f`, one can
choose a finitely generated ideal with the same vanishing locus as `f` such
that every affine blowup chart in that ideal has a strict transform locally
free of rank `r`. -/
theorem blowupModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : R) (r : ℕ)
    (hf : FiniteLocallyFreeOfRank
      (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ I : Ideal R,
      I.FG ∧
      SameVanishingLocus f I ∧
      ∀ (a : R) (ha : a ∈ I),
        FiniteLocallyFreeOfRank
          (affineBlowup I a)
          (strictTransformModule (M := M) I a ha) r := by
  sorry

/-!
## Coverage notes

The affine-chart presentation, localization, add-principal, and valuation
colimit assertions used in the source proofs are already represented by the
Algebra Chapter 70 declarations imported above.  The Fitting-ideal base-change,
principal-ideal, and local-freeness interfaces are imported from Chapter 8.
The presentations, exact sequences, filtered-colimit calculations, and local
relation computations displayed inside the source proofs are proof-local
scaffolding for the five declarations above, so they do not introduce further
public mathematical statements at this chapter boundary.
-/

end

end Formalization.Books.MoreAlgebra.Unit27
