import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# More on Algebra, Chapter 25: Content ideals

The source's content ideal is represented by the predicate that an ideal is a
least member of the set of ideals carrying a specified module element.  The
flat intersection identity used below is already available as
`Formalization.Books.Algebra.Unit39.flat_intersect_ideals`.
-/

namespace Formalization.Books.MoreAlgebra.Unit25

universe u v

noncomputable section

/-! ## Content ideals -/

/-- The ideals of `A` whose scalar multiple of `M` contains `x`. -/
def contentIdeals
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x : M) : Set (Ideal A) :=
  {I | x ∈ I • (⊤ : Submodule A M)}

/-- `I` is the content ideal of `x` when it is least among the ideals whose
scalar multiple of `M` contains `x`. -/
def IsContentIdeal
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] (x : M) (I : Ideal A) : Prop :=
  IsLeast (contentIdeals x) I

/- The displayed equality
`I M ∩ I' M = (I ∩ I') M` is the existing theorem
`Formalization.Books.Algebra.Unit39.flat_intersect_ideals`. -/

/-! ## The lemmas -/

/-- A content ideal, when it exists for a flat module, is finitely generated. -/
theorem contentIdeal_finitelyGenerated
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    I.FG := by
  sorry

/-- The map induced by an `A`-linear map on the quotients by the maximal ideal. -/
def maximalIdealQuotientMap
    {A : Type u} {M N : Type v} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (u : M →ₗ[A] N) :
    (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) →ₗ[A]
      (N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))) :=
  Submodule.mapQ
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) u
    (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u)

/-- A map of flat modules over a local ring preserves the content ideal of an
element when its reduction modulo the maximal ideal is injective. -/
theorem contentIdeal_map_of_local
    {A : Type u} {M N : Type v} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module.Flat A N]
    (u : M →ₗ[A] N)
    (hu : Function.Injective (maximalIdealQuotientMap u))
    {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    IsContentIdeal (u x) I := by
  sorry

/-- Every element of a flat Mittag--Leffler module has a content ideal. -/
theorem exists_contentIdeal_of_flat_mittagLeffler
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    (hM : Formalization.Books.Algebra.Unit88.IsMittagLefflerModule
      (ModuleCat.of A M)) (x : M) :
    ∃ I : Ideal A, IsContentIdeal x I := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit25
