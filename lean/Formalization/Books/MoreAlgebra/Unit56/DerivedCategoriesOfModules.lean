import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Formalization.Books.MoreAlgebra.Unit53.AbelianCategoriesOfModules
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit31.KInjectiveComplexes
import Formalization.Books.Derived.Unit34.DerivedLimits
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 56: Derived categories of modules

The source uses `Mod_A`, `K(A)`, and `D(A)` for modules, the homotopy
category of complexes, and the derived category.  These declarations expose
Mathlib's canonical categorical constructions and record the product,
K-injective, derived-limit, and change-of-rings assertions from the section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit31
open Formalization.Books.Derived.Unit34
open Formalization.Books.MoreAlgebra.Unit53

universe w u

namespace Formalization.Books.MoreAlgebra.Unit56

/-! ## Module, homotopy, and derived categories -/

/- The source's `Mod_A` is the earlier chapter's canonical `ModuleCat` alias.
   Integer-indexed cochain complexes and their bounded subcategories likewise
   reuse the generic declarations from Derived Categories, Chapter 8. -/
abbrev Comp (A : Type u) [CommRing A] :=
  Formalization.Books.Derived.Unit08.Comp (moduleCategory A)

/-- The homotopy category `K(A)` of complexes of `A`-modules. -/
abbrev K (A : Type u) [CommRing A] :=
  Formalization.Books.Derived.Unit08.K (moduleCategory A)

/-- The unbounded derived category `D(A)`. -/
abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :=
  DerivedCategory (moduleCategory A)

/-- The bounded-below homotopy category `K⁺(A)`. -/
abbrev KPlus (A : Type u) [CommRing A] :=
  Formalization.Books.Derived.Unit08.KPlus (moduleCategory A)

/-- The bounded-above homotopy category `K⁻(A)`. -/
abbrev KMinus (A : Type u) [CommRing A] :=
  Formalization.Books.Derived.Unit08.KMinus (moduleCategory A)

/-- The bounded homotopy category `Kᵇ(A)`. -/
abbrev KBounded (A : Type u) [CommRing A] :=
  Formalization.Books.Derived.Unit08.KBounded (moduleCategory A)

/-- The bounded-below derived category `D⁺(A)`. -/
abbrev DPlus (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :=
  Formalization.Books.Derived.Unit11.DPlus (moduleCategory A)

/-- The bounded-above derived category `D⁻(A)`. -/
abbrev DMinus (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :=
  Formalization.Books.Derived.Unit11.DMinus (moduleCategory A)

/-- The bounded derived category `Dᵇ(A)`. -/
abbrev DBounded (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :=
  Formalization.Books.Derived.Unit11.DBounded (moduleCategory A)

/-- The quasi-isomorphism class in `K(A)` inverted to obtain `D(A)`. -/
abbrev quasiIsoInK (A : Type u) [CommRing A] : MorphismProperty (K A) :=
  HomotopyCategory.quasiIso (moduleCategory A) (.up ℤ)

/-- The localization functor from `K(A)` to `D(A)`. -/
noncomputable abbrev derivedQuotient (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] : K A ⥤ D A :=
  DerivedCategory.Qh

theorem homotopyCategory_is_triangulated (A : Type u) [CommRing A] :
    IsTriangulated (K A) := by
  infer_instance

theorem derivedCategory_is_triangulated (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :
    IsTriangulated (D A) := by
  infer_instance

theorem derivedCategory_is_localization (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :
    (derivedQuotient A).IsLocalization (quasiIsoInK A) := by
  exact Formalization.Books.Derived.Unit11.derivedCategory_is_localization
    (moduleCategory A)

/-! ## Products and K-injective resolutions -/

theorem moduleCategory_has_products (A : Type u) [CommRing A] :
    HasProducts.{u} (moduleCategory A) := by
  infer_instance

theorem moduleCategory_products_are_exact (A : Type u) [CommRing A] :
    AB4Star (moduleCategory A) := by
  infer_instance

instance moduleCategory_has_enough_injectives (A : Type u) [CommRing A] :
    EnoughInjectives (moduleCategory A) := by
  exact Formalization.Books.MoreAlgebra.Unit55.module_category_has_enough_injectives (R := A)

/- The source's existence statement is Mathlib's `HasKInjectiveResolution`,
   supplied for module complexes by the preceding derived-limit chapter once
   the module-category product and injective instances are installed. -/
theorem every_module_complex_has_kInjective_resolution
    (A : Type u) [CommRing A] :
    ∀ K : Comp A, HasKInjectiveResolution (moduleCategory A) K := by
  intro K
  exact Formalization.Books.Derived.Unit34.every_complex_has_kInjective_resolution K

/- The countable-product assertion is already proved for abelian categories
   with exact countable products; the module instances above supply those
   hypotheses. -/
theorem derivedCategory_has_countable_products
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :
    HasCountableProducts (D A) := by
  infer_instance

/- The source also records arbitrary products.  Mathlib's general derived
   category API does not provide this module-specific instance, so this is a
   chapter-facing existence interface; the later source proof is deferred. -/
instance derivedCategory_has_products
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :
    HasProducts (D A) := by
  sorry

abbrev DerivedInverseSystem (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)] :=
  Formalization.Books.Derived.Unit34.DerivedInverseSystem (D A)

abbrev IsDerivedLimit (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)]
    (F : DerivedInverseSystem A) (L : D A) : Prop :=
  Formalization.Books.Derived.Unit34.IsDerivedLimit F L

theorem every_module_derived_inverse_system_has_derived_limit
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)]
    (F : DerivedInverseSystem A) :
    ∃ L : D A, IsDerivedLimit A F L := by
  exact Formalization.Books.Derived.Unit34.exists_isDerivedLimit F

theorem derived_limit_unique_up_to_iso
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (moduleCategory A)]
    {F : DerivedInverseSystem A} {L L' : D A}
    (hL : IsDerivedLimit A F L) (hL' : IsDerivedLimit A F L') :
    Nonempty (L ≅ L') := by
  exact Formalization.Books.Derived.Unit34.derivedLimit_unique_up_to_iso hL hL'

/-! ## Change of rings and K-injectives -/

/- These are the degreewise change-of-scalars functors applied to complexes.
   `coextendScalars` is the canonical module object `Hom_A(B, -)`, so its
   homological-complex image is the source's `Hom_A(B, I^•)`. -/
noncomputable abbrev restrictScalarsComplex
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Comp S) : Comp R :=
  ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj I

noncomputable abbrev homOfScalarsComplex
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Comp A) : Comp B :=
  ((ModuleCat.coextendScalars f).mapHomologicalComplex (.up ℤ)).obj I

/-- Flat base change carries K-injective `S`-complexes to K-injective
`R`-complexes. -/
theorem isKInjective_of_flat_ring_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.Flat f) {I : Comp S} (hI : I.IsKInjective) :
    (restrictScalarsComplex f I).IsKInjective := by
  sorry

/-- Along an epimorphism of rings, K-injectivity of an `S`-complex after
restriction to `R` implies K-injectivity over `S`. -/
theorem isKInjective_of_ring_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [Epi (CommRingCat.ofHom f)] {I : Comp S}
    (hI : (restrictScalarsComplex f I).IsKInjective) :
    I.IsKInjective := by
  sorry

/-- Coextension of scalars computes `Hom_A(B, I^•)` and preserves
K-injectivity. -/
theorem homOfScalarsComplex_isKInjective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {I : Comp A} (hI : I.IsKInjective) :
    (homOfScalarsComplex f I).IsKInjective := by
  sorry

end Formalization.Books.MoreAlgebra.Unit56
