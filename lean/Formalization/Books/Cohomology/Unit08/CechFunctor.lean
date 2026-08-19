import Formalization.Books.Cohomology.Unit08.CechComplex
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Cohomology of Sheaves, Chapter 8: Čech cohomology as a presheaf functor

The Čech constructions in this file are deliberately presheaf constructions.
The exactness and derived-functor assertions therefore have presheaves as
their source; applying them to sheaves without an additional sheafification
or acyclicity hypothesis would be incorrect.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit12
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit08

/-! ## The additive and module-valued Čech functors -/

/-- The canonical additive Čech-complex functor on abelian presheaves. -/
noncomputable def cechAdditiveFunctor {X : TopCat.{v}} (𝒰 : CechOpenCover X) :
    AbelianPresheaf X ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  CategoryTheory.cechComplexFunctor 𝒰.memberOpen

/-- The additive Čech-complex functor on presheaves of modules, after
forgetting the module structures. -/
noncomputable def cechModuleUnderlyingFunctor {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) :
    PMod X.structureSheaf.obj ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  (PresheafOfModules.toPresheaf X.structureSheaf.obj) ⋙ cechAdditiveFunctor 𝒰

/-- The `p`th additive Čech cohomology functor. -/
noncomputable def cechCohomologyFunctor {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (p : ℕ) : AbelianPresheaf X ⥤ AddCommGrpCat.{v} :=
  cechAdditiveFunctor 𝒰 ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p

/-- The additive group underlying the module-valued Čech cohomology functor. -/
noncomputable def cechModuleCohomologyFunctor {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (p : ℕ) :
    PMod X.structureSheaf.obj ⥤ AddCommGrpCat.{v} :=
  cechModuleUnderlyingFunctor 𝒰 ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p

/-- The underlying Čech complex can be chosen with its natural module-valued
terms over the ring of sections on the covered open.  The comparison field
records that its underlying additive complex is the canonical one. -/
structure CechModuleComplexData {X : RingedSpace.{v}} (𝒰 : CechOpenCover X) where
  functor : PMod X.structureSheaf.obj ⥤
    CochainComplex (ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier))) ℕ
  term_iso : ∀ (F : PMod X.structureSheaf.obj) (p : ℕ),
    Nonempty
      ((forget₂ (ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier)))
        AddCommGrpCat).obj ((functor.obj F).X p) ≅
        (cechComplex 𝒰 F.presheaf).X p)

/-- Existence of the module structures on the Čech terms. -/
theorem exists_cechModuleComplexData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) : Nonempty (CechModuleComplexData 𝒰) := by
  sorry

/-- A chosen module-valued Čech complex. -/
noncomputable def cechModuleComplexData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) : CechModuleComplexData 𝒰 :=
  Classical.choice (exists_cechModuleComplexData 𝒰)

/-- The module-valued Čech cohomology functor supplied by the chosen complex. -/
noncomputable def cechModuleCohomologyFunctor' {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (p : ℕ) :
    PMod X.structureSheaf.obj ⥤
      ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier)) :=
  (cechModuleComplexData 𝒰).functor ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier))) (ComplexShape.up ℕ) p

/-! ## Exactness, δ-functors, and the representing complex -/

/-- The Čech complex is exact as a functor of presheaves. -/
theorem cechModuleUnderlyingFunctor_isExact {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) : IsExact (cechModuleUnderlyingFunctor 𝒰) := by
  sorry

/-- Čech cohomology, in all degrees, is a cohomological δ-functor on
abelian presheaves. -/
theorem cechCohomology_is_delta_functor {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) :
    Nonempty (CohomologicalDeltaFunctor (AbelianPresheaf X) AddCommGrpCat) := by
  sorry

/-- The module-valued version is a cohomological δ-functor as well. -/
theorem cechModuleCohomology_is_delta_functor {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) :
    Nonempty
      (CohomologicalDeltaFunctor (PMod X.structureSheaf.obj)
        (ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier)))) := by
  sorry

/-- A complex of extension-by-zero presheaves representing the Čech terms. -/
structure CechRepresentingComplexData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) where
  complex : CochainComplex (PMod X.structureSheaf.obj) ℕ
  term_projective : ∀ p : ℕ, Projective (complex.X p)
  extension_by_zero_adjunction : ∀ p : ℕ, Nonempty (∀ i : Fin (p + 1) → 𝒰.member,
    openModulePresheafExtensionByZero X (∏ᶜ 𝒰.memberOpen ∘ i) ⊣
      openModulePresheafRestrictionFunctor X (∏ᶜ 𝒰.memberOpen ∘ i))
  represents : ∀ (F : PMod X.structureSheaf.obj) (p : ℕ),
    Nonempty
      ((complex.X p ⟶ F) ≃
        (cechComplex 𝒰 F.presheaf).X p)

/-- The extension-by-zero construction supplies a representing complex for
the Čech cochains. -/
theorem exists_cechRepresentingComplexData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) : Nonempty (CechRepresentingComplexData 𝒰) := by
  sorry

/-- A chosen representing complex for the Čech cochains. -/
noncomputable def cechRepresentingComplexData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) : CechRepresentingComplexData 𝒰 :=
  Classical.choice (exists_cechRepresentingComplexData 𝒰)

/-- The chosen representing complex computes the Čech functor by Hom. -/
theorem cechRepresentingComplex_represents {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (F : PMod X.structureSheaf.obj) (p : ℕ) :
    Nonempty
      (((cechRepresentingComplexData 𝒰).complex.X p ⟶ F) ≃
        (cechComplex 𝒰 F.presheaf).X p) := by
  exact (cechRepresentingComplexData 𝒰).represents F p

/-- The Čech δ-functor is the right derived functor of its degree-zero
sections functor.  The universal property is represented using the
projective extension-by-zero complex above. -/
structure CechDerivedFunctorData {X : TopCat.{v}} (𝒰 : CechOpenCover X) where
  delta : CohomologicalDeltaFunctor (AbelianPresheaf X) AddCommGrpCat
  comparison : ∀ p : ℕ, delta.functor p ≅ cechCohomologyFunctor 𝒰 p
  universal : delta.IsUniversal

theorem cechCohomology_is_derived_functor {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) : Nonempty (CechDerivedFunctorData 𝒰) := by
  sorry

end Formalization.Books.Cohomology.Unit08
