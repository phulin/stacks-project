import Formalization.Books.Algebra.Unit10.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Commutative Algebra, Chapter 11: Characterizing finite and finitely presented modules

The source characterizes finite and finitely presented modules by the behavior of
`Hom`.  The filtered diagrams and their colimits below use Mathlib's category of
modules and its canonical internal-hom functor.  A small interface records an
arbitrary filtered colimit together with the comparison to its target module.
-/

namespace Formalization.Books.Algebra.Unit11

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

universe u

/-! ## Filtered colimits and the Hom comparison map -/

/-- A filtered colimit presentation of an `R`-module object.

 The presentation field reuses Mathlib's canonical colimit-presentation
 interface; the filtered wrapper records the source's directedness hypothesis.
-/
structure FilteredModuleColimit {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) where
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  presentation : ColimitPresentation index N

/-- The module-valued functor `Hom_R(N, -)` used in the source. -/
abbrev moduleHomFunctor {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (Formalization.Books.Algebra.Unit10.internalHomFunctor (R := R)).obj
    (Opposite.op N)

/-- The canonical map
`colim Hom_R(N, M_i) → Hom_R(N, colim M_i)` for a filtered colimit presentation. -/
noncomputable def filteredModuleHomColimitMap
    {R : Type u} [CommRing R] {N : ModuleCat.{u} R}
    (C : FilteredModuleColimit N) :
    letI : Category.{u} C.index := C.indexCategory
    letI : HasColimit C.presentation.diag := C.presentation.hasColimit
    colimit (C.presentation.diag ⋙ moduleHomFunctor N) ⟶ (moduleHomFunctor N).obj N := by
  letI : Category.{u} C.index := C.indexCategory
  letI : IsFiltered C.index := C.indexFiltered
  letI : HasColimit C.presentation.diag := C.presentation.hasColimit
  let e : colimit C.presentation.diag ≅ N :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit C.presentation.diag)
      C.presentation.isColimit
  exact colimit.post C.presentation.diag (moduleHomFunctor N) ≫
    (moduleHomFunctor N).map e.hom

/-- A finite module is characterized by injectivity of `Hom` on every filtered
colimit, as in Lemma `lemma-characterize-finite-module-hom`. -/
theorem finite_iff_hom_filteredColimit_injective
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Module.Finite R N ↔
      ∀ (C : FilteredModuleColimit N),
        Function.Injective (filteredModuleHomColimitMap C).hom := by
  constructor
  · intro h C
    letI : Category.{u} C.index := C.indexCategory
    letI : IsFiltered C.index := C.indexFiltered
    letI : HasColimit C.presentation.diag := C.presentation.hasColimit
    have map_apply {A B : ModuleCat R} (f : A ⟶ B) (g : N ⟶ A) :
        (moduleHomFunctor N).map f g = g ≫ f := by
      change (ihom N).map f g = _
      exact ModuleCat.ihom_map_apply f g
    intro f g hfg
    obtain ⟨i, fi, hfi⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N))) f
    obtain ⟨j, gj, hgj⟩ :=
      Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget (ModuleCat R))
          (colimit.isColimit (C.presentation.diag ⋙ moduleHomFunctor N))) g
    sorry
  · intro h
    sorry

/-! ## Relations -/

/-- A relation among the entries of `x` is a coefficient vector whose linear
combination of those entries vanishes.  `Fin n` supplies the source's
`n`-element indexing, including the case `n = 0`. -/
def IsRelation {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : Fin n → M) (f : Fin n → R) : Prop :=
  ∑ i, f i • x i = 0

/-! ## Filtered colimits of finitely presented modules -/

/-- A filtered colimit presentation whose stages are finitely presented. -/
structure FilteredFinitelyPresentedModuleColimit
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    extends FilteredModuleColimit N where
  finitelyPresented : ∀ i, Module.FinitePresentation R (presentation.diag.obj i)

/-- Every module is a filtered colimit of finitely presented modules, as in
Lemma `lemma-module-colimit-fp`. -/
theorem exists_filteredColimit_finitelyPresented
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Nonempty (FilteredFinitelyPresentedModuleColimit N) := by
  sorry

/-! ## The finitely presented characterization -/

/-- A module is finitely presented exactly when `Hom` commutes with every
filtered colimit. -/
theorem finitePresentation_iff_hom_filteredColimit_bijective
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    Module.FinitePresentation R N ↔
      ∀ (C : FilteredModuleColimit N),
        Function.Bijective (filteredModuleHomColimitMap C).hom := by
  sorry

end Formalization.Books.Algebra.Unit11
