import Formalization.Books.Injectives.Unit12.KInjectivesInGrothendieckCategories
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Formalization.Books.Injectives.Unit14

variable {C : Type u} [Category.{v} C] [Abelian C]

abbrev GabrielRing (U : C) : Type v := End U

def homModule (U A : C) : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ :=
  ModuleCat.of (GabrielRing U)ᵐᵒᵖ (U ⟶ A)

def homMap (U : C) {A B : C} (f : A ⟶ B) :
    homModule U A ⟶ homModule U B :=
  ModuleCat.ofHom {
    toFun := fun g => g ≫ f
    map_add' := by
      intro g h
      simp
    map_smul' := by
      intro r g
      change (r.unop ≫ g) ≫ f = r.unop ≫ (g ≫ f)
      simp [Category.assoc]
  }

@[simp]
theorem homMap_apply (U : C) {A B : C} (f : A ⟶ B) (g : U ⟶ A) :
    (homMap U f).hom g = g ≫ f := rfl

def homFunctor (U : C) : C ⥤ ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ where
  obj A := homModule U A
  map f := homMap U f
  map_id := by
    intro A
    apply ModuleCat.hom_ext
    dsimp [homMap, homModule]
    ext g
    change (g : U ⟶ A) ≫ 𝟙 A = (g : U ⟶ A)
    simp
  map_comp := by
    intro A B D f g
    apply ModuleCat.hom_ext
    dsimp [homMap, homModule]
    ext h
    change (h : U ⟶ A) ≫ (f ≫ g) = ((h : U ⟶ A) ≫ f) ≫ g
    simp [Category.assoc]

instance homFunctor_preservesZeroMorphisms (U : C) :
    (homFunctor U).PreservesZeroMorphisms where
  map_zero A B := by
    apply ModuleCat.hom_ext
    dsimp [homFunctor, homMap, homModule]
    ext g
    change (g : U ⟶ A) ≫ (0 : A ⟶ B) = 0
    simp

/-! ## The adjoint construction -/

section AdjointConstruction

variable [IsGrothendieckAbelian.{max u v} C]

/-- The coproduct of `I` copies of the chosen generator. -/
abbrev generatorCopower (U : C) (I : Type (max u v)) : C := ∐ fun _ : I => U

/-- The standard direct-sum/free module on a family of generators. -/
abbrev freeModule (R : Type v) [Ring R] (I : Type v) : ModuleCat.{v} R :=
  ModuleCat.of R (I →₀ R)

/-- A free presentation of a module by coproducts of the regular module. -/
structure FreePresentation (U : C) (M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ)
    where
  I : Type v
  J : Type v
  differential :
    freeModule ((GabrielRing U)ᵐᵒᵖ) J ⟶ freeModule ((GabrielRing U)ᵐᵒᵖ) I
  augmentation : freeModule ((GabrielRing U)ᵐᵒᵖ) I ⟶ M
  differential_augmentation : differential ≫ augmentation = 0
  exact :
    (ShortComplex.mk differential augmentation differential_augmentation).Exact
  augmentation_epi : Epi augmentation

/-- The exact sequence in a chosen free presentation, with its zero term
omitted as in the `ShortComplex` API. -/
def FreePresentation.sequence {U : C}
    {M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ} (P : FreePresentation U M) :
    ShortComplex (ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ) :=
  ShortComplex.mk P.differential P.augmentation P.differential_augmentation

omit [IsGrothendieckAbelian C] in
theorem FreePresentation.sequence_exact {U : C}
    {M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ} (P : FreePresentation U M) :
    P.sequence.Exact := P.exact

omit [IsGrothendieckAbelian C] in
theorem FreePresentation.augmentation_is_epimorphism {U : C}
    {M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ} (P : FreePresentation U M) :
    Epi P.augmentation := P.augmentation_epi

/-- Every module admits the free presentation used in the construction of `F`. -/
theorem exists_freePresentation (U : C)
    (M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ) :
    Nonempty (FreePresentation U M) := by
  sorry

/-- A selected free presentation, used by the source's tensor-style construction. -/
noncomputable def chosenFreePresentation (U : C)
    (M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ) : FreePresentation U M :=
  Classical.choice (exists_freePresentation U M)

/-- The cokernel object attached to a map between copowers of the generator. -/
noncomputable def generatorPresentationObject (U : C) {I J : Type (max u v)}
    (d : generatorCopower U J ⟶ generatorCopower U I) : C :=
  cokernel d

/-- The displayed presentation sequence for the cokernel construction. -/
noncomputable def generatorPresentationSequence (U : C) {I J : Type (max u v)}
    (d : generatorCopower U J ⟶ generatorCopower U I) : ShortComplex C :=
  ShortComplex.mk d (cokernel.π d) (cokernel.condition d)

/-- The cokernel presentation is exact at the middle term. -/
theorem generatorPresentationSequence_exact (U : C) {I J : Type (max u v)}
    (d : generatorCopower U J ⟶ generatorCopower U I) :
    (generatorPresentationSequence U d).Exact := by
  sorry

/-- The last map in the cokernel presentation is an epimorphism. -/
theorem generatorPresentationSequence_epi (U : C) {I J : Type (max u v)}
    (d : generatorCopower U J ⟶ generatorCopower U I) :
    Epi (cokernel.π d) := by
  infer_instance

/-- The source's omitted independence and functoriality argument for the
presentation construction is recorded as a left-adjoint package. -/
structure LeftAdjointData (U : C) where
  functor : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ ⥤ C
  adjunction : functor ⊣ homFunctor U

/-- The Hom functor associated to a generator has a left adjoint. -/
theorem exists_leftAdjoint (U : C) (hU : IsSeparator U) :
    Nonempty (LeftAdjointData U) := by
  sorry

/-- A selected left adjoint to the canonical Hom functor. -/
noncomputable def chosenLeftAdjoint (U : C) (hU : IsSeparator U) :
    LeftAdjointData U :=
  Classical.choice (exists_leftAdjoint U hU)

/-- The selected left adjoint functor. -/
noncomputable abbrev leftAdjointFunctor (U : C) (hU : IsSeparator U) :
    ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ ⥤ C :=
  (chosenLeftAdjoint U hU).functor

/-- The adjoint image of a map into `G(A)`. -/
def adjointMap (L : LeftAdjointData U) {M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ}
    {A : C} (f : M ⟶ (homFunctor U).obj A) : L.functor.obj M ⟶ A :=
  (L.adjunction.homEquiv M A).symm f

/-- The source's generator argument: a monomorphism into `G(A)` has a
monomorphic adjoint map. -/
theorem adjointMap_mono (U : C) (L : LeftAdjointData U)
    {M : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ} {A : C}
    (f : M ⟶ (homFunctor U).obj A) [Mono f] :
    Mono (adjointMap L f) := by
  sorry

end AdjointConstruction

/-! ## The Gabriel-Popescu theorem -/

section GabrielPopescuTheorem

variable [IsGrothendieckAbelian.{max u v} C]

/-- The complete ordinary Gabriel-Popescu package.  Right `End U`-modules are
represented by left modules over `(End U)ᵐᵒᵖ`, the canonical `ModuleCat` model. -/
structure GabrielPopescuData where
  U : C
  generator : IsSeparator U
  F : ModuleCat.{v} (GabrielRing U)ᵐᵒᵖ ⥤ C
  adjunction : F ⊣ homFunctor U
  chosen : F = leftAdjointFunctor U generator
  additive : F.Additive
  fullyFaithful : Nonempty (homFunctor U).FullyFaithful
  exact : Formalization.Books.Categories.Unit23.IsExact F

/-- The Hom functor preserves all existing limits, hence in particular
products and finite limits. -/
theorem homFunctor_preserves_limits (U : C) {J : Type w} [Category.{w} J]
    [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (homFunctor U) := by
  sorry

/-- In particular, the Hom functor is left exact. -/
theorem homFunctor_is_left_exact (U : C) :
    Formalization.Books.Categories.Unit23.IsLeftExact (homFunctor U) := by
  sorry

/-- The Gabriel-Popescu theorem for Grothendieck abelian categories. -/
theorem gabriel_popescu : Nonempty (GabrielPopescuData (C := C)) := by
  sorry

end GabrielPopescuTheorem

/-! ## Derived functors -/

section DerivedGabrielPopescu

variable [IsGrothendieckAbelian.{max u v} C]

/-- The derived-category data supplied by the Gabriel-Popescu theorem.  The
last field is the categorical form of `F ∘ RG = id` on `D(𝒜)`. -/
structure DerivedGabrielPopescuData (D : GabrielPopescuData (C := C))
    [HasDerivedCategory.{u} C]
    [HasDerivedCategory.{u} (ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ)] where
  RG : DerivedCategory C ⥤
    DerivedCategory (ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ)
  F : DerivedCategory (ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ) ⥤ DerivedCategory C
  rightDerivedComparison :
    (homFunctor D.U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ) ⟶
      DerivedCategory.Q (C := C) ⋙ RG
  rightDerived :
    RG.IsRightDerivedFunctor rightDerivedComparison
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  leftDerivedComparison :
    letI := D.additive
    DerivedCategory.Q (C := ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ) ⋙ F ⟶
      D.F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := C)
  leftDerived :
    letI := D.additive
    F.IsLeftDerivedFunctor leftDerivedComparison
        (HomologicalComplex.quasiIso (ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ)
          (ComplexShape.up ℤ))
  adjunction : F ⊣ RG
  fullyFaithful : Nonempty RG.FullyFaithful
  inverse : Nonempty (RG ⋙ F ≅ 𝟭 (DerivedCategory C))

/-- The derived Gabriel-Popescu statement: `RG` is fully faithful and the
underived left adjoint extends to the left adjoint `F` on derived categories. -/
theorem derived_gabriel_popescu (D : GabrielPopescuData (C := C))
    [HasDerivedCategory.{u} C]
    [HasDerivedCategory.{u} (ModuleCat.{v} (GabrielRing D.U)ᵐᵒᵖ)] :
    Nonempty (DerivedGabrielPopescuData D) := by
  sorry

end DerivedGabrielPopescu

end Formalization.Books.Injectives.Unit14
