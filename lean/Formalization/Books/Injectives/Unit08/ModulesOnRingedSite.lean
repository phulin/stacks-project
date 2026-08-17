import Formalization.Books.Homology.Unit27.Injectives
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.RingTheory.Flat.Basic

/-!
# Injectives, Chapter 8: Modules on a ringed site

The canonical sheaf and presheaf module categories are used throughout.  The
source's internal sheaf Hom with values in a chosen injective abelian sheaf is
recorded by `SheafDualData`: this is the one source-facing interface not yet
provided by Mathlib for sheaves of modules over a varying sheaf of rings.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit27

universe u

namespace Formalization.Books.Injectives.Unit08

/-! ## The injective abelian sheaf and the duality construction -/

/--
The chosen injective abelian-sheaf embedding from the local-generator
construction.  Its source stands for the displayed coproduct of the sheaves
`j_{U!} O_U / I`; the target is the chosen injective abelian sheaf.
-/
structure AbelianSheafInjectiveEmbedding
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) where
  source : Sheaf J AddCommGrpCat.{u}
  target : Sheaf J AddCommGrpCat.{u}
  hom : source ⟶ target
  hom_mono : Mono hom
  target_injective : Injective target

/-- The source-facing duality package `F ↦ SheafHom(F, J)`. -/
structure SheafDualData
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) where
  /-- The selected embedding of the local-generator abelian sheaf. -/
  injectiveEmbedding : AbelianSheafInjectiveEmbedding J
  /-- The contravariant internal-Hom dual, represented as a functor on the opposite category. -/
  dual : (SheafOfModules.{u} R)ᵒᵖ ⥤ SheafOfModules.{u} R
  /-- Evaluation into the double dual. -/
  evaluation : ∀ F : SheafOfModules.{u} R,
    F ⟶ dual.obj (op (dual.obj (op F)))
  /-- Naturality of evaluation. -/
  evaluation_naturality : ∀ {F G : SheafOfModules.{u} R} (f : F ⟶ G),
    f ≫ evaluation G = evaluation F ≫ dual.map (op (dual.map f.op))

/-!
The source calls the object below `SheafHom(F, J)`.  Mathlib currently exposes
the internal Hom of sheaves as a sheaf of types; its sections are canonically
the morphisms of sheaves.  The module-valued dual in `SheafDualData` is the
source's module refinement of this interface.
-/

noncomputable def internalSheafHom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{u} R) (G : Sheaf J AddCommGrpCat.{u}) :
    Sheaf J (Type u) :=
  CategoryTheory.sheafHom ((SheafOfModules.toSheaf R).obj F) G

noncomputable def internalSheafHomSectionsEquiv
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{u} R) (G : Sheaf J AddCommGrpCat.{u}) :
    (internalSheafHom F G).1.sections ≃
      ((SheafOfModules.toSheaf R).obj F ⟶ G) :=
  CategoryTheory.sheafHomSectionsEquiv ((SheafOfModules.toSheaf R).obj F) G

/-- The injective abelian sheaf selected by a duality package. -/
abbrev selectedInjectiveAbelianSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R) : Sheaf J AddCommGrpCat.{u} :=
  D.injectiveEmbedding.target

/-- The contravariant sheaf-module dual. -/
def sheafDual
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    (F : SheafOfModules.{u} R) : SheafOfModules.{u} R :=
  D.dual.obj (op F)

/-- The map on duals induced by a morphism of sheaf modules. -/
def sheafDualMap
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    sheafDual D G ⟶ sheafDual D F :=
  D.dual.map f.op

/-- The evaluation map `F ⟶ F^∨∨`. -/
def evaluationMap
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    (F : SheafOfModules.{u} R) :
    F ⟶ sheafDual D (sheafDual D F) :=
  D.evaluation F

theorem evaluationMap_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    f ≫ evaluationMap D G = evaluationMap D F ≫ sheafDualMap D (sheafDualMap D f) := by
  exact D.evaluation_naturality f

/-! ## The free flat resolution -/

/- The source's free Yoneda coproduct is the canonical presheaf model of
   `⊕_{U, s ∈ F(U)} j_{U!} O_U`.  The index `m : M.Elements` is precisely a
   pair consisting of an object and a section over that object. -/
noncomputable def freeYonedaCoproductMap
    {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) :
    M.freeYonedaCoproduct ⟶ N.freeYonedaCoproduct :=
  Sigma.desc fun m =>
    N.ιFreeYonedaCoproduct (N.elementsMk m.1 (f.app m.1 m.2))

@[reassoc (attr := simp)]
theorem freeYonedaCoproductMap_ι
    {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (m : M.Elements) :
    M.ιFreeYonedaCoproduct m ≫ freeYonedaCoproductMap f =
      N.ιFreeYonedaCoproduct (N.elementsMk m.1 (f.app m.1 m.2)) := by
  apply Sigma.ι_desc

theorem freeYonedaCoproductMap_id
    {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) :
    freeYonedaCoproductMap (𝟙 M) = 𝟙 M.freeYonedaCoproduct := by
  apply Sigma.hom_ext
  intro m
  rw [freeYonedaCoproductMap_ι]
  rfl

theorem freeYonedaCoproductMap_comp
    {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P) :
    freeYonedaCoproductMap (f ≫ g) =
      freeYonedaCoproductMap f ≫ freeYonedaCoproductMap g := by
  apply Sigma.hom_ext
  intro m
  rw [freeYonedaCoproductMap_ι, ← Category.assoc,
    freeYonedaCoproductMap_ι, freeYonedaCoproductMap_ι]
  rfl

/- The functorial version of the source's free construction. -/
noncomputable def freeYonedaCoproductFunctor
    {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} R where
  obj M := M.freeYonedaCoproduct
  map f := freeYonedaCoproductMap f
  map_id M := freeYonedaCoproductMap_id M
  map_comp f g := freeYonedaCoproductMap_comp f g

/- The free, sheafified module used for the source's functor `𝓕`. -/
noncomputable def flatResolutionFunctor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  SheafOfModules.forget R ⋙ freeYonedaCoproductFunctor R.obj ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

/-- The object part of the free flat resolution. -/
noncomputable def flatResolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) : SheafOfModules.{u} R :=
  (flatResolutionFunctor R).obj F

/-- The canonical map `𝓕(F) ⟶ F`. -/
noncomputable def flatResolutionCounitApp
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) :
    flatResolution R F ⟶ F := by
  change (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      F.val.freeYonedaCoproduct ⟶ F
  exact (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (PresheafOfModules.fromFreeYonedaCoproduct F.val)

/- The source's displayed surjection is the canonical free-module counit. -/
theorem flatResolutionCounitApp_epi
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) :
    Epi (flatResolutionCounitApp R F) := by
  sorry

/-- Naturality of the free-resolution counit. -/
theorem flatResolutionCounitApp_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    (flatResolutionFunctor R).map f ≫ flatResolutionCounitApp R G =
      flatResolutionCounitApp R F ≫ f := by
  sorry

/- The flatness assertion for a module over a commutative ring, with the
   commutative structure required to have the same semiring as the ring
   structure already carried by `RingCat`. -/
def IsPointwiseCommutativeRingedSite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Prop :=
  ∀ X : Cᵒᵖ, ∃ S : CommSemiring (R.obj.obj X),
    S.toSemiring = (inferInstance : Semiring (R.obj.obj X))

structure PointwiseFlatModule (R : RingCat.{u}) (M : ModuleCat.{u} R) where
  commSemiring : CommSemiring (R : Type u)
  commSemiring_toSemiring : commSemiring.toSemiring = (inferInstance : Semiring (R : Type u))
  module : @Module (R : Type u) (M : Type u) commSemiring.toSemiring
    M.isAddCommGroup.toAddCommMonoid
  module_compatibility : ∀ r m, module.smul r m = M.isModule.smul r m
  flat : @Module.Flat (R : Type u) (M : Type u) commSemiring
    M.isAddCommGroup.toAddCommMonoid module

/- The source's flatness assertion, checked on every section.  The module
   structure is already part of `SheafOfModules`; `PointwiseFlatModule` only
   records the commutative semiring required by Mathlib's flatness API. -/
def IsSectionwiseFlatModule
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) : Prop :=
  ∀ X : Cᵒᵖ, Nonempty (PointwiseFlatModule (R.obj.obj X) (M.val.obj X))

/-- The free resolution is flat. -/
theorem flatResolution_isSectionwiseFlatModule
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hR : IsPointwiseCommutativeRingedSite R)
    (F : SheafOfModules.{u} R) :
    IsSectionwiseFlatModule R (flatResolution R F) := by
  sorry

/-! ## Exact duality and the injective target -/

/-- Duality is exact, as in the source's `Hom(-, 𝓙)` lemma. -/
theorem sheafDual_isExact
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (D : SheafDualData R)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsExact D.dual := by
  sorry

/-- Evaluation into the double dual is a monomorphism. -/
theorem evaluationMap_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    (F : SheafOfModules.{u} R) :
    Mono (evaluationMap D F) := by
  sorry

/-- The source's injective object `𝓙(F) = (𝓕(F^∨))^∨`. -/
noncomputable abbrev injectiveModule
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    SheafOfModules.{u} R :=
  sheafDual D (flatResolution R (sheafDual D F))

/-- Dualization of the free-resolution counit. -/
noncomputable def dualFlatResolutionMap
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    sheafDual D (sheafDual D F) ⟶ injectiveModule R D F :=
  D.dual.map (op (flatResolutionCounitApp R (sheafDual D F)))

/-- The dual of the free-resolution surjection is the canonical injection. -/
theorem dualFlatResolutionMap_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    Mono (dualFlatResolutionMap R D F) := by
  sorry

/-- The canonical monomorphism `F ⟶ 𝓙(F)`. -/
noncomputable def injectiveModuleEmbeddingApp
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    F ⟶ injectiveModule R D F :=
  evaluationMap D F ≫ dualFlatResolutionMap R D F

/-- The functorial object part of `F ↦ 𝓙(F)`. -/
noncomputable abbrev injectiveModuleFunctor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  D.dual.rightOp ⋙ (flatResolutionFunctor R).op ⋙ D.dual

theorem injectiveModuleFunctor_obj
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    (injectiveModuleFunctor R D).obj F = injectiveModule R D F := by
  rfl

theorem injectiveModule_isInjective
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    Injective (injectiveModule R D F) := by
  sorry

theorem injectiveModuleEmbeddingApp_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    Mono (injectiveModuleEmbeddingApp R D F) := by
  sorry

theorem injectiveModuleEmbeddingApp_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    f ≫ injectiveModuleEmbeddingApp R D G =
      injectiveModuleEmbeddingApp R D F ≫ (injectiveModuleFunctor R D).map f := by
  sorry

/-! ## Enough injectives and the presheaf corollary -/

/-- Existence of the source's chosen injective abelian sheaf and duality package. -/
theorem exists_sheafDualData
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Nonempty (SheafDualData R) := by
  sorry

/-- Sheaves of modules on a ringed site have functorial injective embeddings. -/
theorem sheavesOfModules_have_functorial_injective_embeddings
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    HasFunctorialInjectiveEmbeddings (C := SheafOfModules.{u} R) := by
  sorry

/-- The trivial topology used to identify presheaves with sheaves. -/
abbrev presheafTrivialTopology
    {C : Type u} [Category.{u} C] : GrothendieckTopology C := ⊥

/-- Every presheaf is a sheaf for the trivial topology. -/
theorem presheaf_isSheaf_for_trivialTopology
    {C : Type u} [Category.{u} C] {A : Type u} [Category A]
    (P : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (presheafTrivialTopology (C := C)) P := by
  exact Presheaf.isSheaf_bot P

/-- Presheaves of modules have functorial injective embeddings. -/
theorem presheafModules_have_functorial_injective_embeddings
    {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasFunctorialInjectiveEmbeddings (C := PresheafOfModules.{u} R) := by
  sorry

end Formalization.Books.Injectives.Unit08
