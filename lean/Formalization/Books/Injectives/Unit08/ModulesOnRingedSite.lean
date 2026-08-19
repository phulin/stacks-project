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

/- The source's pointwise commutativity hypothesis, with the commutative
   structure required to have the same semiring as the ring structure already
   carried by `RingCat`. -/
def IsPointwiseCommutativeRingedSite
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Prop :=
  ∀ X : Cᵒᵖ, ∃ S : CommSemiring (R.obj.obj X),
    S.toSemiring = (inferInstance : Semiring (R.obj.obj X))

/- The source's pointwise flatness assertion for a module over a commutative
   ring.  The module structure is already part of `ModuleCat`; this records the
   commutative semiring required by Mathlib's flatness API. -/
structure PointwiseFlatModule (R : RingCat.{u}) (M : ModuleCat.{u} R) where
  commSemiring : CommSemiring (R : Type u)
  commSemiring_toSemiring : commSemiring.toSemiring =
    (inferInstance : Semiring (R : Type u))
  module : @Module (R : Type u) (M : Type u) commSemiring.toSemiring
    M.isAddCommGroup.toAddCommMonoid
  module_compatibility : ∀ r m, module.smul r m = M.isModule.smul r m
  flat : @Module.Flat (R : Type u) (M : Type u) commSemiring
    M.isAddCommGroup.toAddCommMonoid module

def IsSectionwiseFlatPresheafModule
    {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{u} R) : Prop :=
  ∀ X : Cᵒᵖ, Nonempty (PointwiseFlatModule (R.obj X) (M.obj X))

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
  /-- Exactness of the internal-Hom dual in the abelian sheaf-module category. -/
  dual_isExact : ∀ [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}], IsExact dual
  /-- Evaluation is monic, as supplied by the chosen generating injective sheaf. -/
  evaluation_mono : ∀ F : SheafOfModules.{u} R, Mono (evaluation F)
  /-- The dual sends epimorphisms to monomorphisms in the weakly sheafified
      module category. -/
  dual_map_mono_of_epi : ∀ [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (f : F ⟶ G), Epi f → Mono (dual.map f.op)
  /-- The dual of the sheafification of a sectionwise flat presheaf module is
      injective.  This is the form used by the canonical free resolution: its
      presheaf is sectionwise flat, whereas its sheafification need not have
      flat modules of sections. -/
  dual_of_sectionwiseFlatSheafification_isInjective :
    ∀ [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      (M : PresheafOfModules.{u} R.obj),
      IsSectionwiseFlatPresheafModule R.obj M →
        Injective (dual.obj
          (op ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M)))

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
  constructor
  intro Z g h w
  apply (SheafOfModules.forget R).map_injective
  apply (cancel_epi (PresheafOfModules.fromFreeYonedaCoproduct F.val)).mp
  let ff : F.val.freeYonedaCoproduct ⟶
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj F :=
    PresheafOfModules.fromFreeYonedaCoproduct F.val
  have hw := w
  change
    ((PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
      (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
        ff ≫ g) =
      (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
        (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
          ff ≫ h at hw
  have heqF :
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F =
        PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj) := by
    apply Equiv.ext
    intro k
    exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply
      (𝟙 R.obj) k
  have hcounit :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F).symm
          ff =
        (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
          ff := by
    exact congrArg (fun e => e.symm
      ff) heqF
  have hwAdj :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F).symm
          ff ≫ g =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F).symm
          ff ≫ h := by
    simpa only [hcounit] using hw
  have hwAdj' := congrArg
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
      F.val.freeYonedaCoproduct Z) hwAdj
  rw [Adjunction.homEquiv_naturality_right] at hwAdj'
  rw [Adjunction.homEquiv_naturality_right] at hwAdj'
  have hcancel :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
      F.val.freeYonedaCoproduct F).apply_symm_apply ff
  simp only [hcancel] at hwAdj'
  change F.val.fromFreeYonedaCoproduct ≫
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).map g.val =
    F.val.fromFreeYonedaCoproduct ≫
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).map h.val
  convert hwAdj' using 1 <;> rfl

/-- Naturality of the free-resolution counit. -/
theorem flatResolutionCounitApp_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    (flatResolutionFunctor R).map f ≫ flatResolutionCounitApp R G =
      flatResolutionCounitApp R F ≫ f := by
  change (PresheafOfModules.sheafification (𝟙 R.obj)).map
      (freeYonedaCoproductMap f.val) ≫
      (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
        (P := G.val.freeYonedaCoproduct) (F := G) (𝟙 R.obj)).symm
        (PresheafOfModules.fromFreeYonedaCoproduct G.val) =
    (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
      (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
      (PresheafOfModules.fromFreeYonedaCoproduct F.val) ≫ f
  have hfree :
      freeYonedaCoproductMap f.val ≫
        PresheafOfModules.fromFreeYonedaCoproduct G.val =
      PresheafOfModules.fromFreeYonedaCoproduct F.val ≫ f.val := by
    apply Sigma.hom_ext
    intro m
    change F.val.ιFreeYonedaCoproduct m ≫ freeYonedaCoproductMap f.val ≫
        G.val.fromFreeYonedaCoproduct =
      F.val.ιFreeYonedaCoproduct m ≫ F.val.fromFreeYonedaCoproduct ≫ f.val
    rw [← Category.assoc, freeYonedaCoproductMap_ι,
      G.val.ι_fromFreeYonedaCoproduct]
    rw [← Category.assoc, F.val.ι_fromFreeYonedaCoproduct]
    apply PresheafOfModules.freeYonedaEquiv.injective
    rw [PresheafOfModules.freeYonedaEquiv_comp]
    simp only [PresheafOfModules.Elements.fromFreeYoneda,
      PresheafOfModules.freeYonedaEquiv]
    calc
      _ = (ConcreteCategory.hom (f.val.app m.fst)) m.snd :=
        (PresheafOfModules.freeHomEquiv.trans yonedaEquiv).apply_symm_apply _
      _ = _ := by
        exact (congrArg (ConcreteCategory.hom (f.val.app m.fst))
          ((PresheafOfModules.freeHomEquiv.trans yonedaEquiv).apply_symm_apply m.snd)).symm
  have heq (P : PresheafOfModules R.obj) (H : SheafOfModules R) :
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P H =
        PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := P) (F := H) (𝟙 R.obj) := by
    apply Equiv.ext
    intro g
    exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply (𝟙 R.obj) g
  have heqG := heq G.val.freeYonedaCoproduct G
  have heqF := heq F.val.freeYonedaCoproduct F
  have hGmap :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          G.val.freeYonedaCoproduct G).symm
          (PresheafOfModules.fromFreeYonedaCoproduct G.val) =
        (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := G.val.freeYonedaCoproduct) (F := G) (𝟙 R.obj)).symm
          (PresheafOfModules.fromFreeYonedaCoproduct G.val) := by
    exact congrArg (fun e => e.symm
      (PresheafOfModules.fromFreeYonedaCoproduct G.val)) heqG
  have hFmap :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F).symm
          (PresheafOfModules.fromFreeYonedaCoproduct F.val) =
        (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
          (PresheafOfModules.fromFreeYonedaCoproduct F.val) := by
    rw [heqF]
  have hAdj :=
    CategoryTheory.Adjunction.homEquiv_naturality_right_square
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))
      (freeYonedaCoproductMap f.val)
      (PresheafOfModules.fromFreeYonedaCoproduct G.val)
      (PresheafOfModules.fromFreeYonedaCoproduct F.val)
      f hfree
  have hleft :
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
          (freeYonedaCoproductMap f.val) ≫
        (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := G.val.freeYonedaCoproduct) (F := G) (𝟙 R.obj)).symm
          (PresheafOfModules.fromFreeYonedaCoproduct G.val) =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
          (freeYonedaCoproductMap f.val) ≫
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          G.val.freeYonedaCoproduct G).symm
          (PresheafOfModules.fromFreeYonedaCoproduct G.val) :=
    congrArg (fun k => (PresheafOfModules.sheafification (𝟙 R.obj)).map
      (freeYonedaCoproductMap f.val) ≫ k) hGmap.symm
  have hright :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          F.val.freeYonedaCoproduct F).symm
          (PresheafOfModules.fromFreeYonedaCoproduct F.val) ≫ f =
        (PresheafOfModules.sheafificationHomEquiv (R₀ := R.obj) (R := R)
          (P := F.val.freeYonedaCoproduct) (F := F) (𝟙 R.obj)).symm
          (PresheafOfModules.fromFreeYonedaCoproduct F.val) ≫ f :=
    congrArg (fun k => k ≫ f) hFmap
  exact hleft.trans (hAdj.trans hright)

/-- The free presheaf whose sheafification is the flat resolution is
sectionwise flat.  This is the hypothesis used by sheaf-flatness after
sheafification; it is deliberately not a claim that the modules of sections
of the associated sheaf are flat. -/
theorem flatResolution_isSectionwiseFlatModule
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hR : IsPointwiseCommutativeRingedSite R)
    (F : SheafOfModules.{u} R) :
    IsSectionwiseFlatPresheafModule R.obj F.val.freeYonedaCoproduct := by
  /-
  Proof roadmap.

  * Introduce `X : Cᵒᵖ` and choose `S` and `hS` from `hR X`.  After
    eliminating `hS`, the `CommSemiring` used by `Module.Flat` and the
    semiring already carried by `R.obj.obj X` are definitionally the same.
  * Evaluate the coproduct presentation
    `F.val.freeYonedaCoproduct = ∐ (PresheafOfModules.Elements.freeYoneda)`
    at `X`.  Use
    `PresheafOfModules.evaluation_preservesColimit` from
    `Mathlib/Algebra/Category/ModuleCat/Presheaf/Colimits.lean` to identify
    this value with the coproduct of the modules
    `(ModuleCat.free (R.obj.obj X)).obj (X.unop ⟶ m.1.unop)`, using
    `PresheafOfModules.freeObj_obj` from
    `Mathlib/Algebra/Category/ModuleCat/Presheaf/Free.lean`.
  * Define a second colimiting cofan with point
    `(ModuleCat.free (R.obj.obj X)).obj
      (Σ m : F.val.Elements, X.unop ⟶ m.1.unop)`.  Its leg at `m` is
    `ModuleCat.free.map` applied to `fun f => ⟨m, f⟩`.  Prove the universal
    property with `ModuleCat.freeHomEquiv`, `ModuleCat.free_hom_ext`, and
    `ModuleCat.freeDesc_apply` from
    `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`; a family of maps
    out of the summands is exactly a function on the sigma type.
  * Obtain the resulting module isomorphism with
    `IsColimit.coconePointUniqueUpToIso`.  Its target is the finsupp module
    on the displayed sigma type, hence is flat by `Module.Flat.finsupp` in
    `Mathlib/RingTheory/Flat/Basic.lean`; transport flatness back with
    `Module.Flat.of_linearEquiv` (use the module isomorphism's
    `toLinearEquiv`).
  * Package `S`, the transported module structure, the pointwise `rfl`
    compatibility, and the transported flatness proof into
    `Nonempty (PointwiseFlatModule _ _)`.
  -/
  sorry

/-! ## Exact duality and the injective target -/

/-- Duality is exact, as in the source's `Hom(-, 𝓙)` lemma. -/
theorem sheafDual_isExact
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (D : SheafDualData R)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsExact D.dual := by
  exact D.dual_isExact

/-- Evaluation into the double dual is a monomorphism. -/
theorem evaluationMap_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (D : SheafDualData R)
    (F : SheafOfModules.{u} R) :
    Mono (evaluationMap D F) := by
  exact D.evaluation_mono F

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
  exact D.dual_map_mono_of_epi (flatResolutionCounitApp R (sheafDual D F))
    (flatResolutionCounitApp_epi R (sheafDual D F))

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
    (hR : IsPointwiseCommutativeRingedSite R)
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    Injective (injectiveModule R D F) := by
  exact D.dual_of_sectionwiseFlatSheafification_isInjective _
    (flatResolution_isSectionwiseFlatModule R hR (sheafDual D F))

theorem injectiveModuleEmbeddingApp_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) (F : SheafOfModules.{u} R) :
    Mono (injectiveModuleEmbeddingApp R D F) := by
  let h₁ : Mono (evaluationMap D F) := evaluationMap_mono D F
  let h₂ : Mono (dualFlatResolutionMap R D F) :=
    dualFlatResolutionMap_mono R D F
  change Mono (evaluationMap D F ≫ dualFlatResolutionMap R D F)
  constructor
  intro Z g h w
  exact h₁.right_cancellation g h
    (h₂.right_cancellation (g ≫ evaluationMap D F)
      (h ≫ evaluationMap D F) (by simpa only [Category.assoc] using w))

theorem injectiveModuleEmbeddingApp_natural
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (D : SheafDualData R) {F G : SheafOfModules.{u} R} (f : F ⟶ G) :
    f ≫ injectiveModuleEmbeddingApp R D G =
      injectiveModuleEmbeddingApp R D F ≫ (injectiveModuleFunctor R D).map f := by
  let q : D.dual.obj (op G) ⟶ D.dual.obj (op F) := D.dual.map f.op
  let cF : (flatResolutionFunctor R).obj (D.dual.obj (op F)) ⟶
      D.dual.obj (op F) := flatResolutionCounitApp R (D.dual.obj (op F))
  let cG : (flatResolutionFunctor R).obj (D.dual.obj (op G)) ⟶
      D.dual.obj (op G) := flatResolutionCounitApp R (D.dual.obj (op G))
  let r : (flatResolutionFunctor R).obj (D.dual.obj (op G)) ⟶
      (flatResolutionFunctor R).obj (D.dual.obj (op F)) :=
    (flatResolutionFunctor R).map q
  have hnat : r ≫ cF = cG ≫ q := by
    dsimp [r, cF, cG, q]
    exact flatResolutionCounitApp_natural R (D.dual.map f.op)
  have hop : cF.op ≫ r.op = q.op ≫ cG.op := by
    simpa only [CategoryTheory.op_comp] using congrArg (fun k => k.op) hnat
  have hmap := congrArg D.dual.map hop.symm
  rw [D.dual.map_comp, D.dual.map_comp] at hmap
  have heval : f ≫ D.evaluation G = D.evaluation F ≫ D.dual.map q.op := by
    dsimp [q]
    exact D.evaluation_naturality f
  have hcanonical :
      f ≫ D.evaluation G ≫ D.dual.map cG.op =
        D.evaluation F ≫ D.dual.map cF.op ≫ D.dual.map r.op := by
    calc
      f ≫ D.evaluation G ≫ D.dual.map cG.op =
          (f ≫ D.evaluation G) ≫ D.dual.map cG.op := by rw [Category.assoc]
      _ = (D.evaluation F ≫ D.dual.map q.op) ≫ D.dual.map cG.op := by
        rw [heval]
      _ = D.evaluation F ≫ D.dual.map cF.op ≫ D.dual.map r.op := by
        rw [Category.assoc, hmap]
  exact (by
    change f ≫ D.evaluation G ≫
        D.dual.map (op (flatResolutionCounitApp R (D.dual.obj (op G)))) =
      (D.evaluation F ≫ D.dual.map
        (op (flatResolutionCounitApp R (D.dual.obj (op F))))) ≫
        D.dual.map ((flatResolutionFunctor R).map (D.dual.map f.op)).op
    exact hcanonical)

/-! ## Enough injectives and the presheaf corollary -/

/-- Existence of the source's chosen injective abelian sheaf and duality package. -/
theorem exists_sheafDualData
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hR : IsPointwiseCommutativeRingedSite R) :
    Nonempty (SheafDualData R) := by
  /-
  Proof roadmap (this is the missing internal-Hom boundary, not a choice-only
  consequence of the existing Mathlib API).

  1. Construct the generating abelian sheaf used in Stacks, tag 01DQ.  For
     every `U : C` and every subobject `I` of the sheaf-module version of
     `j_{U!} R|_U`, take its quotient, forget it with
     `SheafOfModules.toSheaf R`, and form their sigma coproduct `G` in
     `Sheaf J AddCommGrpCat.{u}`.  The useful existing building blocks are
     `J.overPullback AddCommGrpCat.{u} U` in
     `Mathlib/CategoryTheory/Sites/Over.lean`, `Sigma.ι`/`Sigma.desc`, and
     cokernels in the abelian instance from
     `Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.lean`.  A local
     `j_!` for sheaves of modules and its restriction adjunction still have
     to be defined here; `Over.lean` currently supplies only the pullback
     side.  Prove the generator lemma: for every nonzero section `s` of a
     sheaf module `F`, one quotient summand maps monomorphically to `F` and
     carries the class of `1` to `s`.

  2. Embed `G` monomorphically into an injective abelian sheaf `𝓙`, and set
     `injectiveEmbedding := ⟨G, 𝓙, i, inferInstance, inferInstance⟩`.
     This step needs the previous-section result
     `EnoughInjectives (Sheaf J AddCommGrpCat.{u})`; no such general-site
     instance is currently present in Mathlib or an earlier Injectives unit,
     so prove the local-generator injective presentation first (the
     topological-space-only analogue is
     `abelian_sheaves_have_enough_injectives` in
     `Formalization/Books/Injectives/Unit04/AbelianSheaves.lean`).  Once that
     instance exists, use its `InjectivePresentation` and the fields
     `f`, `mono`, and `injective`.

  3. Build a functor
     `dual : (SheafOfModules.{u} R)ᵒᵖ ⥤ SheafOfModules.{u} R` whose
     underlying sheaf of types is
     `CategoryTheory.sheafHom ((SheafOfModules.toSheaf R).obj F) 𝓙`.
     `CategoryTheory.sheafHom`, `sheafHomSectionsEquiv`, and the restriction
     formula through `J.overPullback AddCommGrpCat.{u} U` are in
     `Mathlib/CategoryTheory/Sites/SheafHom.lean`.  That file explicitly
     leaves bifunctoriality as TODO, so define the contravariant map locally
     by precomposition on every slice, prove its restriction naturality, and
     then equip those Hom groups with the pointwise additive structure and
     the `R.obj.obj U`-action.  Use the witnesses `hR U` (eliminating their
     `toSemiring` equalities before defining scalar multiplication) to make
     precomposition `R`-linear.  Before using Mathlib's commutative tensor
     API below, package the chosen structures into
     `Rcomm : Cᵒᵖ ⥤ CommRingCat.{u}` and prove
     `Rcomm ⋙ forget₂ CommRingCat RingCat = R.obj`; the maps are the same
     underlying ring homomorphisms, and their `map_mul` proofs respect the
     chosen structures after eliminating `hR U` and `hR V`.  Transport along
     this functor equality once, instead of repeatedly changing scalar
     structures objectwise.

  4. Define `evaluation F` on a local section `x` by
     `φ ↦ φ x`.  Prove `evaluation_naturality` by extensionality on each
     slice and `rfl` after unfolding precomposition.  Prove
     `evaluation_mono` with the generator lemma from step 1: for nonzero
     `x`, extend the corresponding nonzero map from its quotient summand
     across the monomorphism into `F` using
     `Injective.factorThru`; evaluation at the extension detects `x`.

  5. Prove `dual_isExact` from injectivity of `𝓙`.  Objectwise over each
     `U`, use the restriction/extension-by-zero adjunction from step 1 to
     show that `𝓙|_U` is injective, then identify sections of the dual with
     morphisms by `CategoryTheory.sheafHomSectionsEquiv`.  Assemble exactness
     in `SheafOfModules R` using the faithful exact functor
     `SheafOfModules.toSheaf R` and the abelian exactness API imported from
     `Formalization/Books/Categories/Unit23/ExactFunctors.lean`.
     `dual_map_mono_of_epi` then follows by applying this exactness to an
     epimorphism and passing to opposites; do not prove it independently by
     element chasing.

  6. For `dual_of_sectionwiseFlatSheafification_isInjective`, let `P` be the
     supplied sectionwise-flat presheaf.  Define the presheaf tensor using
     the pointwise construction in
     `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`, then
     sheafify it with `PresheafOfModules.sheafification (𝟙 R.obj)`.
     Sectionwise flatness makes the presheaf tensor functor preserve
     monomorphisms by `Module.Flat` at each `U`; exactness of sheafification
     promotes this to sheaf-flatness.  Finally identify
     `Hom(G, dual.obj (op (sheafification.obj P)))` with
     `Hom(toSheaf (G ⊗ sheafification.obj P), 𝓙)`.  The first functor is
     exact by flatness and the second by injectivity of `𝓙`, which is the
     `Injective` criterion for the required dual object.

  7. Fill the `SheafDualData` record with the constructions and claims from
     steps 2--6 and return it with `Nonempty.intro`.

  Failed shortcut to avoid: `internalSheafHomSectionsEquiv` only identifies
  global sections with morphisms; it does not provide the module-valued
  bifunctor, its map on morphisms, the tensor-Hom adjunction, or the generator
  argument needed for evaluation to be monic.
  -/
  sorry

/-- Sheaves of modules on a ringed site have functorial injective embeddings. -/
theorem sheavesOfModules_have_functorial_injective_embeddings
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hR : IsPointwiseCommutativeRingedSite R) :
    HasFunctorialInjectiveEmbeddings (C := SheafOfModules.{u} R) := by
  classical
  let D : SheafDualData R := Classical.choice (exists_sheafDualData R hR)
  let K : SheafOfModules R ⥤ Arrow (SheafOfModules R) := {
    obj := fun F => Arrow.mk (injectiveModuleEmbeddingApp R D F)
    map := fun f => {
      left := f
      right := (injectiveModuleFunctor R D).map f
      w := injectiveModuleEmbeddingApp_natural R D f
    }
    map_id := by
      intro F
      apply Arrow.hom_ext
      · rfl
      · exact (injectiveModuleFunctor R D).map_id F
    map_comp := by
      intro F G H f g
      apply Arrow.hom_ext
      · rfl
      · change (injectiveModuleFunctor R D).map (f ≫ g) =
          (injectiveModuleFunctor R D).map f ≫ (injectiveModuleFunctor R D).map g
        exact (injectiveModuleFunctor R D).map_comp f g
  }
  refine ⟨K, ?_, ?_, ?_⟩
  · rfl
  · intro F
    exact injectiveModuleEmbeddingApp_mono R D F
  · intro F
    exact injectiveModule_isInjective R hR D F

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
    {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    HasFunctorialInjectiveEmbeddings
      (C := PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) := by
  /-
  Proof roadmap.

  * Put `R₀ := R ⋙ forget₂ CommRingCat RingCat` and form the ring sheaf
    `Rsh : Sheaf (presheafTrivialTopology (C := C)) RingCat` as
    `⟨R₀, Presheaf.isSheaf_bot R₀⟩`.  The commutativity witness required by
    `sheavesOfModules_have_functorial_injective_embeddings Rsh` is
    `fun X => ⟨inferInstance, rfl⟩`.
  * Define the module analogue of `CategoryTheory.sheafBotEquivalence` from
    `Mathlib/CategoryTheory/Sites/Sheaf.lean`:
    `presheafModulesSheafBotEquivalence R₀ :
      SheafOfModules Rsh ≌ PresheafOfModules R₀`.
    Its functor is `SheafOfModules.forget Rsh`; its inverse sends `M` to
    `⟨M, Presheaf.isSheaf_bot M.presheaf⟩`.  Both unit and counit are
    componentwise identity isomorphisms, so the triangle fields are `rfl`.
  * Add a local helper saying that
    `HasFunctorialInjectiveEmbeddings` transports across an equivalence.
    Given `e : A ≌ B` and arrow functor `K : A ⥤ Arrow A`, first form
    `T := e.inverse ⋙ K ⋙ e.functor.mapArrow`.  Its arrows start at
    `e.functor.obj (e.inverse.obj B)`, so define the transported arrow at `B`
    by precomposing `T.obj B` with `e.counitIso.inv.app B`; define its map
    with left component `f`, right component `(T.map f).right`, and prove the
    square using `e.counitIso.inv.naturality_assoc f` followed by
    `(T.map f).w`.  The left projection is then definitionally `𝟭 B`.
    Monomorphisms are preserved by an equivalence and by composition with
    the counit isomorphism, and injective targets are preserved by
    `Functor.preservesInjectiveObjects_of_isEquivalence` from
    `Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean`.
    (Equivalently, specialize
    `adjoint_functorial_injective_embeddings` from
    `Formalization/Books/Homology/Unit29/AdjointFunctors.lean` to the two
    functors of `e`.)
  * Apply that helper to `presheafModulesSheafBotEquivalence R₀` and to
    `sheavesOfModules_have_functorial_injective_embeddings Rsh` with the
    commutativity witness from the first step.

  Do not try to apply the sheaf theorem directly to an arbitrary
  `RingCat`-valued presheaf: the endofunctor `F ↦ F^∨` above uses
  commutativity to remain in left modules.  The `CommRingCat` input here is
  the corrected source interface.
  -/
  sorry

end Formalization.Books.Injectives.Unit08
