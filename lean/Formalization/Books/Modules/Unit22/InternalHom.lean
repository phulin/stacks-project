import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Modules.Unit20.FlatMorphisms
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Sheaves of Modules, Chapter 22: Internal Hom

The source defines the sheaf of local module homomorphisms and then records
its tensor adjunction, exactness, change-of-rings, stalk, pullback, coherence,
and filtered-colimit properties.  Chapter 16 established the project's
commutative sheaf-of-rings model for tensor products, so this file uses that
same model and exposes the local-Hom construction through a canonical data
interface.
-/

namespace Formalization.Books.Modules.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit24
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit16

universe v

noncomputable section

/-! ## The local Hom sheaf and its canonical maps -/

/- The `over` construction is the canonical restriction of a sheaf to an
   open.  Thus this is literally the source's
   `Hom_{O|U}(F|U, G|U)`, expressed on the over-category of `U`. -/
abbrev LocalModuleHom {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) (U : Opens X) : Type v :=
  SheafOfModules.over F U ⟶ SheafOfModules.over G U

/- The module of homomorphisms between two stalk modules. -/
noncomputable def stalkModuleHom {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O.obj x)) := by
  exact ModuleCat.of (↑(TopCat.Presheaf.stalk O.obj x))
    (commRingSheafModuleStalk F x ⟶ commRingSheafModuleStalk G x)

/- The two scalar actions in the source are retained explicitly.  The
   sectionwise module structure is part of the data, while the equality field
   records that multiplication before a local map and multiplication after it
   agree. -/
structure InternalHomData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) where
  hom : CommRingSheafModule O
  sections : ∀ U : Opens X,
    Nonempty ((hom.val.obj (op U) : Type v) ≃ LocalModuleHom O F G U)
  sectionwiseModule : ∀ U : Opens X,
    Module (↑(O.obj.obj (op U))) (LocalModuleHom O F G U)
  precomposeScalar : ∀ (U : Opens X),
    (O.obj.obj (op U) : Type v) → LocalModuleHom O F G U → LocalModuleHom O F G U
  postcomposeScalar : ∀ (U : Opens X),
    (O.obj.obj (op U) : Type v) → LocalModuleHom O F G U → LocalModuleHom O F G U
  precompose_smul : ∀ (U : Opens X) (r : O.obj.obj (op U))
    (φ : LocalModuleHom O F G U),
    (letI := sectionwiseModule U; r • φ) = precomposeScalar U r φ
  postcompose_smul : ∀ (U : Opens X) (r : O.obj.obj (op U))
    (φ : LocalModuleHom O F G U),
    (letI := sectionwiseModule U; r • φ) = postcomposeScalar U r φ
  scalar_actions_agree : ∀ (U : Opens X) (r : O.obj.obj (op U))
    (φ : LocalModuleHom O F G U),
    precomposeScalar U r φ = postcomposeScalar U r φ
  evaluation : Formalization.Books.Modules.Unit16.tensorProductSheaf O F hom ⟶ G
  stalkMap : ∀ x : X, commRingSheafModuleStalk hom x ⟶ stalkModuleHom O F G x

theorem internalHomData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) : Nonempty (InternalHomData O F G) := by
  sorry

/- The source's sheaf Hom.  Its body is a chosen instance of the canonical
   local-Hom sheaf supplied by `InternalHomData`. -/
noncomputable def internalHomData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) : InternalHomData O F G :=
  Classical.choice (internalHomData_exists O F G)

noncomputable abbrev internalHom {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) : CommRingSheafModule O :=
  (internalHomData O F G).hom

noncomputable def internalHomSectionsEquiv {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X) :
    (internalHom O F G).val.obj (op U) ≃ LocalModuleHom O F G U :=
  Classical.choice ((internalHomData O F G).sections U)

noncomputable def internalHom_sectionwiseModule {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X) :
    Module (↑(O.obj.obj (op U))) (LocalModuleHom O F G U) :=
  (internalHomData O F G).sectionwiseModule U

theorem internalHom_scalar_actions_agree {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (U : Opens X)
    (r : O.obj.obj (op U)) (φ : LocalModuleHom O F G U) :
    (internalHomData O F G).precomposeScalar U r φ =
      (internalHomData O F G).postcomposeScalar U r φ := by
  exact (internalHomData O F G).scalar_actions_agree U r φ

noncomputable abbrev internalHomEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) :
    Formalization.Books.Modules.Unit16.tensorProductSheaf O F (internalHom O F G) ⟶ G :=
  (internalHomData O F G).evaluation

noncomputable abbrev internalHomStalkMap {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) (x : X) :
    commRingSheafModuleStalk (internalHom O F G) x ⟶ stalkModuleHom O F G x :=
  (internalHomData O F G).stalkMap x

/- The chosen pre- and post-composition maps are the two functorial Hom
   actions used throughout the rest of the chapter. -/
theorem internalHomPrecomp_exists {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ G : CommRingSheafModule O} (f : F₁ ⟶ F₂) :
    Nonempty (internalHom O F₂ G ⟶ internalHom O F₁ G) := by
  sorry

noncomputable def internalHomPrecomp {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ G : CommRingSheafModule O} (f : F₁ ⟶ F₂) :
    internalHom O F₂ G ⟶ internalHom O F₁ G :=
  Classical.choice (internalHomPrecomp_exists f)

theorem internalHomPostcomp_exists {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G₁ G₂ : CommRingSheafModule O} (g : G₁ ⟶ G₂) :
    Nonempty (internalHom O F G₁ ⟶ internalHom O F G₂) := by
  sorry

noncomputable def internalHomPostcomp {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G₁ G₂ : CommRingSheafModule O} (g : G₁ ⟶ G₂) :
    internalHom O F G₁ ⟶ internalHom O F G₂ :=
  Classical.choice (internalHomPostcomp_exists g)

theorem internalHomPrecomp_comp {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F G : CommRingSheafModule O}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F) :
    internalHomPrecomp f₁ ≫ internalHomPrecomp f₂ =
      internalHomPrecomp (G := G) (f₂ ≫ f₁) := by
  sorry

theorem internalHomPrecomp_zero {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ G : CommRingSheafModule O} :
    internalHomPrecomp (G := G) (0 : F₁ ⟶ F₂) = 0 := by
  sorry

theorem internalHomPostcomp_comp {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G G₁ G₂ : CommRingSheafModule O}
    (g₁ : G ⟶ G₁) (g₂ : G₁ ⟶ G₂) :
    internalHomPostcomp g₁ ≫ internalHomPostcomp g₂ =
      internalHomPostcomp (F := F) (g₁ ≫ g₂) := by
  sorry

theorem internalHomPostcomp_zero {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G₁ G₂ : CommRingSheafModule O} :
    internalHomPostcomp (F := F) (0 : G₁ ⟶ G₂) = 0 := by
  sorry

/-! ## Tensor adjunction -/

theorem internalHom_tensor_hom_equiv_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O) :
    Nonempty ((Formalization.Books.Modules.Unit16.tensorProductSheaf O F G ⟶ H) ≃
      (F ⟶ internalHom O G H)) := by
  sorry

noncomputable def internalHomTensorCurry {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O) :
    (Formalization.Books.Modules.Unit16.tensorProductSheaf O F G ⟶ H) ≃
      (F ⟶ internalHom O G H) :=
  Classical.choice (internalHom_tensor_hom_equiv_exists O F G H)

noncomputable def internalHomTensorUncurry {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O) :
    (F ⟶ internalHom O G H) ≃
      (Formalization.Books.Modules.Unit16.tensorProductSheaf O F G ⟶ H) :=
  (internalHomTensorCurry O F G H).symm

@[simp] theorem internalHomTensorUncurry_curry {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O)
    (φ : Formalization.Books.Modules.Unit16.tensorProductSheaf O F G ⟶ H) :
    internalHomTensorUncurry O F G H (internalHomTensorCurry O F G H φ) = φ := by
  exact (internalHomTensorCurry O F G H).left_inv φ

@[simp] theorem internalHomTensorCurry_uncurry {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O)
    (φ : F ⟶ internalHom O G H) :
    internalHomTensorCurry O F G H (internalHomTensorUncurry O F G H φ) = φ := by
  exact (internalHomTensorCurry O F G H).right_inv φ

/- Functoriality in all three entries of the adjunction. -/
theorem internalHomTensorCurry_natural {X : TopCat.{v}}
    (O : CommRingSheaf X)
    {F₁ F₂ G₁ G₂ H₁ H₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (h : H₁ ⟶ H₂)
    (φ : Formalization.Books.Modules.Unit16.tensorProductSheaf O F₂ G₂ ⟶ H₁) :
    internalHomTensorCurry O F₁ G₁ H₂
        (tensorProductMap f g ≫ φ ≫ h) =
      f ≫ internalHomTensorCurry O F₂ G₂ H₁ φ ≫
        internalHomPrecomp g ≫ internalHomPostcomp h := by
  sorry

/-! ## Exactness -/

universe u

structure ExactAtZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : Prop where
  map_comp : f ≫ g = 0
  mono : Mono f
  exact : (ShortComplex.mk f g map_comp).Exact

noncomputable def internalHomPrecompSequence {X : TopCat.{v}}
    {O : CommRingSheaf X} {F₂ F₁ F G : CommRingSheafModule O}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F)
    (h : f₂ ≫ f₁ = 0) :
  ShortComplex (CommRingSheafModule O) :=
  ShortComplex.mk (internalHomPrecomp f₁) (internalHomPrecomp f₂)
    (by rw [internalHomPrecomp_comp (G := G), h, internalHomPrecomp_zero])

noncomputable def internalHomPostcompSequence {X : TopCat.{v}}
    {O : CommRingSheaf X} {F G G₁ G₂ : CommRingSheafModule O}
    (g₁ : G ⟶ G₁) (g₂ : G₁ ⟶ G₂)
    (h : g₁ ≫ g₂ = 0) :
  ShortComplex (CommRingSheafModule O) :=
  ShortComplex.mk (internalHomPostcomp g₁) (internalHomPostcomp g₂)
    (by rw [internalHomPostcomp_comp (F := F), h, internalHomPostcomp_zero])

theorem internalHom_exact_precomp
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F G : CommRingSheafModule O}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F)
    (hF : RightExactSequence f₂ f₁) :
    ExactAtZero (A := internalHom O F G) (B := internalHom O F₁ G)
      (D := internalHom O F₂ G) (internalHomPrecomp (G := G) f₁)
      (internalHomPrecomp (G := G) f₂) := by
  sorry

theorem internalHom_exact_postcomp
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G G₁ G₂ : CommRingSheafModule O}
    (g₁ : G ⟶ G₁) (g₂ : G₁ ⟶ G₂)
    (hG : ExactAtZero g₁ g₂) :
    ExactAtZero (A := internalHom O F G) (B := internalHom O F G₁)
      (D := internalHom O F G₂) (internalHomPostcomp (F := F) g₁)
      (internalHomPostcomp (F := F) g₂) := by
  sorry

/-! ## Change of rings -/

noncomputable abbrev restrictScalarsModule {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂) :
    CommRingSheafModule O₂ ⥤ CommRingSheafModule O₁ :=
  SheafOfModules.restrictScalars (commRingSheafMorphismToRingSheaf α)

noncomputable abbrev restrictedStructureModule {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂) : CommRingSheafModule O₁ :=
  (restrictScalarsModule α).obj (SheafOfModules.unit (commRingSheafToRingSheaf O₂))

structure ChangeOfRingsInternalHomData {X : TopCat.{v}}
    (O₁ O₂ : CommRingSheaf X) (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) where
  hom : CommRingSheafModule O₂
  underlyingIso :
    (restrictScalarsModule α).obj hom ≅
      internalHom O₁ (restrictedStructureModule α) G
  homEquiv : ∀ F : CommRingSheafModule O₂,
    ((restrictScalarsModule α).obj F ⟶ G) ≃ (F ⟶ hom)

/- The `homEquiv` field is refined below to the source-facing adjunction; its
   type is intentionally kept in a separate theorem so the O₂-action on the
   internal Hom is explicit in the interface. -/
theorem changeOfRingsInternalHomData_exists {X : TopCat.{v}}
    (O₁ O₂ : CommRingSheaf X) (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) :
    Nonempty (ChangeOfRingsInternalHomData O₁ O₂ α G) := by
  sorry

noncomputable def changeOfRingsInternalHomData {X : TopCat.{v}}
    (O₁ O₂ : CommRingSheaf X) (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) : ChangeOfRingsInternalHomData O₁ O₂ α G :=
  Classical.choice (changeOfRingsInternalHomData_exists O₁ O₂ α G)

noncomputable abbrev changeOfRingsInternalHom {X : TopCat.{v}}
    (O₁ O₂ : CommRingSheaf X) (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) : CommRingSheafModule O₂ :=
  (changeOfRingsInternalHomData O₁ O₂ α G).hom

theorem internalHom_changeOfRings
    {X : TopCat.{v}} (O₁ O₂ : CommRingSheaf X) (α : O₁ ⟶ O₂)
    (F : CommRingSheafModule O₂) (G : CommRingSheafModule O₁) :
    Nonempty (((restrictScalarsModule α).obj F ⟶ G) ≃
      (F ⟶ changeOfRingsInternalHom O₁ O₂ α G)) := by
  exact ⟨(changeOfRingsInternalHomData O₁ O₂ α G).homEquiv F⟩

/-! ## Stalks -/

theorem internalHom_stalk_injective_of_finiteType
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O)
    (hF : IsFiniteType F) (x : X) :
    Function.Injective (internalHomStalkMap O F G x) := by
  sorry

theorem internalHom_stalk_isIso_of_finitePresentation
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O)
    (hF : IsFinitePresentation F) (x : X) :
    IsIso (internalHomStalkMap O F G x) := by
  sorry

/-! ## Pullback and coherence -/

def IsFlatMorphism {X Y : TopCat.{v}} {OX : CommRingSheaf X}
    {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX)) : Prop :=
  ∀ x : X, Formalization.Books.Modules.Unit20.commutativeFlatOverAt f α
    (SheafOfModules.unit (commRingSheafToRingSheaf OX)) x

theorem pullback_internalHom
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (F G : CommRingSheafModule OY)
    (hF : IsFinitePresentation F) (hf : IsFlatMorphism f α) :
    Nonempty
      ((pullbackModule f α).obj (internalHom OY F G) ≅
        internalHom OX ((pullbackModule f α).obj F)
          ((pullbackModule f α).obj G)) := by
  sorry

noncomputable def finiteCopyDirectSum
    {Y : Formalization.Books.Sheaves.Unit22.RingedSpace.{v}}
    (G : Mod Y.structureSheaf) (n : ℕ) : Mod Y.structureSheaf :=
  colimit (Discrete.functor (fun _ : ULift.{v} (Fin n) => G))

def LocallyFiniteCopyKernel {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ (m n : ℕ)
      (φ : finiteCopyDirectSum
        ((openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj G) m ⟶
        finiteCopyDirectSum
        ((openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj G) n),
      Nonempty (((openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj
        (internalHom O F G)) ≅ kernel φ)

theorem internalHom_locallyFiniteCopyKernel
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) (hF : IsFinitePresentation F) :
    LocallyFiniteCopyKernel F G := by
  sorry

theorem internalHom_isCoherent_of_isCoherent
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O)
    (hF : IsFinitePresentation F) (hG : IsCoherent G) :
    IsCoherent (internalHom O F G) := by
  sorry

/-! ## Filtered colimits -/

noncomputable def internalHomPostcompDiagram {X : TopCat.{v}}
    {O : CommRingSheaf X} (F : CommRingSheafModule O)
    {J : Type v} [Category.{v} J]
    (D : J ⥤ CommRingSheafModule O) :
    J ⥤ CommRingSheafModule O where
  obj j := internalHom O F (D.obj j)
  map f := internalHomPostcomp (D.map f)
  map_id j := by sorry
  map_comp f g := by sorry

theorem internalHom_filteredColimitComparison_exists
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O)
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (D : J ⥤ CommRingSheafModule O) :
    Nonempty
      (colimit (internalHomPostcompDiagram F D) ⟶
        internalHom O F (colimit D)) := by
  sorry

noncomputable def internalHom_filteredColimitComparison
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O)
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (D : J ⥤ CommRingSheafModule O) :
    colimit (internalHomPostcompDiagram F D) ⟶
      internalHom O F (colimit D) :=
  Classical.choice (internalHom_filteredColimitComparison_exists F D)

theorem internalHom_commutes_with_filteredColimit
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O)
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (D : J ⥤ CommRingSheafModule O)
    (hF : IsFinitePresentation F) :
    IsIso (internalHom_filteredColimitComparison F D) := by
  sorry

/-! ## Global Hom and the quasi-compact colimit statement -/

noncomputable def globalHomDiagram {X : TopCat.{v}}
    {O : CommRingSheaf X} (G : CommRingSheafModule O)
    {I : Type v} [Category.{v} I]
    (D : I ⥤ CommRingSheafModule O) : I ⥤ Type v where
  obj i := _root_.SheafOfModules.Hom G (D.obj i)
  map := fun {i j} f =>
    TypeCat.ofHom (fun (φ : _root_.SheafOfModules.Hom G (D.obj i)) =>
      ({ val := φ.val ≫ (D.map f).val } :
        _root_.SheafOfModules.Hom G (D.obj j)))
  map_id i := by
    sorry
  map_comp f g := by
    sorry

def HasCofinalFiniteQuasiCompactOpenCover {X : TopCat.{v}} : Prop :=
  ∀ (K : Type v) (V : K → Opens X),
    (∀ x : X, ∃ k, x ∈ V k) →
      ∃ (J : Type v) (_ : Finite J) (U : J → Opens X),
        (∀ x : X, ∃ j, x ∈ U j) ∧
        (∀ j, ∃ k, U j ≤ V k) ∧
        (∀ j j', IsCompact (((U j : Set X) ∩ (U j' : Set X))))

theorem globalHom_colimitComparison_exists
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : CommRingSheafModule O)
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (D : I ⥤ CommRingSheafModule O) :
    Nonempty
      (colimit (globalHomDiagram G D) →
        (G ⟶ colimit D)) := by
  sorry

noncomputable def globalHom_colimitComparison
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : CommRingSheafModule O)
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (D : I ⥤ CommRingSheafModule O) :
    colimit (globalHomDiagram G D) → (G ⟶ colimit D) :=
  Classical.choice (globalHom_colimitComparison_exists G D)

theorem globalHom_colimitComparison_bijective
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : CommRingSheafModule O)
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (D : I ⥤ CommRingSheafModule O)
    (hG : IsFinitePresentation G)
    (hX : HasCofinalFiniteQuasiCompactOpenCover (X := X)) :
    Function.Bijective (globalHom_colimitComparison G D) := by
  sorry

/- The source identifies global morphisms with sections of the internal Hom;
   the unit Hom equivalence is Mathlib's canonical section interface. -/
theorem globalHom_internalHom_equiv
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O) :
    Nonempty ((F ⟶ G) ≃
      (SheafOfModules.unit (commRingSheafToRingSheaf O) ⟶
        internalHom O F G)) := by
  sorry

/- The final source remark is retained as a precise warning predicate: there
   are quasi-compact spaces for which the stronger cofinal-cover hypothesis
   fails. -/
def QuasiCompactOnlyInsufficient : Prop :=
  ∃ X : TopCat.{v}, IsCompact (Set.univ : Set X) ∧
    ¬ HasCofinalFiniteQuasiCompactOpenCover (X := X)

theorem quasiCompactOnlyInsufficient : QuasiCompactOnlyInsufficient := by
  sorry

end

end Formalization.Books.Modules.Unit22
