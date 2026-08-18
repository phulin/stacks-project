import Formalization.Books.Modules.Unit08.LocallyGenerated
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Sheaves of Modules, Chapter 10: Quasi-coherent modules

This file follows the source section `Quasi-coherent modules`.  The ambient
categories, open restrictions, free sheaves, cokernels, pullbacks, and
sheafification are the canonical constructions from the preceding modules
chapters and Mathlib.
-/

namespace Formalization.Books.Modules.Unit10

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open scoped BigOperators

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## The definition and its exact presentation -/

/-- A free-cokernel presentation of a module on an open subspace. -/
def hasPresentationOn {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (U : Opens X.carrier) : Prop :=
  ∃ (I J : Type v)
    (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
    Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ)

/-- The source definition of quasi-coherence. -/
def IsQuasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasPresentationOn F U

/-- The terminology “locally presented” used in the source's explanation. -/
abbrev LocallyPresented {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  IsQuasiCoherent F

/-- The full subcategory denoted by `QCoh(O_X)`. -/
abbrev QCoh (X : RingedSpace.{v}) :=
  ObjectProperty.FullSubcategory
    (fun F : Mod X.structureSheaf => IsQuasiCoherent F)

/-- The opening warning that quasi-coherent sheaves need not form an abelian
category in the generality of ringed spaces. -/
def AllQuasiCoherentCategoriesAbelian : Prop :=
  ∀ X : RingedSpace.{v}, Nonempty (Abelian (QCoh X))

theorem not_all_quasiCoherentCategoriesAbelian :
    ¬ AllQuasiCoherentCategoriesAbelian := by
  sorry

theorem isQuasiCoherent_iff_locallyPresented
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsQuasiCoherent F ↔ LocallyPresented F := Iff.rfl

/-- The generators-and-relations form of the local definition. -/
theorem locallyPresented_has_generators_and_relations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
  exact hF

/-- The cokernel projection is the last arrow in every displayed local
presentation. -/
theorem locallyPresented_has_cokernel_sequence
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) ∧
          Nonempty (IsColimit
            (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))) := by
  intro x
  rcases hF x with ⟨U, hxU, hU⟩
  rcases hU with ⟨I, J, φ, e⟩
  exact ⟨U, hxU, I, J, φ, e,
    Formalization.Books.Modules.Unit03.sheafModuleCokernel_universal
      (ringedOpenSubspace X U).structureSheaf φ⟩

/-- The displayed presentation is exact after identifying its cokernel with
the restricted sheaf. -/
theorem locallyPresented_has_exact_presentation
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf))
        (e : ((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ),
        (ShortComplex.mk φ (cokernel.π φ ≫ e.inv) (by simp)).Exact := by
  sorry

/-! ## Direct sums and pullback -/

/-- The direct sum of two quasi-coherent modules is quasi-coherent. -/
theorem directSum_isQuasiCoherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (hF : IsQuasiCoherent F) (hG : IsQuasiCoherent G) :
    IsQuasiCoherent (sheafModuleDirectSum X.structureSheaf F G) := by
  sorry

/-- The source's infinite-direct-sum warning, expressed using the canonical
coproduct of sheaves of modules. -/
def InfiniteDirectSumsPreserveQuasiCoherent : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (_ : Infinite I)
    (F : I → Mod X.structureSheaf),
    (∀ i, IsQuasiCoherent (F i)) →
      IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)

theorem not_infiniteDirectSumsPreserveQuasiCoherent :
    ¬ InfiniteDirectSumsPreserveQuasiCoherent := by
  sorry

/-- An existential form of the infinite-direct-sum warning. -/
def HasInfiniteDirectSumFailure (X : RingedSpace.{v}) : Prop :=
  ∃ (I : Type v) (_ : Infinite I) (F : I → Mod X.structureSheaf),
    (∀ i, IsQuasiCoherent (F i)) ∧
      ¬ IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)

theorem exists_infinite_directSum_failure :
    ∃ X : RingedSpace.{v}, HasInfiniteDirectSumFailure X := by
  sorry

/-- Pullback preserves quasi-coherence. -/
theorem pullback_isQuasiCoherent
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsQuasiCoherent G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsQuasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## The three associated-sheaf constructions -/

/-- The ring of global sections. -/
abbrev globalSectionsRing (X : RingedSpace.{v}) : Type v :=
  X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))

/-- The constant presheaf of rings with value `R`. -/
abbrev constantRingPresheaf (X : RingedSpace.{v}) (R : Type v) [Ring R] :
    TopCat.Presheaf RingCat X.carrier :=
  (Functor.const (Opens X.carrier)ᵒᵖ).obj (RingCat.of R)

/-- The constant presheaf of `R`-modules with value `M`. -/
noncomputable def constantModulePresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (M : ModuleCat R) :
    PresheafOfModules (constantRingPresheaf X R) where
  obj _ := M
  map f :=
    (ModuleCat.restrictScalarsId'
      ((constantRingPresheaf X R).map (𝟙 _)).hom
      (congrArg RingCat.Hom.hom ((constantRingPresheaf X R).map_id _))).inv.app M
  map_id := by simp
  map_comp := by
    intro X₁ Y Z f g
    apply ModuleCat.hom_ext
    intro m
    rfl

/-- The map from a constant ring presheaf to the structure sheaf, induced by
a map into global sections. -/
noncomputable def globalSectionsPresheafMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    constantRingPresheaf X R ⟶ X.structureSheaf.obj := by
  classical
  refine { app := fun U => RingCat.ofHom ?_, naturality := ?_ }
  · exact
      ((X.structureSheaf.obj.map
          (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom.comp α)
  · intro U V f
    apply RingCat.hom_ext
    ext r
    simp only [constantRingPresheaf]
    rw [← X.structureSheaf.obj.map_comp]
    congr 1
    apply Subsingleton.elim

/-- The presheaf `U ↦ O_X(U) ⊗_R M`. -/
noncomputable abbrev associatedSheafPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PresheafOfModules X.structureSheaf.obj :=
  (Formalization.Books.Sheaves.Unit06.changeOfRingsCore
      (globalSectionsPresheafMap α)).obj (constantModulePresheaf M)

/-- The sheafification of the presheaf description. -/
noncomputable def associatedSheafFromPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj
    (associatedSheafPresheaf α M)

/-- The associated sheaf attached to a bundled module. -/
noncomputable abbrev associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  associatedSheafFromPresheaf α M

/-- The source notation `F_M` when `M` is presented by its carrier type. -/
noncomputable abbrev associatedSheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (α : R →+* globalSectionsRing X)
    (M : Type v) [AddCommGroup M] [Module R M] : Mod X.structureSheaf :=
  associatedSheafModule α (ModuleCat.of R M)

noncomputable abbrev associatedSheafOfModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Mod X.structureSheaf :=
  associatedSheafModule α M

noncomputable abbrev associatedSheafOfGlobalSections
    {X : RingedSpace.{v}} (M : ModuleCat (globalSectionsRing X)) :
    Mod X.structureSheaf :=
  associatedSheafModule (RingHom.id _) M

theorem associatedSheaf_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] :
    IsQuasiCoherent (associatedSheaf α M) := by
  sorry

theorem associatedSheafModule_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    IsQuasiCoherent (associatedSheafModule α M) := by
  sorry

/-! The presentation and point descriptions in the source. -/

/-- A module presentation by free modules. -/
structure ModulePresentation {R : Type v} [Ring R] (M : ModuleCat R) where
  relations : Type v
  generators : Type v
  map : (ModuleCat.free R).obj relations ⟶ (ModuleCat.free R).obj generators
  presentation : Nonempty (cokernel map ≅ M)

/-- The coefficient of a free-module map at a relation and generator. -/
abbrev ModulePresentation.matrixEntry {R : Type v} [Ring R]
    {M : ModuleCat R} (P : ModulePresentation M)
    (j : P.relations) (i : P.generators) : R :=
  ((P.map.hom (ModuleCat.freeMk j) : (ModuleCat.free R).obj P.generators) i)

/-- A one-point ringed space with structure ring `R`. -/
noncomputable def onePointRingedSpace (R : Type v) [Ring R] : RingedSpace.{v} :=
  { carrier := TopCat.of (ULift.{v} PUnit)
    structureSheaf :=
      (CategoryTheory.constantSheaf
        (Opens.grothendieckTopology (TopCat.of (ULift.{v} PUnit))) RingCat).obj
        (RingCat.of R) }

/-- The unique continuous map to the one-point space. -/
noncomputable def onePointContinuousMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R] :
    X.carrier ⟶ (onePointRingedSpace R).carrier :=
  TopCat.ofHom
    (ContinuousMap.const X.carrier (default : (onePointRingedSpace R).carrier))

/-- The one-point morphism whose map on structure sheaves is induced by `α`. -/
noncomputable def onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  { continuous := onePointContinuousMap
    sharp := by
      let F := (TopCat.Sheaf.pushforward RingCat onePointContinuousMap).obj
        X.structureSheaf
      let hα : R →+* F.presheaf.obj (op (⊤ : Opens (onePointRingedSpace R).carrier)) := by
        simpa [F, globalSectionsRing] using α
      exact
        ((CategoryTheory.constantSheafAdj
            (Opens.grothendieckTopology (onePointRingedSpace R).carrier) RingCat
            (T := (⊤ : Opens (onePointRingedSpace R).carrier)) isTerminalTop).homEquiv
          (RingCat.of R) F).symm (RingCat.ofHom hα) }

/-- The one-point morphism realizes the prescribed map on global sections. -/
def onePointRingedSpaceHomInduces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (f : RingedSpaceHom X (onePointRingedSpace R)) : Prop :=
  f.sharp = (onePointRingedSpaceHom α).sharp

theorem onePointRingedSpaceHom_induces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    onePointRingedSpaceHomInduces α (onePointRingedSpaceHom α) := by
  rfl

/-- The point/pullback description of the associated sheaf. -/
def PointModuleDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ P : Mod (onePointRingedSpace R).structureSheaf,
    Nonempty ((sheafModuleRingedSpacePullback (onePointRingedSpaceHom α)).obj P ≅
      associatedSheafModule α M)

/-- A source-facing name for the pullback description. -/
abbrev PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ P : Mod (onePointRingedSpace R).structureSheaf,
    Nonempty ((sheafModuleRingedSpacePullback (onePointRingedSpaceHom α)).obj P ≅
      associatedSheafModule α M)

/-- The three constructions in the source have canonical comparison
isomorphisms. -/
structure AssociatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  modulePresentation : ModulePresentation M
  matrixEntries : modulePresentation.relations → modulePresentation.generators →
    globalSectionsRing X
  matrixEntries_eq : matrixEntries = fun j i ↦
    α (modulePresentation.matrixEntry j i)
  presentationMap :
    (SheafOfModules.free modulePresentation.relations : Mod X.structureSheaf) ⟶
      (SheafOfModules.free modulePresentation.generators : Mod X.structureSheaf)
  presentationCokernel : Mod X.structureSheaf
  presentationCokernelIso : Nonempty
    (cokernel presentationMap ≅ presentationCokernel)
  pullbackDescription : PullbackDescription α M
  presentationToAssociated : Nonempty
    (presentationCokernel ≅ associatedSheafModule α M)
  presheafToAssociated : Nonempty
    (associatedSheafFromPresheaf α M ≅ associatedSheafModule α M)

theorem exists_associatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty (AssociatedSheafDescriptions α M) := by
  sorry

/-! ## Functorial properties, stalks, and Hom -/

/-- Data asserting that a chosen functor has the associated-sheaf objects. -/
def IsAssociatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (F : ModuleCat R ⥤ Mod X.structureSheaf) : Prop :=
  ∀ M, Nonempty (F.obj M ≅ associatedSheafModule α M)

/-- Existence of the functor supplied by the presheaf construction. -/
theorem exists_associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ∃ F : ModuleCat R ⥤ Mod X.structureSheaf,
      IsAssociatedSheafFunctor α F := by
  sorry

/-- The associated-sheaf construction is functorial in `M`. -/
noncomputable def associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ Mod X.structureSheaf := by
  exact Classical.choose (exists_associatedSheafFunctor α)

theorem associatedSheafFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty ((associatedSheafFunctor α).obj M ≅ associatedSheafModule α M) := by
  exact (Classical.choose_spec (exists_associatedSheafFunctor α)) M

/-- The stalk construction attached to the associated-sheaf functor. -/
noncomputable def associatedSheafStalkFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (x : X) :
    ModuleCat R ⥤ ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  associatedSheafFunctor α ⋙ sheafModuleStalkFunctor X.structureSheaf x

theorem associatedSheafStalkFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    Nonempty ((associatedSheafStalkFunctor α x).obj M ≅
      (sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheafModule α M)) := by
  sorry

/-- The associated-sheaf functor with codomain restricted to quasi-coherent
modules. -/
noncomputable def associatedSheafQCohFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ QCoh X where
  obj M := ⟨associatedSheafModule α M, associatedSheafModule_isQuasiCoherent α M⟩
  map f := ⟨(associatedSheafFunctor α).map f⟩
  map_id := by
    intro M
    apply ObjectProperty.hom_ext
    exact (associatedSheafFunctor α).map_id M
  map_comp := by
    intro M N P f g
    apply ObjectProperty.hom_ext
    exact (associatedSheafFunctor α).map_comp f g

theorem associatedSheafFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  sorry

/-- The map from global sections to a stalk. -/
noncomputable def globalToStalkRing
    {X : RingedSpace.{v}} (x : X) :
    globalSectionsRing X →+*
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  (TopCat.Presheaf.Γgerm (C := RingCat.{v}) X.structureSheaf.obj x).hom

/-- The canonical module `O_{X,x} ⊗_R M`. -/
noncomputable abbrev StalkTensorProduct
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  (ModuleCat.extendScalars ((globalToStalkRing x).comp α)).obj
    (ModuleCat.of R M)

theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X) :
    Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ StalkTensorProduct α M x) := by
  sorry

/-- The induced `R`-module of global sections. -/
noncomputable abbrev globalSectionsModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (G : Mod X.structureSheaf) : ModuleCat R :=
  (ModuleCat.restrictScalars α).obj
    ((SheafOfModules.evaluation X.structureSheaf (op (⊤ : Opens X.carrier))).obj G)

theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (G : Mod X.structureSheaf) :
    Nonempty ((associatedSheaf α M ⟶ G) ≃
      (ModuleCat.of R M ⟶ globalSectionsModule α G)) := by
  sorry

/-! ## Restriction and local presentation -/

/-- The map on global sections attached to a ringed-space morphism. -/
noncomputable def ringedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X) :
    globalSectionsRing X →+* globalSectionsRing Y := by
  simpa using (g.sharp.hom.app (op (⊤ : Opens X.carrier))).hom

/-- Scalar extension of a module. -/
noncomputable abbrev associatedScalarExtensionModule
    {R S : Type v} [Ring R] [Ring S]
    (β : R →+* S) (M : ModuleCat R) : ModuleCat S :=
  (ModuleCat.extendScalars β).obj M

theorem restrict_associatedSheaf
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    {R : Type v} [Ring R] (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty ((sheafModuleRingedSpacePullback g).obj (associatedSheafModule α M) ≅
      associatedSheafModule (RingHom.id _)
        (associatedScalarExtensionModule (ringedSpaceGlobalSectionsMap g).comp α M)) := by
  sorry

/-- A fundamental system of quasi-compact neighbourhoods at a point. -/
def HasQuasiCompactNeighborhoodBasis {X : RingedSpace.{v}} (x : X) : Prop :=
  ∀ U : Opens X.carrier, x ∈ U →
    ∃ K : Set X.carrier, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U

theorem exists_local_associatedSheaf
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (x : X)
    (hX : HasQuasiCompactNeighborhoodBasis x) (hF : IsQuasiCoherent F) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat (globalSectionsRing (ringedOpenSubspace X U)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
          associatedSheafModule (RingHom.id _) M) := by
  sorry

/-! ## The countable wedge example -/

abbrev CountableIndex : Type v := ULift.{v} ℕ
abbrev CountablePairIndex : Type v := ULift.{v} (ℕ × ℕ)

/-- A continuous cutoff which is zero near the origin and one outside a
larger compact interval. -/
structure CutoffFunction where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  zero_on : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, toFun x = 0
  one_on : ∀ x, x ∈ Set.Iic (-2 : ℝ) ∨ x ∈ Set.Ici 2 → toFun x = 1

instance : CoeFun CutoffFunction (fun _ => ℝ → ℝ) := ⟨CutoffFunction.toFun⟩

def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x => f (n * x)

/-- Local finiteness on each branch of the wedge. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, (Function.support (c j · x)).Finite

/-- A section of a free sheaf has finite free support when it comes from a
finite subcoproduct. -/
def HasFiniteFreeSupport {X : RingedSpace.{v}} (O : RingSheaf X.carrier)
    {I : Type v} (U : Opens X.carrier)
    (s : sheafModuleSections O (SheafOfModules.free I : Mod O) U) : Prop :=
  ∃ K : Finset I, ∃ t : sheafModuleSections O
      (SheafOfModules.free (↥K) : Mod O) U,
    sheafModuleSectionsMap O
      (SheafOfModules.freeMap (fun k : ↥K => k.1)) U t = s

/-- Failure of a finite matrix expression on the prescribed neighbourhoods. -/
def NotLocallyFiniteLinearCombination {X : RingedSpace.{v}}
    (φ : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
      (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf))
    (U : ℕ → Opens X.carrier) : Prop :=
  ∃ n j, 2 * n < j ∧
    ¬ HasFiniteFreeSupport X.structureSheaf (U n)
      (sheafModuleSectionsMap X.structureSheaf φ (U n)
        ((SheafOfModules.freeSection (R := X.structureSheaf)
          (ULift.up j)).eval (op (U n))))

/-- Data of the countable wedge example in the source. -/
structure WedgeOfLinesExample where
  X : RingedSpace.{v}
  neighbourhood : ℕ → Opens X.carrier
  coefficients : ℕ → ℕ → X → ℝ
  locallyFinite : LocallyFiniteBranchCoefficients coefficients
  map : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
    (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf)
  no_local_matrix : NotLocallyFiniteLinearCombination map neighbourhood

theorem exists_wedgeOfLinesExample : Nonempty WedgeOfLinesExample := by
  sorry

end

end Formalization.Books.Modules.Unit10
