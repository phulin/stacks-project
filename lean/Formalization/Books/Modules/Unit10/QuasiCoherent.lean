import Formalization.Books.Modules.Unit08.LocallyGenerated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
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
  Nonempty (((openModuleRestrictionFunctor X U).obj F).Presentation)

/-- The source definition of quasi-coherence, using Mathlib's canonical
presentation data for sheaves of modules. -/
abbrev IsQuasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsQuasicoherent F

/-- The pointwise local-presentation formulation used in the source's
explanation of quasi-coherence. The underlying presentation is Mathlib's
canonical `SheafOfModules.Presentation`, whose generators present the module
and whose relations generate the kernel of the associated epimorphism. -/
def HasLocalPresentation {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasPresentationOn F U

/- The source calls this condition “locally presented” immediately after the
definition of quasi-coherence. -/
abbrev LocallyPresented {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  HasLocalPresentation F

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
    IsQuasiCoherent F ↔ LocallyPresented F := by
  sorry

/-! The first part of the source's generators-and-relations explanation. -/
theorem locallyPresented_isLocallyGenerated
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    locallyGenerated F := by
  sorry

/-- The generators-and-relations form of the local definition. -/
theorem locallyPresented_has_generators_and_relations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
  sorry

/-- The presentation object is the canonical Mathlib packaging of the two
parts of the source's generators-and-relations explanation. -/
theorem locallyPresented_has_presentation
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasPresentationOn F U := by
  sorry

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
  sorry

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

/-- The warning used in the proof of the local-presentation lemma: global
sections need not commute with an infinite coproduct. -/
def GlobalSectionsOfCoproductAlwaysCommute : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (F : I → Mod X.structureSheaf),
    Nonempty ((SheafOfModules.evaluation X.structureSheaf
        (op (⊤ : Opens X.carrier))).obj
      (sheafModuleCoproduct X.structureSheaf F) ≅
      colimit (Discrete.functor (fun i =>
        (SheafOfModules.evaluation X.structureSheaf
          (op (⊤ : Opens X.carrier))).obj (F i))))

theorem not_globalSectionsOfCoproductAlwaysCommute :
    ¬ GlobalSectionsOfCoproductAlwaysCommute := by
  sorry

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
    ext m
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
    have htop :
        (X.structureSheaf.obj.map
            (homOfLE (show (V.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom =
          (X.structureSheaf.obj.map f).hom.comp
            (X.structureSheaf.obj.map
              (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom := by
      rw [← RingCat.hom_comp, ← X.structureSheaf.obj.map_comp]
      congr 1
    change
      (X.structureSheaf.obj.map
          (homOfLE (show (V.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom
          (α r) =
        (X.structureSheaf.obj.map f).hom
          ((X.structureSheaf.obj.map
            (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom
            (α r))
    exact congrArg (fun h : globalSectionsRing X →+* _ => h (α r)) htop

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

/-! The free sheaves used in the counterexample are instances of the
associated-sheaf construction. -/
noncomputable abbrev associatedSheafFreeModule
    (X : RingedSpace.{v}) (I : Type v) : Mod X.structureSheaf :=
  associatedSheafModule (RingHom.id _)
    ((ModuleCat.free (globalSectionsRing X)).obj I)

theorem freeSheaf_associatedSheaf_iso
    {X : RingedSpace.{v}} (I : Type v) :
    Nonempty ((SheafOfModules.free I : Mod X.structureSheaf) ≅
      associatedSheafFreeModule X I) := by
  sorry

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
  let v : P.generators →₀ R := P.map.hom (ModuleCat.freeMk j)
  v i

/-! The matrix in the second construction is finite in each column because
the corresponding element of a free module is a finitely supported function. -/

noncomputable def ModulePresentation.relationSectionValue
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations)
    (U : (Opens X.carrier)ᵒᵖ) :
    (SheafOfModules.free (R := X.structureSheaf) P.generators).val.obj U :=
  Finset.sum (P.map.hom (ModuleCat.freeMk j)).support (fun i =>
    let rU :=
      (X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
        (α (P.matrixEntry j i))
    let mU : (SheafOfModules.free (R := X.structureSheaf) P.generators).val.obj U :=
      (SheafOfModules.freeSection (R := X.structureSheaf) i).1 U
    rU • mU)

theorem ModulePresentation.relationSectionValue_compatible
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations)
    {_U _V : (Opens X.carrier)ᵒᵖ} (f : _U ⟶ _V) :
    (SheafOfModules.free (R := X.structureSheaf) P.generators).val.map f
        (P.relationSectionValue α j _U) =
      P.relationSectionValue α j _V := by
  sorry

noncomputable def ModulePresentation.relationSection
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) :
    (SheafOfModules.free P.generators : Mod X.structureSheaf).sections :=
  PresheafOfModules.sectionsMk (P.relationSectionValue α j)
    (fun {_U _V} f => P.relationSectionValue_compatible α j f)

noncomputable def associatedPresentationMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) :
    (SheafOfModules.free P.relations : Mod X.structureSheaf) ⟶
      (SheafOfModules.free P.generators : Mod X.structureSheaf) :=
  (SheafOfModules.freeHomEquiv _).symm
    (fun j => P.relationSection α j)

theorem associatedPresentationMap_section
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) :
    (SheafOfModules.freeHomEquiv
        (SheafOfModules.free P.generators : Mod X.structureSheaf)
      (associatedPresentationMap α P)) j = P.relationSection α j := by
  simp [associatedPresentationMap]

/-! For every chosen module presentation, the associated sheaf has the same
cokernel presentation. This is the presentation-independent construction
asserted in the source's second description. -/
theorem associatedPresentationMap_cokernel_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) :
    Nonempty (cokernel (associatedPresentationMap α P) ≅
      associatedSheafModule α M) := by
  sorry

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
    (ContinuousMap.const X.carrier
      (ULift.up PUnit.unit : (onePointRingedSpace R).carrier))

/-- The one-point morphism whose map on structure sheaves is induced by `α`. -/
noncomputable def onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  { continuous := onePointContinuousMap (X := X) (R := R)
    sharp := by
      let F := (TopCat.Sheaf.pushforward RingCat
        (onePointContinuousMap (X := X) (R := R))).obj
        X.structureSheaf
      let hα : R →+* F.presheaf.obj (op (⊤ : Opens (onePointRingedSpace R).carrier)) := by
        let e : F.presheaf.obj (op (⊤ : Opens (onePointRingedSpace R).carrier)) =
            X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) := by
          change X.structureSheaf.obj.obj
              (op ((Opens.map (onePointContinuousMap (X := X) (R := R))).obj
                (⊤ : Opens (onePointRingedSpace R).carrier))) =
            X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))
          rw [Opens.map_top]
        exact (RingCat.Hom.hom (eqToHom e.symm)).comp α
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
  f.continuous = onePointContinuousMap ∧
    HEq f.sharp (onePointRingedSpaceHom α).sharp

theorem onePointRingedSpaceHom_induces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    onePointRingedSpaceHomInduces α (onePointRingedSpaceHom α) := by
  exact ⟨rfl, HEq.rfl⟩

/-- The sheaf on the one-point ringed space corresponding to an `R`-module.
This is the point-space instance of the associated-sheaf construction. -/
noncomputable def onePointRingToGlobalSections
    (R : Type v) [Ring R] :
    R →+* globalSectionsRing (onePointRingedSpace R) :=
  RingCat.Hom.hom ((CategoryTheory.constantSheafAdj
      (Opens.grothendieckTopology (onePointRingedSpace R).carrier) RingCat
      (T := (⊤ : Opens (onePointRingedSpace R).carrier)) isTerminalTop).unit.app
    (RingCat.of R))

noncomputable abbrev onePointModule
    {R : Type v} [Ring R] (M : ModuleCat R) :
  Mod (onePointRingedSpace R).structureSheaf :=
  associatedSheafModule (X := onePointRingedSpace R) (RingHom.id _)
    ((ModuleCat.coextendScalars (onePointRingToGlobalSections R)).obj M)

/-! The pullback API exposes the right-adjoint witness explicitly here. -/

noncomputable def pointModulePullback
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint)
    (P : Mod (onePointRingedSpace R).structureSheaf) : Mod X.structureSheaf := by
  letI := h
  exact (sheafModuleRingedSpacePullback (onePointRingedSpaceHom α)).obj P

/-- The point/pullback description of the associated sheaf. -/
def PointModuleDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
    Nonempty (pointModulePullback α h (onePointModule M) ≅
      associatedSheafModule α M)

/-! The point-space/pullback construction is canonically the same associated
sheaf as the presheaf construction. -/
theorem associatedSheaf_point_description
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PointModuleDescription α M := by
  sorry

/-- A source-facing name for the pullback description. -/
abbrev PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
    Nonempty (pointModulePullback α h (onePointModule M) ≅
      associatedSheafModule α M)

/-- The three constructions in the source have canonical comparison
isomorphisms. -/
structure AssociatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  modulePresentation : ModulePresentation M
  presentationCokernelIso : Nonempty
    (cokernel (associatedPresentationMap α modulePresentation) ≅
      associatedSheafModule α M)
  pullbackWitness :
    ∃ h : (SheafOfModules.pushforward
        (F := Opens.map (onePointRingedSpaceHom α).continuous)
        (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
      Nonempty (pointModulePullback α h (onePointModule M) ≅
        associatedSheafModule α M)
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
  map f := ⟨
    (Classical.choice (associatedSheafFunctor_obj α _)).inv ≫
      (associatedSheafFunctor α).map f ≫
      (Classical.choice (associatedSheafFunctor_obj α _)).hom⟩
  map_id := by
    intro M
    apply ObjectProperty.hom_ext
    simp
  map_comp := by
    intro M N P f g
    apply ObjectProperty.hom_ext
    simp [Category.assoc]

theorem associatedSheafFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  sorry

theorem associatedSheafQCohFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafQCohFunctor α) := by
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
    [AddCommGroup M] [Module R M] (x : X)
    (hR : ∀ a b : R, a * b = b * a)
    (hA : ∀ a b : TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x,
      a * b = b * a) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  let A := TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x
  let ringR : Ring R := inferInstance
  let ringA : Ring A := inferInstance
  letI : CommRing R := { ringR with mul_comm := hR }
  letI : CommRing A := { ringA with mul_comm := hA }
  (ModuleCat.extendScalars ((globalToStalkRing x).comp α)).obj
    (ModuleCat.of R M)

theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X)
    (hR : ∀ a b : R, a * b = b * a)
    (hA : ∀ a b : TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x,
      a * b = b * a) :
    Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ StalkTensorProduct α M x hR hA) := by
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
  have h := (g.sharp.hom.app (op (⊤ : Opens X.carrier))).hom
  change X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) →+*
    Y.structureSheaf.obj.obj
      (op ((Opens.map g.continuous).obj (⊤ : Opens X.carrier))) at h
  rw [Opens.map_top] at h
  exact h

/-- Scalar extension of a module. -/
noncomputable abbrev associatedScalarExtensionModule
    {R S : Type v} [Ring R] [Ring S]
    (hR : ∀ a b : R, a * b = b * a)
    (hS : ∀ a b : S, a * b = b * a)
    (β : R →+* S) (M : ModuleCat R) : ModuleCat S := by
  let ringR : Ring R := inferInstance
  let ringS : Ring S := inferInstance
  letI : CommRing R := { ringR with mul_comm := hR }
  letI : CommRing S := { ringS with mul_comm := hS }
  exact (ModuleCat.extendScalars β).obj M

theorem restrict_associatedSheaf
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    {R : Type v} [Ring R] (α : R →+* globalSectionsRing X) (M : ModuleCat R)
    (hR : ∀ a b : R, a * b = b * a)
    (hY : ∀ a b : globalSectionsRing Y, a * b = b * a) :
    Nonempty ((sheafModuleRingedSpacePullback g).obj (associatedSheafModule α M) ≅
      associatedSheafModule (RingHom.id _)
        (associatedScalarExtensionModule
          hR hY ((ringedSpaceGlobalSectionsMap g).comp α) M)) := by
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
  one_on : ∀ x, x ∈ Set.Iio (-2 : ℝ) ∨ x ∈ Set.Ioi 2 → toFun x = 1

instance : CoeFun CutoffFunction (fun _ => ℝ → ℝ) := ⟨CutoffFunction.toFun⟩

def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x => f (n * x)

/-- Local finiteness of the branchwise coefficient sum. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, ∃ U : Set X.carrier, IsOpen U ∧ x ∈ U ∧
    (Set.Finite {i | ∃ y ∈ U, c j i y ≠ 0})

/-- The characteristic coefficient of a branch, with the common origin
assigned value zero. -/
def branchIndicator {X : RingedSpace.{v}} (branch : Set X.carrier) (origin : X)
    (x : X) : ℝ :=
  by classical exact if x = origin then 0 else if x ∈ branch then 1 else 0

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
  ∀ n j, 2 * n < j →
    ¬ HasFiniteFreeSupport X.structureSheaf (U n)
      (sheafModuleSectionsMap X.structureSheaf φ (U n)
        ((SheafOfModules.freeSection (R := X.structureSheaf)
          (ULift.up j)).eval (op (U n))))

/-- Data of the countable wedge example in the source. -/
structure WedgeOfLinesExample where
  X : RingedSpace.{v}
  origin : X
  neighbourhood : ℕ → Opens X.carrier
  origin_mem_neighbourhood : ∀ n, origin ∈ neighbourhood n
  neighbourhood_basis : ∀ U : Opens X.carrier, origin ∈ U →
    ∃ n, neighbourhood n ≤ U
  branches : ℕ → Set X.carrier
  branches_cover : ⋃ i, branches i = Set.univ
  branches_meet_only_at_origin : ∀ i j, i ≠ j →
    branches i ∩ branches j ⊆ {origin}
  cutoff : CutoffFunction
  coordinate : X → ℝ
  coefficients : ℕ → ℕ → X → ℝ
  coefficient_formula : ∀ j i x,
    coefficients j i x =
      scaledCutoff cutoff j (coordinate x) * branchIndicator (branches i) origin x
  locallyFinite : LocallyFiniteBranchCoefficients coefficients
  map : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
    (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf)
  no_local_matrix : NotLocallyFiniteLinearCombination map neighbourhood

theorem exists_wedgeOfLinesExample : Nonempty WedgeOfLinesExample := by
  sorry

end

end Formalization.Books.Modules.Unit10
