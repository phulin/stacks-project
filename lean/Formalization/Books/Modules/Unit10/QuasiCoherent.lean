import Formalization.Books.Modules.Unit06.ClosedImmersions
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sheaves of Modules, Chapter 10: Quasi-coherent modules

The preceding modules chapter already provides the canonical project
interfaces for quasi-coherence and for the associated-sheaf construction.
This file gives those interfaces the source-facing names used in this
section, and records the additional presentation, point, and example data
which is explicit in the text.
-/

namespace Formalization.Books.Modules.Unit10

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit02
open scoped BigOperators

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## The local definition -/

/-- The free-cokernel presentation condition on one open neighbourhood. -/
abbrev hasPresentationOn {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (U : Opens X.carrier) : Prop :=
  Formalization.Books.Modules.Unit06.hasModulePresentationOn F U

/-- The source's pointwise definition of quasi-coherence. -/
abbrev LocallyPresented {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  Formalization.Books.Modules.Unit06.quasiCoherent F

/-- The canonical Mathlib/project quasi-coherence property. -/
abbrev IsQuasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  Formalization.Books.Modules.Unit06.quasiCoherent F

/-- The category denoted by `QCoh(O_X)` in the source. -/
abbrev QCoh (X : RingedSpace.{v}) :=
  Formalization.Books.Modules.Unit06.QCoh (X := X)

/-- The assertion that every quasi-coherent category is abelian is false in
general, as warned at the start of the source section. -/
abbrev AllQuasiCoherentCategoriesAbelian : Prop :=
  Formalization.Books.Modules.Unit06.allQuasiCoherentCategoriesAbelian

theorem not_all_quasiCoherentCategoriesAbelian :
    ¬ AllQuasiCoherentCategoriesAbelian := by
  exact Formalization.Books.Modules.Unit06.not_allQuasiCoherentCategoriesAbelian

/-- The two source-facing names describe the same property. -/
theorem isQuasiCoherent_iff_locallyPresented
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsQuasiCoherent F ↔ LocallyPresented F := Iff.rfl

/-- The presentation in the definition supplies generators and relations. -/
theorem locallyPresented_has_generators_and_relations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
  exact hF

/-- The last arrow in the displayed presentation is the cokernel projection. -/
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
  rcases hF x with ⟨U, hxU, I, J, φ, hφ⟩
  exact ⟨U, hxU, I, J, φ, hφ,
    Formalization.Books.Modules.Unit03.sheafModuleCokernel_universal
      (ringedOpenSubspace X U).structureSheaf φ⟩

/-- The displayed cokernel presentation is exact. -/
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

/-- The binary direct sum of quasi-coherent modules is quasi-coherent. -/
theorem directSum_isQuasiCoherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (hF : IsQuasiCoherent F) (hG : IsQuasiCoherent G) :
    IsQuasiCoherent (sheafModuleDirectSum X.structureSheaf F G) := by
  exact Formalization.Books.Modules.Unit06.quasiCoherent_directSum hF hG

/-- The source's warning that arbitrary infinite direct sums need not remain
quasi-coherent, expressed using the canonical coproduct construction. -/
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

/-- A witness that the quasi-coherent full subcategory is not abelian. -/
def HasNonabelianQuasiCoherentCategory (X : RingedSpace.{v}) : Prop :=
  ¬ Nonempty (Abelian (QCoh X))

theorem exists_nonabelian_quasiCoherentCategory :
    ∃ X : RingedSpace.{v}, HasNonabelianQuasiCoherentCategory X := by
  classical
  apply Classical.byContradiction
  intro h
  apply not_all_quasiCoherentCategoriesAbelian
  intro X
  by_contra hX
  exact h ⟨X, hX⟩

/-- Pullback along a morphism of ringed spaces preserves quasi-coherence. -/
theorem pullback_isQuasiCoherent
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsQuasiCoherent G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsQuasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  exact Formalization.Books.Modules.Unit06.quasiCoherent_pullback f G hG

/-! ## The sheaf associated to a module -/

/-- The ring of global sections of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{v}) : Type v :=
  Formalization.Books.Modules.Unit06.globalSectionsRing X

/-- The constant presheaf of rings with value `R`. -/
abbrev constantRingPresheaf (X : RingedSpace.{v}) (R : Type v) [Ring R] :
    TopCat.Presheaf RingCat X.carrier :=
  Formalization.Books.Modules.Unit06.constantRingPresheaf X R

/-- The constant presheaf of `R`-modules with value `M`. -/
noncomputable abbrev constantModulePresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (M : ModuleCat R) :
    PresheafOfModules (constantRingPresheaf X R) :=
  Formalization.Books.Modules.Unit06.constantModulePresheaf M

/-- The natural map from the constant global-sections ring to the structure
sheaf. -/
noncomputable abbrev globalSectionsPresheafMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    constantRingPresheaf X R ⟶ X.structureSheaf.obj := by
  exact Formalization.Books.Modules.Unit06.globalSectionsPresheafMap α

/-- The presheaf `U ↦ O_X(U) ⊗_R M` in the source's third construction. -/
noncomputable abbrev associatedSheafPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PresheafOfModules X.structureSheaf.obj :=
  Formalization.Books.Modules.Unit06.associatedSheafPresheaf α M

/-- The sheafification of the presheaf description. -/
noncomputable def associatedSheafFromPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj
    (associatedSheafPresheaf α M)

/-- The canonical project associated-sheaf construction. -/
noncomputable abbrev associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  Formalization.Books.Modules.Unit06.associatedSheafModule α M

/-- The source's `F_M`, for an `R`-module represented by its carrier type. -/
noncomputable abbrev associatedSheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] : Mod X.structureSheaf :=
  Formalization.Books.Modules.Unit06.associatedSheaf α M

/-- The source's associated-sheaf terminology for a bundled module. -/
noncomputable abbrev associatedSheafOfModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (α : R →+* globalSectionsRing X)
    (M : ModuleCat R) : Mod X.structureSheaf :=
  associatedSheafModule α M

/-- The associated sheaf for a module over the global-sections ring. -/
noncomputable abbrev associatedSheafOfGlobalSections
    {X : RingedSpace.{v}} (M : ModuleCat (globalSectionsRing X)) :
    Mod X.structureSheaf :=
  associatedSheafModule (RingHom.id _) M

/-- Associated sheaves are quasi-coherent. -/
theorem associatedSheaf_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] :
    IsQuasiCoherent (associatedSheaf α M) := by
  exact Formalization.Books.Modules.Unit06.associatedSheaf_quasiCoherent α M

/-- The same quasi-coherence assertion for the bundled module interface used
by the associated-sheaf functor. -/
theorem associatedSheafModule_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    IsQuasiCoherent (associatedSheafModule α M) := by
  sorry

/-! The three descriptions in the source. -/

/-- A presentation of a bundled module by free modules. -/
abbrev ModulePresentation {R : Type v} [Ring R] (M : ModuleCat R) :=
  Formalization.Books.Modules.Unit06.ModulePresentation M

/-- A matrix coefficient in a free presentation. -/
abbrev ModulePresentation.matrixEntry {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) (i : P.generators) : R :=
  Formalization.Books.Modules.Unit06.ModulePresentation.matrixEntry P j i

/-- The finite section corresponding to one presentation column. -/
noncomputable abbrev ModulePresentation.matrixSection
    {X : RingedSpace.{v}} {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M)
    (entries : P.relations → P.generators → globalSectionsRing X)
    (j : P.relations) :
      sheafModuleSections X.structureSheaf
      (SheafOfModules.free P.generators : Mod X.structureSheaf)
      (⊤ : Opens X.carrier) := by
  exact Formalization.Books.Modules.Unit06.ModulePresentation.matrixSection P entries j

/-- The one-point ringed space with ring `R`. -/
noncomputable abbrev onePointRingedSpace (R : Type v) [Ring R] : RingedSpace.{v} :=
  Formalization.Books.Modules.Unit06.onePointRingedSpace R

/-- Existence of the one-point morphism inducing `α` on global sections. -/
theorem exists_onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    Nonempty (RingedSpaceHom X (onePointRingedSpace R)) := by
  exact ⟨Formalization.Books.Modules.Unit06.onePointRingedSpaceHom α⟩

/-- A chosen one-point morphism. -/
noncomputable abbrev onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  Formalization.Books.Modules.Unit06.onePointRingedSpaceHom α

/-- The chosen one-point morphism induces the prescribed map on global
sections. -/
abbrev onePointRingedSpaceHomInduces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (f : RingedSpaceHom X (onePointRingedSpace R)) : Prop :=
  Formalization.Books.Modules.Unit06.onePointRingedSpaceHomInduces α f

theorem onePointRingedSpaceHom_induces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    onePointRingedSpaceHomInduces α (onePointRingedSpaceHom α) := by
  exact Formalization.Books.Modules.Unit06.onePointRingedSpaceHom_induces α

/-- The module on the one-point ringed space corresponding to `M`. -/
abbrev PointModuleDescription {R : Type v} [Ring R] (M : ModuleCat R) :=
  Formalization.Books.Modules.Unit06.PointModuleDescription M

/-- The pullback description of the one-point construction. -/
abbrev PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :=
  Formalization.Books.Modules.Unit06.PullbackDescription α M

/-- All three source constructions, with their canonical comparison data. -/
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
  presentationMap_matrix :
    ∀ j, sheafModuleSectionsMap X.structureSheaf presentationMap
        (⊤ : Opens X.carrier)
        ((SheafOfModules.freeSection (R := X.structureSheaf) j).eval
          (op (⊤ : Opens X.carrier))) =
      modulePresentation.matrixSection matrixEntries j
  presentationCokernel : Mod X.structureSheaf
  presentationCokernelIso : Nonempty
    (cokernel presentationMap ≅ presentationCokernel)
  pullbackDescription : PullbackDescription α M
  presentationToAssociated : Nonempty
    (presentationCokernel ≅ associatedSheafModule α M)
  presheafToAssociated : Nonempty
    (associatedSheafFromPresheaf α M ≅ associatedSheafModule α M)

/-- The source's three associated-sheaf descriptions are canonically
isomorphic. -/
theorem exists_associatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty (AssociatedSheafDescriptions α M) := by
  sorry

/-! ## Functorial properties -/

/-- The associated-sheaf construction is functorial in `M`. -/
noncomputable abbrev associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ Mod X.structureSheaf :=
  Formalization.Books.Modules.Unit06.associatedSheafFunctor α

theorem associatedSheafFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    (associatedSheafFunctor α).obj M = associatedSheafModule α M := rfl

/-- The stalk construction is functorial in `M`. -/
noncomputable def associatedSheafStalkFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (x : X) :
    ModuleCat R ⥤ ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  associatedSheafFunctor α ⋙ sheafModuleStalkFunctor X.structureSheaf x

theorem associatedSheafStalkFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    (associatedSheafStalkFunctor α x).obj M =
      (sheafModuleStalkFunctor X.structureSheaf x).obj (associatedSheafModule α M) := rfl

/-- The associated-sheaf functor with codomain restricted to `QCoh(O_X)`. -/
noncomputable def associatedSheafQCohFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ QCoh X where
  obj M := ⟨associatedSheafModule α M,
    associatedSheafModule_isQuasiCoherent α M⟩
  map f := ⟨(associatedSheafFunctor α).map f⟩
  map_id := by
    intro M
    rw [(associatedSheafFunctor α).map_id M]
    rfl
  map_comp := by
    intro M N P f g
    rw [(associatedSheafFunctor α).map_comp f g]
    rfl

/-- The associated-sheaf functor preserves arbitrary colimits. -/
theorem associatedSheafFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  exact Formalization.Books.Modules.Unit06.associatedSheaf_preserves_colimits α

/-! ## Stalks and Hom -/

/-- The map from global sections to a stalk ring. -/
noncomputable abbrev globalToStalkRing
    {X : RingedSpace.{v}} (x : X) :
    globalSectionsRing X →+*
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  (TopCat.Presheaf.Γgerm (C := RingCat.{v}) X.structureSheaf.obj x).hom

/-- The canonical module implementing `O_{X,x} ⊗_R M`. -/
noncomputable abbrev StalkTensorProduct
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  Formalization.Books.Modules.Unit06.associatedStalkTensorModule α M x

/-- The stalk formula for an associated sheaf. -/
theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X) :
    Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ StalkTensorProduct α M x) := by
  exact Formalization.Books.Modules.Unit06.associatedSheaf_stalk_iso α M x

/-- The `R`-module of global sections induced by `α`. -/
noncomputable abbrev globalSectionsModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (G : Mod X.structureSheaf) : ModuleCat R :=
  Formalization.Books.Modules.Unit06.associatedGlobalSectionsModule α G

/-- The associated-sheaf Hom formula. -/
theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (G : Mod X.structureSheaf) :
    Nonempty ((associatedSheaf α M ⟶ G) ≃
      (ModuleCat.of R M ⟶ globalSectionsModule α G)) := by
  exact Formalization.Books.Modules.Unit06.associatedSheaf_hom_equiv α M G

/-! ## Restriction and local presentation -/

/-- The map on global sections induced by a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X) :
    globalSectionsRing X →+* globalSectionsRing Y :=
  Formalization.Books.Modules.Unit06.ringedSpaceGlobalSectionsMap g

/-- The chosen scalar-extension module in the restriction formula. -/
noncomputable abbrev associatedScalarExtensionModule
    {R S : Type v} [Ring R] [Ring S]
    (β : R →+* S) (M : ModuleCat R) : ModuleCat S :=
  Formalization.Books.Modules.Unit06.associatedScalarExtensionModule β M

/-- Restriction of an associated sheaf is associated to the scalar extension
of its module of sections. -/
theorem restrict_associatedSheaf
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    {R : Type v} [Ring R] (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty ((sheafModuleRingedSpacePullback g).obj (associatedSheafModule α M) ≅
      associatedSheafModule (RingHom.id _) 
        (associatedScalarExtensionModule (ringedSpaceGlobalSectionsMap g).comp α M)) := by
  exact Formalization.Books.Modules.Unit06.associatedSheaf_restrict g α M

/-- A fundamental system of quasi-compact neighbourhoods at a point. -/
abbrev HasQuasiCompactNeighborhoodBasis {X : RingedSpace.{v}} (x : X) : Prop :=
  Formalization.Books.Modules.Unit06.hasQuasiCompactNeighborhoodBasis x

/-- A quasi-coherent module is locally associated to a module of sections when
the point has such a neighbourhood basis. -/
theorem exists_local_associatedSheaf
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (x : X)
    (hX : HasQuasiCompactNeighborhoodBasis x) (hF : IsQuasiCoherent F) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat (globalSectionsRing (ringedOpenSubspace X U)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
          associatedSheafModule (RingHom.id _) M) := by
  exact Formalization.Books.Modules.Unit06.quasiCoherent_locally_associated F x hX hF

/-! ## The countable wedge example -/

/-- A countable index for the free sheaves in the example. -/
abbrev CountableIndex : Type v := ULift.{v} ℕ

/-- A countable paired index for the matrix entries. -/
abbrev CountablePairIndex : Type v := ULift.{v} (ℕ × ℕ)

/-- The cutoff function used by the wedge example. -/
structure CutoffFunction where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  vanishes_on : ∀ x, x ∈ Set.Ioo (-1 : ℝ) 1 → toFun x = 0
  is_one_on : ∀ x, x < -2 ∨ 2 < x → toFun x = 1

instance : CoeFun CutoffFunction (fun _ ↦ ℝ → ℝ) :=
  ⟨CutoffFunction.toFun⟩

/-- The scaled cutoff `f_n(x) = f(nx)`. -/
def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x ↦ f ((n : ℝ) * x)

/-- Local finiteness of the branch-index coefficients. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ K : Finset ℕ, ∀ z : X, z ∈ U → ∀ i, i ∉ K → c j i z = 0

/-- Failure of finite matrix support on every indicated neighbourhood. -/
def NotLocallyFiniteLinearCombination {X : RingedSpace.{v}}
    (φ : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
      (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf))
    (U : ℕ → Opens X.carrier) : Prop :=
  ∀ (n j : ℕ), 2 * n < j →
    ¬ ∃ K : Finset ℕ,
      sheafModuleSectionsMap X.structureSheaf φ (U n)
          ((SheafOfModules.freeSection (R := X.structureSheaf)
            (⟨j⟩ : CountableIndex)).eval (op (U n))) ∈
        Submodule.span (X.structureSheaf.obj.obj (op (U n)))
          ((fun i : ℕ ↦
              ((SheafOfModules.freeSection (R := X.structureSheaf)
                (⟨(j, i)⟩ : CountablePairIndex)).eval (op (U n)))) '' (K : Set ℕ))

/-- The ringed-space, topology, coefficient, and matrix data of the source's
countable wedge example. -/
structure WedgeOfLinesExample where
  X : RingedSpace.{v}
  origin : X
  branch : ℕ → ℝ → X
  branch_cover : ∀ z : X, z = origin ∨ ∃ i x, x ≠ 0 ∧ z = branch i x
  branch_zero : ∀ i, branch i 0 = origin
  branch_separated : ∀ {i j : ℕ} {x y : ℝ},
    branch i x = branch j y → (x = 0 ∧ y = 0) ∨ (i = j ∧ x = y)
  wedge_topology : ∀ V : Set X,
    IsOpen V ↔ ∀ i, IsOpen (branch i ⁻¹' V)
  continuous_function_sections : ∀ U : Opens X.carrier,
    Nonempty (X.structureSheaf.obj.obj (op U) ≃+*
      ContinuousMap (U : Set X) ℝ)
  cutoff : CutoffFunction
  neighbourhood : ℕ → Opens X.carrier
  neighbourhood_basis :
    IsFundamentalSystemOfNeighborhoods origin
      (fun n ↦ (neighbourhood n : Set X))
  neighbourhood_on_branch : ∀ n i x,
    branch i x ∈ neighbourhood n ↔
      -(1 : ℝ) / ((n : ℝ) + 1) < x ∧ x < (1 : ℝ) / ((n : ℝ) + 1)
  coefficient : ℕ → ℕ → X → ℝ
  coefficient_at_origin : ∀ j i, coefficient j i origin = 0
  coefficient_continuous : ∀ j i, Continuous (coefficient j i)
  coefficient_on_branch : ∀ j i x, x ≠ 0 →
    coefficient j i (branch i x) = scaledCutoff cutoff j x
  coefficient_off_branch : ∀ j i k x, x ≠ 0 → k ≠ i →
    coefficient j k (branch i x) = 0
  coefficient_locally_finite : LocallyFiniteBranchCoefficients coefficient
  matrixMap :
    (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
      (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf)
  matrixMap_not_finite :
    NotLocallyFiniteLinearCombination matrixMap neighbourhood

/-- The wedge example supplies the map whose high-index generators have no
finite local matrix expression. -/
theorem exists_wedgeOfLinesExample : Nonempty WedgeOfLinesExample := by
  sorry

/-! The source's final assertions about further examples are explicitly
expectations, so they are recorded by the preceding interfaces and are not
made into false universal or existential theorems. -/

end

end Formalization.Books.Modules.Unit10
