import Formalization.Books.Modules.Unit03.AbelianCategory
import Formalization.Books.Topology.Unit02.BasicNotions
import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sheaves of Modules, Chapter 10: Quasi-coherent modules

This file records the source definition of quasi-coherence together with the
canonical presentation, pullback, associated-sheaf, restriction, and local
presentation interfaces used in the section.  The ambient category of sheaves
of modules and its free, cokernel, coproduct, and pullback constructions are
the canonical Mathlib constructions exposed in earlier chapters.
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

/-
The source uses the pointwise formulation.  Mathlib's
`SheafOfModules.IsQuasicoherent` uses the equivalent cover-by-opens
formulation, and is the property used for the category below.  Keeping the
pointwise formulation here makes the source definition and its displayed
free-cokernel presentation available without introducing a second category.
-/

/-- The source's local free-cokernel presentation condition. -/
def LocallyPresented {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ (I J : Type v)
      (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
        (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
      Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ)

/-- The canonical Mathlib quasi-coherence property for a ringed space. -/
abbrev IsQuasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsQuasicoherent F

/-- The source definition agrees with Mathlib's cover formulation. -/
theorem isQuasiCoherent_iff_locallyPresented
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsQuasiCoherent F ↔ LocallyPresented F := by
  sorry

/-- The category denoted by `QCoh(O_X)` in the source. -/
abbrev QCoh (X : RingedSpace.{v}) :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).FullSubcategory

/-! The two clauses in the displayed presentation are the generators and
relations data of the canonical Mathlib presentation. -/

/-- A local free-cokernel presentation gives the source's generators and
relations presentation data. -/
theorem locallyPresented_has_generators_and_relations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
  exact hF

/-- The cokernel presentation carries the canonical exactness/cokernel
sequence displayed in the source. -/
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
    sheafModuleCokernel_universal (ringedOpenSubspace X U).structureSheaf φ⟩

/-- The displayed free presentation is exact at the middle term, with the
last map identified with the cokernel projection. -/
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
  sorry

/-! The source warns that the following statements fail for arbitrary ringed
spaces.  They are represented as existential predicates rather than as
universal assertions. -/

/-- A witness that an infinite direct sum of quasi-coherent modules fails to
be quasi-coherent. -/
def HasInfiniteDirectSumFailure (X : RingedSpace.{v}) : Prop :=
  ∃ (I : Type v) (_ : Infinite I) (F : I → Mod X.structureSheaf),
    (∀ i, IsQuasiCoherent (F i)) ∧
      ¬ IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)

/-- A witness that the quasi-coherent full subcategory is not abelian. -/
def HasNonabelianQuasiCoherentCategory (X : RingedSpace.{v}) : Prop :=
  ¬ Nonempty (Abelian (QCoh X))

/-- The source's warning about infinite direct sums. -/
theorem exists_infinite_directSum_failure :
    ∃ X : RingedSpace.{v}, HasInfiniteDirectSumFailure X := by
  sorry

/-- The source's warning that quasi-coherent modules need not form an abelian
subcategory on a general ringed space. -/
theorem exists_nonabelian_quasiCoherentCategory :
    ∃ X : RingedSpace.{v}, HasNonabelianQuasiCoherentCategory X := by
  sorry

/-- Pullback along a morphism of ringed spaces preserves quasi-coherence. -/
theorem pullback_isQuasiCoherent
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsQuasiCoherent G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsQuasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## The sheaf associated to a module -/

/-- The ring of global sections of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{v}) : Type v :=
  X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))

/-- The constant presheaf of rings with value `R`. -/
abbrev constantRingPresheaf (X : RingedSpace.{v}) (R : Type v) [Ring R] :
    TopCat.Presheaf RingCat X.carrier :=
  (Functor.const (Opens X.carrier)ᵒᵖ).obj (RingCat.of R)

/-- The constant presheaf of `R`-modules with value `M`. -/
noncomputable def constantModulePresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (M : ModuleCat R) :
    PresheafOfModules (constantRingPresheaf X R) :=
  (PresheafOfModules.constFunctor
      (Limits.constCocone (Opens X.carrier)ᵒᵖ (RingCat.of R))).obj M

/-- The canonical map from the constant ring presheaf to the structure
sheaf induced by a ring map from global sections. -/
noncomputable def globalSectionsPresheafMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    constantRingPresheaf X R ⟶ X.structureSheaf.obj := by
  refine {
    app := fun U => RingCat.ofHom
      ((X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom.comp α)
    naturality := ?_ }
  intro U V f
  apply RingCat.hom_ext
  ext r
  change ((X.structureSheaf.obj.map
      (homOfLE (show V.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom (α r)) =
    (X.structureSheaf.obj.map f).hom
      ((X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op).hom (α r))
  rw [← RingCat.comp_apply, ← X.structureSheaf.obj.map_comp]
  have h :
      (homOfLE (show V.unop ≤ (⊤ : Opens X.carrier) from le_top)).op =
        (homOfLE (show U.unop ≤ (⊤ : Opens X.carrier) from le_top)).op ≫ f :=
    Subsingleton.elim _ _
  rw [h]

/-- The presheaf tensor product underlying the associated sheaf. -/
noncomputable def associatedSheafPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PresheafOfModules X.structureSheaf.obj :=
  Formalization.Books.Sheaves.Unit06.tensorProductPresheaf
    (globalSectionsPresheafMap α) (constantModulePresheaf M)

/-- The sheaf associated to `M` and `α`, obtained by sheafifying the
presheaf `U ↦ O_X(U) ⊗_R M`. -/
noncomputable def associatedSheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj
    (associatedSheafPresheaf α M)

/-- The source's notation `F_M` for the associated sheaf. -/
abbrev associatedSheafOfModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :=
  associatedSheaf α M

/-- The shorthand associated sheaf for a module over the global-sections
ring. -/
abbrev associatedSheafOfGlobalSections
    {X : RingedSpace.{v}} (M : ModuleCat (globalSectionsRing X)) :=
  associatedSheaf (RingHom.id _) M

/-- Associated sheaves are quasi-coherent. -/
theorem associatedSheaf_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    IsQuasiCoherent (associatedSheaf α M) := by
  sorry

/-- The associated sheaf of a free module is the corresponding free sheaf. -/
theorem associatedSheaf_freeModule_iso
    {X : RingedSpace.{v}} {I : Type v} :
    Nonempty (associatedSheaf (RingHom.id (globalSectionsRing X))
        ((ModuleCat.free (globalSectionsRing X)).obj I) ≅
      (SheafOfModules.free I : Mod X.structureSheaf)) := by
  sorry

/-! The three constructions in the source are represented by a presentation
interface.  Its module presentation records the matrix coefficients, while
the two displayed sheaves are retained as objects equipped with canonical
isomorphisms to the presheaf-sheafification construction above. -/

/-- A presentation of a module over a ring, retaining its free generators and
relations and the resulting module isomorphism. -/
structure ModulePresentation {R : Type v} [Ring R] (M : ModuleCat R) where
  generators : Type v
  relations : Type v
  relationMap : (ModuleCat.free R).obj relations ⟶ (ModuleCat.free R).obj generators
  quotientIso : Nonempty (cokernel relationMap ≅ M)

/-- The coefficient of a relation generator in a module presentation. -/
def ModulePresentation.matrixEntry {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) (i : P.generators) : R :=
  let z : P.generators →₀ R := P.relationMap.hom (ModuleCat.freeMk j)
  z i

/-- The finite section obtained from one column of the matrix coefficients. -/
noncomputable def ModulePresentation.matrixSection
    {X : RingedSpace.{v}} {R : Type v} [Ring R] {M : ModuleCat R}
    (P : ModulePresentation M)
    (entries : P.relations → P.generators → globalSectionsRing X)
    (j : P.relations) :
    sheafModuleSections X.structureSheaf
      (SheafOfModules.free P.generators : Mod X.structureSheaf)
      (⊤ : Opens X.carrier) := by
  let z : P.generators →₀ R := P.relationMap.hom (ModuleCat.freeMk j)
  exact ∑ i ∈ z.support,
    entries j i •
      (SheafOfModules.freeSection (R := X.structureSheaf) i).eval
        (op (⊤ : Opens X.carrier))

/-- The one-point ringed space whose ring is `R`. -/
noncomputable def onePointRingedSpace (R : Type v) [Ring R] : RingedSpace.{v} where
  carrier := TopCat.of PUnit
  structureSheaf :=
    (CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (TopCat.of PUnit)) RingCat.{v}).obj (RingCat.of R)

/-- Existence of the ringed-space morphism inducing a map on global sections. -/
theorem exists_onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    Nonempty (RingedSpaceHom X (onePointRingedSpace R)) := by
  sorry

/-- A chosen morphism to the one-point ringed space. -/
noncomputable def onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  Classical.choice (exists_onePointRingedSpaceHom α)

/-- The one-point pullback description of the associated sheaf. -/
structure PointModuleDescription {R : Type v} [Ring R] (M : ModuleCat R) where
  pointModule : Mod (onePointRingedSpace R).structureSheaf
  correspondence :
    ∃ e : (Mod (onePointRingedSpace R).structureSheaf) ≌ ModuleCat R,
      Nonempty (pointModule ≅ e.inverse.obj M)

/-- A presentation of the one-point module corresponding to `M`. -/
structure PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  projection : RingedSpaceHom X (onePointRingedSpace R)
  projection_is_canonical : projection = onePointRingedSpaceHom α
  pointModule : PointModuleDescription M
  pullbackToAssociated :
    ∀ [_h : ((SheafOfModules.pushforward (F := Opens.map projection.continuous)
      projection.sharp).IsRightAdjoint)],
      Nonempty ((sheafModuleRingedSpacePullback projection).obj pointModule.pointModule ≅
        associatedSheaf α M)

/-- The three source descriptions of the associated sheaf, with the pullback
and presentation realizations exposed as usable objects. -/
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
    (presentationCokernel ≅ associatedSheaf α M)

/-- The associated-sheaf construction has the three canonically isomorphic
descriptions listed in the source. -/
theorem exists_associatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty (AssociatedSheafDescriptions α M) := by
  sorry

/-! ## Functorial properties of the associated construction -/

/-- The associated-sheaf construction is functorial in the module. -/
noncomputable def associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ModuleCat R ⥤ Mod X.structureSheaf :=
  (PresheafOfModules.constFunctor
      (Limits.constCocone (Opens X.carrier)ᵒᵖ (RingCat.of R))) ⋙
    Formalization.Books.Sheaves.Unit06.changeOfRings
      (globalSectionsPresheafMap α) ⋙
    PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

/-- The object of the associated-sheaf functor is the source construction. -/
theorem associatedSheafFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    (associatedSheafFunctor α).obj M = associatedSheaf α M := rfl

/-- Stalks retain the functoriality in the module of the associated
construction. -/
noncomputable def associatedSheafStalkFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (x : X) :
    ModuleCat R ⥤ ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  associatedSheafFunctor α ⋙ sheafModuleStalkFunctor X.structureSheaf x

/-- The object part of the stalk functor is the stalk of the associated
sheaf. -/
theorem associatedSheafStalkFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    (associatedSheafStalkFunctor α x).obj M =
      (sheafModuleStalkFunctor X.structureSheaf x).obj (associatedSheaf α M) := rfl

/-- The associated construction, with its quasi-coherence witness, as a
functor into the source category `QCoh(O_X)`. -/
noncomputable def associatedSheafQCohFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ModuleCat R ⥤ QCoh X where
  obj M := ⟨associatedSheaf α M, associatedSheaf_isQuasiCoherent α M⟩
  map f := ⟨(associatedSheafFunctor α).map f⟩
  map_id := by
    intro M
    rw [(associatedSheafFunctor α).map_id M]
    rfl
  map_comp := by
    intro X Y Z f g
    rw [(associatedSheafFunctor α).map_comp f g]
    rfl

/-- The associated-sheaf functor commutes with arbitrary colimits. -/
theorem associatedSheafFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  sorry

/-! The stalk formula is recorded with the universal property of extension of
scalars.  This keeps the chapter at the `RingCat` generality of the ringed
space API; in the commutative case this is the usual tensor product. -/

/-- The map from global sections to the stalk ring at a point. -/
noncomputable def globalToStalkRing
    {X : RingedSpace.{v}} (x : X) :
    globalSectionsRing X →+*
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  (TopCat.Presheaf.germ (C := RingCat.{v}) X.structureSheaf.obj
      (⊤ : Opens X.carrier) x (by simp)).hom

/-- A chosen module implementing `O_x ⊗_R M`. -/
structure StalkTensorProduct
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) where
  scalarMap : R →+*
    TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x
  scalarMap_eq : scalarMap = (globalToStalkRing x).comp α
  module : ModuleCat.{v, v} (TopCat.Presheaf.stalk (C := RingCat.{v})
    X.structureSheaf.obj x)
  unit : M ⟶ (ModuleCat.restrictScalars scalarMap).obj module
  homEquiv : ∀ N : ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x),
    (module ⟶ N) ≃
      (M ⟶ (ModuleCat.restrictScalars scalarMap).obj N)
  homEquiv_unit : ∀ (N : ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))
      (f : module ⟶ N),
    homEquiv N f = unit ≫ (ModuleCat.restrictScalars scalarMap).map f

/-- The stalk of an associated sheaf is the tensor product module. -/
theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X)
    (T : StalkTensorProduct α M x) :
    Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ T.module) := by
  sorry

/-- The tensor-product stalk interface is inhabited for every point. -/
theorem exists_associatedSheaf_stalkTensorProduct
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    Nonempty (StalkTensorProduct α M x) := by
  sorry

/-- Source-facing form of the stalk formula. -/
theorem associatedSheaf_stalk_tensor_formula
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    ∃ T : StalkTensorProduct α M x,
      Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ T.module) := by
  rcases exists_associatedSheaf_stalkTensorProduct α M x with ⟨T⟩
  exact ⟨T, associatedSheaf_stalk_iso α M x T⟩

/-! The Hom formula uses the canonical `R`-action on global sections induced
by `α`. -/

/-- The `R`-module of global sections of `G` induced by `α`. -/
noncomputable def globalSectionsModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (G : Mod X.structureSheaf) : ModuleCat R := by
  exact (ModuleCat.restrictScalars α).obj
    (sheafModuleSections X.structureSheaf G (⊤ : Opens X.carrier))

/-- The associated-sheaf Hom formula. -/
theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R)
    (G : Mod X.structureSheaf) :
    Nonempty ((associatedSheaf α M ⟶ G) ≃
      (M ⟶ globalSectionsModule α G)) := by
  sorry

/-! ## Restriction and the local presentation lemma -/

/-- The ring map on global sections induced by a morphism of ringed spaces. -/
noncomputable def ringedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X) :
    globalSectionsRing X →+* globalSectionsRing Y := by
  have htop : (Opens.map g.continuous).obj (⊤ : Opens X.carrier) =
      (⊤ : Opens Y.carrier) := by
    ext y
    simp
  have hObj :
      Y.structureSheaf.obj.obj
          (op ((Opens.map g.continuous).obj (⊤ : Opens X.carrier))) =
        Y.structureSheaf.obj.obj (op (⊤ : Opens Y.carrier)) := by
    rw [htop]
  exact (g.sharp.hom.app (op (⊤ : Opens X.carrier)) ≫ eqToHom hObj).hom

/-- The module extension-of-scalars datum used by the restriction lemma. -/
structure RestrictionScalarExtension
    {X Y : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R)
    (g : RingedSpaceHom Y X) where
  module : ModuleCat (globalSectionsRing Y)
  unit : M ⟶
    (ModuleCat.restrictScalars ((ringedSpaceGlobalSectionsMap g).comp α)).obj module
  homEquiv : ∀ N : ModuleCat (globalSectionsRing Y),
    (module ⟶ N) ≃
      (M ⟶
        (ModuleCat.restrictScalars
          ((ringedSpaceGlobalSectionsMap g).comp α)).obj N)
  homEquiv_unit : ∀ (N : ModuleCat (globalSectionsRing Y))
      (f : module ⟶ N),
    homEquiv N f = unit ≫
      (ModuleCat.restrictScalars ((ringedSpaceGlobalSectionsMap g).comp α)).map f

/-- Restriction of an associated sheaf is associated to the scalar-extension
module `Γ(Y, O_Y) ⊗_R M`.  The explicit module object is existential because
the surrounding `RingCat` API also supports noncommutative sheaves of rings. -/
theorem restrict_associatedSheaf
    {X Y : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R)
    (g : RingedSpaceHom Y X)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)] :
    ∃ E : RestrictionScalarExtension α M g,
      Nonempty ((sheafModuleRingedSpacePullback g).obj (associatedSheaf α M) ≅
        associatedSheaf (RingHom.id _) E.module) := by
  sorry

/-- A fundamental system of quasi-compact open neighbourhoods at a point. -/
def HasQuasiCompactNeighborhoodBasis {X : RingedSpace.{v}} (x : X) : Prop :=
  ∃ (ι : Type v) (E : ι → Set X),
    IsFundamentalSystemOfNeighborhoods x E ∧ ∀ i, IsCompact (E i)

/-- If `x` has a fundamental system of quasi-compact neighbourhoods, a
quasi-coherent module is locally associated to a module of sections. -/
theorem exists_local_associatedSheaf
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (x : X)
    (hX : HasQuasiCompactNeighborhoodBasis x) (hF : IsQuasiCoherent F) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat (globalSectionsRing (ringedOpenSubspace X U)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
          associatedSheaf (RingHom.id _) M) := by
  sorry

/-! ## The countable wedge example -/

/-- A universe-correct countable index for free sheaves of modules. -/
abbrev CountableIndex : Type v := ULift.{v} ℕ

/-- A universe-correct index for the matrix entries. -/
abbrev CountablePairIndex : Type v := ULift.{v} (ℕ × ℕ)

/-- A cutoff function used in the wedge-of-lines example. -/
structure CutoffFunction where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  vanishes_on : ∀ x, x ∈ Set.Ioo (-1 : ℝ) 1 → toFun x = 0
  is_one_on : ∀ x, x < -2 ∨ 2 < x → toFun x = 1

instance : CoeFun CutoffFunction (fun _ ↦ ℝ → ℝ) :=
  ⟨CutoffFunction.toFun⟩

/-- The scaled cutoff functions `f_n(x) = f(nx)`. -/
def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x ↦ f ((n : ℝ) * x)

/-- A family of coefficients is locally finite in the branch index. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ K : Finset ℕ, ∀ z : X, z ∈ U → ∀ i, i ∉ K → c j i z = 0

/-- The finite-linear-combination failure used in the wedge example. -/
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

/-- The countable wedge of real lines with its cutoff and matrix-map data. -/
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
      -(1 : ℝ) / (n + 1 : ℝ) < x ∧ x < (1 : ℝ) / (n + 1 : ℝ)
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

/-- The wedge example supplies the morphism whose image of the high-index
generator is not a finite linear combination on the indicated neighbourhoods. -/
theorem exists_wedgeOfLinesExample : Nonempty WedgeOfLinesExample := by
  sorry

/-! The final two consequences in the source are explicitly presented there
as expectations (“there should be ...” and “similarly ...”), so they are not
asserted as theorem declarations at this statement-only stage. -/

end

end Formalization.Books.Modules.Unit10
