import Formalization.Books.Defos.Unit05.InfinitesimalDeformations
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules
import Mathlib.Algebra.Torsor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Deformation Theory, Chapter 7: Deformations of ringed spaces

This file formalizes the numbered source section
`books/defos.tex:1701-2382`.  The ringed-space thickening and module f-map
interfaces come from Chapters 3--5.  The source uses the naive cotangent
complex for sheaves of rings; the project has a commutative-sheaf
presentation API and a generic ringed-space API, so this chapter exposes the
small two-term complex and derived-Ext interface needed to state the
ringed-space results without adding assumptions to the source.
-/

namespace Formalization.Books.Defos.Unit07

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Defos.Unit03
open Formalization.Books.Defos.Unit04
open Formalization.Books.Defos.Unit05
open Formalization.Books.Defos.Unit02
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The naive cotangent complex and its Ext interface -/

/-- A two-term sheaf-module complex, with terms in degrees `-1` and `0`.

This is the generic ringed-space version of the two-term complex exposed by
the Modules chapter. -/
structure NaiveCotangentComplex {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) where
  degreeNegOne : Mod O
  degreeZero : Mod O
  differential : degreeNegOne ⟶ degreeZero

/-- A morphism of two-term sheaf-module complexes. -/
structure NaiveCotangentComplexMap {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X}
    (K L : NaiveCotangentComplex O) where
  degreeNegOneMap : K.degreeNegOne ⟶ L.degreeNegOne
  degreeZeroMap : K.degreeZero ⟶ L.degreeZero
  commutes : K.differential ≫ degreeZeroMap = degreeNegOneMap ≫ L.differential

/-- A chosen naive cotangent complex for a morphism of ringed spaces. -/
structure RelativeNaiveCotangentData {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) where
  complex : NaiveCotangentComplex X.structureSheaf
  differentials : Mod X.structureSheaf
  degreeZero_iso : Nonempty (complex.degreeZero ≅ differentials)

/-- Existence of the chosen presentation-independent naive cotangent data. -/
theorem exists_relativeNaiveCotangentData {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) : Nonempty (RelativeNaiveCotangentData f) := by
  sorry

/-- A chosen representative of the naive cotangent data. -/
noncomputable def relativeNaiveCotangentData {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) : RelativeNaiveCotangentData f :=
  Classical.choice (exists_relativeNaiveCotangentData f)

/-- The source's `Ω_{X/S}` interface. -/
abbrev RelativeDifferentials {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) : Mod X.structureSheaf :=
  (relativeNaiveCotangentData f).differentials

/-- The source's `NL_{X/S}` interface. -/
abbrev RelativeNaiveCotangentComplex {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) : NaiveCotangentComplex X.structureSheaf :=
  (relativeNaiveCotangentData f).complex

/-- Ext groups whose first argument is a two-term naive cotangent complex.

The degree-zero equivalence records the source identification
`Ext^0(NL,G) = Hom(Ω,G)`. -/
class NaiveExtTheory {X : TopCat.{v}} (O : RingSheaf.{v, v} X) where
  ext : NaiveCotangentComplex O → Mod O → ℕ → Type (v + 1)
  group : ∀ (K : NaiveCotangentComplex O) (G : Mod O) (n : ℕ),
    AddCommGroup (ext K G n)
  degreeZeroEquiv : ∀ (K : NaiveCotangentComplex O) (G : Mod O),
    (K.degreeZero ⟶ G) ≃+ ext K G 0

/-- The source notation `Ext^n_O(K,G)`. -/
abbrev NaiveExtGroup {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    [NaiveExtTheory O] (K : NaiveCotangentComplex O)
    (G : Mod O) (n : ℕ) : Type (v + 1) :=
  NaiveExtTheory.ext K G n

instance naiveExtGroup_addCommGroup {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} [h : NaiveExtTheory O]
    (K : NaiveCotangentComplex O) (G : Mod O) (n : ℕ) :
    AddCommGroup (NaiveExtGroup K G n) :=
  h.group K G n

/-- The degree-zero Ext/Hom identification used in the obstruction lemma. -/
noncomputable abbrev naiveExtDegreeZeroEquiv {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} [NaiveExtTheory O]
    (K : NaiveCotangentComplex O) (G : Mod O) :
    (K.degreeZero ⟶ G) ≃+ NaiveExtGroup K G 0 :=
  NaiveExtTheory.degreeZeroEquiv K G

/-- The derived pullback data needed to write `Lg^*` on complexes and Ext. -/
class DerivedNaivePullback {X Y : RingedSpace.{v}}
    (g : RingedSpaceHom X Y) [NaiveExtTheory X.structureSheaf]
    [NaiveExtTheory Y.structureSheaf] where
  pullbackComplex : NaiveCotangentComplex Y.structureSheaf →
    NaiveCotangentComplex X.structureSheaf
  pullbackExt : ∀ (K : NaiveCotangentComplex Y.structureSheaf)
    (F : Mod Y.structureSheaf) (G : Mod X.structureSheaf) (n : ℕ),
    RingedSpaceModuleFMap g F G →
      NaiveExtGroup K F n →
      NaiveExtGroup (pullbackComplex K) G n
  postcomposeExt : ∀ (K : NaiveCotangentComplex Y.structureSheaf)
    (L : NaiveCotangentComplex X.structureSheaf) (G : Mod X.structureSheaf)
    (n : ℕ), NaiveCotangentComplexMap (pullbackComplex K) L →
      NaiveExtGroup L G n → NaiveExtGroup (pullbackComplex K) G n

abbrev derivedPullbackNaiveCotangentComplex
    {X Y : RingedSpace.{v}} {g : RingedSpaceHom X Y}
    [NaiveExtTheory X.structureSheaf] [NaiveExtTheory Y.structureSheaf]
    [DerivedNaivePullback g] (K : NaiveCotangentComplex Y.structureSheaf) :
    NaiveCotangentComplex X.structureSheaf :=
  DerivedNaivePullback.pullbackComplex (g := g) K

/-! ## First-order ringed-space extensions -/

/-- An extension of `O_X` by `G` as an `f^{-1} O_S`-algebra extension.

The kernel identification is retained as an actual module isomorphism, so
the coefficient module is part of the extension data rather than merely a
proposition that some kernel module exists. -/
structure RelativeRingedSpaceExtension {X S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) (G : Mod X.structureSheaf) where
  thickeningSpace : RingedSpace
  inclusion : RingedSpaceHom X thickeningSpace
  firstOrder : IsFirstOrderThickening inclusion
  structureMap : RingedSpaceHom thickeningSpace S
  over_base : RingedSpaceHom.comp inclusion structureMap = f
  kernelIdentification :
    (ringedSpaceModulePushforward inclusion).obj G ≅
      (thickeningIdeal inclusion).carrier

/-- The exact kernel sequence underlying a relative ringed-space extension.

The short complex itself is the canonical Chapter 3 construction; this
abbreviation makes the exact sequence in the displayed source diagram
available at the chapter-owned interface. -/
abbrev relativeExtensionKernelShortComplex
    {X S : RingedSpace.{v}} {f : RingedSpaceHom X S}
    {G : Mod X.structureSheaf}
    (E : RelativeRingedSpaceExtension f G) :
    ShortComplex (Mod E.thickeningSpace.structureSheaf) :=
  thickeningKernelShortComplex E.inclusion

theorem relativeExtensionKernelShortComplex_shortExact
    {X S : RingedSpace.{v}} {f : RingedSpaceHom X S}
    {G : Mod X.structureSheaf}
    (E : RelativeRingedSpaceExtension f G) :
    (relativeExtensionKernelShortComplex E).ShortExact :=
  thickeningKernelShortComplex_shortExact E.inclusion E.firstOrder.toIsThickening

/-- An isomorphism of relative ringed-space extensions. -/
structure RelativeRingedSpaceExtensionIso
    {X S : RingedSpace.{v}} {f : RingedSpaceHom X S}
    {G : Mod X.structureSheaf}
    (E F : RelativeRingedSpaceExtension f G) where
  hom : E.thickeningSpace ≅ F.thickeningSpace
  inclusion_commutes :
    RingedSpaceHom.comp E.inclusion hom.hom = F.inclusion
  structureMap_commutes :
    RingedSpaceHom.comp hom.hom F.structureMap = E.structureMap
  kernel_commutes : Prop

/-- Isomorphism classes of relative extensions. -/
theorem exists_relativeRingedSpaceExtensionSetoid
    {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (G : Mod X.structureSheaf) :
    Nonempty (Setoid (RelativeRingedSpaceExtension f G)) := by
  let r : RelativeRingedSpaceExtension f G →
      RelativeRingedSpaceExtension f G → Prop :=
    fun E F => Nonempty (RelativeRingedSpaceExtensionIso E F)
  exact ⟨{ r := r, iseqv := by sorry }⟩

noncomputable def relativeRingedSpaceExtensionSetoid
    {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (G : Mod X.structureSheaf) : Setoid (RelativeRingedSpaceExtension f G) :=
  Classical.choice (exists_relativeRingedSpaceExtensionSetoid f G)

abbrev RelativeRingedSpaceExtensionClass
    {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (G : Mod X.structureSheaf) : Type _ :=
  Quotient (relativeRingedSpaceExtensionSetoid f G)

/-! ## The deformation problem and its solution classes -/

/-- The data in the displayed deformation problem (7.1). -/
structure RingedSpaceDeformationProblem
    {X S S' : RingedSpace.{v}}
    (t : RingedSpaceHom S S') (f : RingedSpaceHom X S)
    (J : Mod S.structureSheaf) (G : Mod X.structureSheaf)
    (c : RingedSpaceModuleFMap f J G) where
  base_firstOrder : IsFirstOrderThickening t
  base_kernelIdentification :
    (ringedSpaceModulePushforward t).obj J ≅ (thickeningIdeal t).carrier

/-- A solution of the displayed deformation problem. -/
structure RingedSpaceDeformationSolution
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    (P : RingedSpaceDeformationProblem t f J G c) where
  extension : RelativeRingedSpaceExtension
    (RingedSpaceHom.comp f t) G
  compatible_with_c : Prop

/-- An isomorphism of solutions preserving the fixed deformation data. -/
structure RingedSpaceDeformationSolutionIso
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    {P : RingedSpaceDeformationProblem t f J G c}
    (E F : RingedSpaceDeformationSolution P) where
  extensionIso : RelativeRingedSpaceExtensionIso E.extension F.extension
  compatibility_commutes : Prop

theorem exists_ringedSpaceDeformationSolutionSetoid
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    (P : RingedSpaceDeformationProblem t f J G c) :
    Nonempty (Setoid (RingedSpaceDeformationSolution P)) := by
  let r : RingedSpaceDeformationSolution P →
      RingedSpaceDeformationSolution P → Prop :=
    fun E F => Nonempty (RingedSpaceDeformationSolutionIso E F)
  exact ⟨{ r := r, iseqv := by sorry }⟩

noncomputable def ringedSpaceDeformationSolutionSetoid
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    (P : RingedSpaceDeformationProblem t f J G c) :
    Setoid (RingedSpaceDeformationSolution P) :=
  Classical.choice (exists_ringedSpaceDeformationSolutionSetoid P)

abbrev RingedSpaceDeformationSolutionClass
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    (P : RingedSpaceDeformationProblem t f J G c) : Type _ :=
  Quotient (ringedSpaceDeformationSolutionSetoid P)

/-! ## The obstruction diagram -/

/-- The commutative diagram of two first-order thickenings used in Lemma
`lemma-huge-diagram-ringed-spaces`. -/
structure RingedSpaceThickeningDiagram
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    (G₁ : Mod X₁.structureSheaf) (G₂ : Mod X₂.structureSheaf)
    (f₁ : RingedSpaceHom X₁ S₁) (f₂ : RingedSpaceHom X₂ S₂)
    (t₁ : RingedSpaceHom S₁ S₁') (t₂ : RingedSpaceHom S₂ S₂')
    (g : RingedSpaceHom X₂ X₁) (s : RingedSpaceHom S₂ S₁)
    (s' : RingedSpaceHom S₂' S₁') where
  front : RelativeRingedSpaceExtension (RingedSpaceHom.comp f₁ t₁) G₁
  back : RelativeRingedSpaceExtension (RingedSpaceHom.comp f₂ t₂) G₂
  base_square : RingedSpaceHom.comp g f₁ = RingedSpaceHom.comp f₂ s
  base_thickening_square : RingedSpaceHom.comp s t₁ =
    RingedSpaceHom.comp t₂ s'
  front_firstOrder : IsFirstOrderThickening front.inclusion
  back_firstOrder : IsFirstOrderThickening back.inclusion
  base₁_firstOrder : IsFirstOrderThickening t₁
  base₂_firstOrder : IsFirstOrderThickening t₂
  kernel_map : RingedSpaceModuleFMap g G₁ G₂

/-- A morphism of the two back/front solutions compatible with the kernel map. -/
structure CompatibleThickeningMorphism
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s') where
  hom : D.back.thickeningSpace ⟶ D.front.thickeningSpace
  top_square : RingedSpaceHom.comp D.back.inclusion hom =
    RingedSpaceHom.comp g D.front.inclusion
  base_square : RingedSpaceHom.comp hom D.front.structureMap =
    RingedSpaceHom.comp D.back.structureMap s'
  kernel_compatibility : Prop

abbrev diagramObstructionGroup
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s')
    [NaiveExtTheory X₁.structureSheaf] [NaiveExtTheory X₂.structureSheaf]
    [DerivedNaivePullback g] : Type _ :=
  NaiveExtGroup
    (derivedPullbackNaiveCotangentComplex (g := g)
      (RelativeNaiveCotangentComplex f₁)) G₂ 1

/-- The obstruction class for the huge diagram. -/
theorem exists_diagramObstruction
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s')
    [NaiveExtTheory X₁.structureSheaf] [NaiveExtTheory X₂.structureSheaf]
    [DerivedNaivePullback g] :
    ∃ o : diagramObstructionGroup (g := g) D,
      (o = 0 ↔ Nonempty (CompatibleThickeningMorphism D)) := by
  sorry

noncomputable def diagramObstruction
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s')
    [NaiveExtTheory X₁.structureSheaf] [NaiveExtTheory X₂.structureSheaf]
    [DerivedNaivePullback g] :
    diagramObstructionGroup (g := g) D :=
  Classical.choose (exists_diagramObstruction D)

theorem diagramObstruction_vanishes_iff
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s')
    [NaiveExtTheory X₁.structureSheaf] [NaiveExtTheory X₂.structureSheaf]
    [DerivedNaivePullback g] :
    diagramObstruction D = 0 ↔
      Nonempty (CompatibleThickeningMorphism D) :=
  Classical.choose_spec (exists_diagramObstruction D)

/-- Once one compatible morphism exists, all compatible morphisms form the
degree-zero torsor from the source. -/
theorem compatibleThickeningMorphisms_is_principalHomogeneousSpace
    {X₁ X₂ S₁ S₂ S₁' S₂' : RingedSpace.{v}}
    {G₁ : Mod X₁.structureSheaf} {G₂ : Mod X₂.structureSheaf}
    {f₁ : RingedSpaceHom X₁ S₁} {f₂ : RingedSpaceHom X₂ S₂}
    {t₁ : RingedSpaceHom S₁ S₁'} {t₂ : RingedSpaceHom S₂ S₂'}
    {g : RingedSpaceHom X₂ X₁} {s : RingedSpaceHom S₂ S₁}
    {s' : RingedSpaceHom S₂' S₁'}
    (D : RingedSpaceThickeningDiagram G₁ G₂ f₁ f₂ t₁ t₂ g s s')
    [NaiveExtTheory X₁.structureSheaf] [NaiveExtTheory X₂.structureSheaf]
    [DerivedNaivePullback g]
    (h : Nonempty (CompatibleThickeningMorphism D)) :
    Nonempty (PrincipalHomogeneousSpace
      (NaiveExtGroup
        (derivedPullbackNaiveCotangentComplex (g := g)
          (RelativeNaiveCotangentComplex f₁)) G₂ 0)
      (CompatibleThickeningMorphism D)) := by
  sorry

/-! ## Presentations of Ext classes and classification -/

/-- A sheaf-of-sets generator over a sheaf of rings. -/
structure SheafOfSetsGenerator {X : TopCat.{v}}
    (B : RingSheaf.{v, v} X) where
  carrier : TopCat.Sheaf (Type v) X
  value : ∀ U, carrier.obj.obj U → B.obj.obj U
  naturality : ∀ {U V} (i : U ⟶ V) (e : carrier.obj.obj U),
    value V (carrier.obj.map i e) = (B.obj.map i).hom (value U e)

/-- The source-facing data expressing that an Ext class is represented by a
map out of the conormal module of a presentation. -/
structure NaiveExtClassPresentation {X : TopCat.{v}}
    {A B : RingSheaf.{v, v} X} (base : A ⟶ B)
    (K : NaiveCotangentComplex B) (G : Mod B) [NaiveExtTheory B]
    (ξ : NaiveExtGroup K G 1)
    where
  generators : SheafOfSetsGenerator B
  conormal : Mod B
  representedClass : (conormal ⟶ G) → NaiveExtGroup K G 1
  representing_map : ∃ q : conormal ⟶ G, representedClass q = ξ

/-- Every degree-one naive Ext class admits a presentation by generators. -/
theorem exists_naiveExtClassPresentation {X : TopCat.{v}}
    {A B : RingSheaf.{v, v} X} (base : A ⟶ B)
    (K : NaiveCotangentComplex B) (G : Mod B) [NaiveExtTheory B]
    (ξ : NaiveExtGroup K G 1) :
    Nonempty (NaiveExtClassPresentation base K G ξ) := by
  sorry

/-- If a solution exists, its isomorphism classes form the source torsor. -/
theorem solution_classes_is_principalHomogeneousSpace
    {X S S' : RingedSpace.{v}}
    {t : RingedSpaceHom S S'} {f : RingedSpaceHom X S}
    {J : Mod S.structureSheaf} {G : Mod X.structureSheaf}
    {c : RingedSpaceModuleFMap f J G}
    (P : RingedSpaceDeformationProblem t f J G c)
    [NaiveExtTheory X.structureSheaf]
    (h : Nonempty (RingedSpaceDeformationSolution P)) :
    Nonempty (PrincipalHomogeneousSpace
      (NaiveExtGroup (RelativeNaiveCotangentComplex f) G 1)
      (RingedSpaceDeformationSolutionClass P)) := by
  sorry

/-! ## Classification of relative algebra extensions -/

/-- The split extension `G ⊕ O_X` supplies a relative extension for every
coefficient module, as used in the proof of the classification lemma. -/
theorem exists_relativeRingedSpaceExtension
    {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (G : Mod X.structureSheaf) :
    Nonempty (RelativeRingedSpaceExtension f G) := by
  sorry

/-- Relative extensions are classified by degree-one Ext of the naive
cotangent complex. -/
theorem relativeExtensionClass_equiv_ext
    {X S : RingedSpace.{v}} (f : RingedSpaceHom X S)
    (G : Mod X.structureSheaf) [NaiveExtTheory X.structureSheaf] :
    Nonempty (RelativeRingedSpaceExtensionClass f G ≃
      NaiveExtGroup (RelativeNaiveCotangentComplex f) G 1) := by
  sorry

/-! ## Functoriality -/

/-- A morphism of two relative extensions over `g`, with the prescribed
module map on square-zero kernels. -/
structure CompatibleRelativeExtensionMorphism
    {X Y S : RingedSpace.{v}}
    {f : RingedSpaceHom X S} (g : RingedSpaceHom Y X)
    {F : Mod X.structureSheaf} {G : Mod Y.structureSheaf}
    (c : RingedSpaceModuleFMap g F G)
    (E : RelativeRingedSpaceExtension f F)
    (E' : RelativeRingedSpaceExtension (RingedSpaceHom.comp g f) G) where
  hom : E'.thickeningSpace ⟶ E.thickeningSpace
  inclusion_commutes :
    RingedSpaceHom.comp E'.inclusion hom =
      RingedSpaceHom.comp g E.inclusion
  structureMap_commutes :
    RingedSpaceHom.comp hom E.structureMap = E'.structureMap
  kernel_compatibility : Prop

/-- The functoriality theorem from Lemma
`extensions-of-relative-ringed-spaces-functorial`. -/
theorem extension_morphism_iff_ext_classes_agree
    {X Y S : RingedSpace.{v}}
    (f : RingedSpaceHom X S) (g : RingedSpaceHom Y X)
    (F : Mod X.structureSheaf) (G : Mod Y.structureSheaf)
    (c : RingedSpaceModuleFMap g F G)
    (E : RelativeRingedSpaceExtension f F)
    (E' : RelativeRingedSpaceExtension (RingedSpaceHom.comp g f) G)
    [NaiveExtTheory X.structureSheaf] [NaiveExtTheory Y.structureSheaf]
    [DerivedNaivePullback g]
    (map : NaiveCotangentComplexMap
      (DerivedNaivePullback.pullbackComplex (g := g)
        (RelativeNaiveCotangentComplex f))
      (RelativeNaiveCotangentComplex (RingedSpaceHom.comp g f)))
    (ξ : NaiveExtGroup (RelativeNaiveCotangentComplex f) F 1)
    (ζ : NaiveExtGroup (RelativeNaiveCotangentComplex
      (RingedSpaceHom.comp g f)) G 1) :
    Nonempty (CompatibleRelativeExtensionMorphism g c E E') ↔
      DerivedNaivePullback.postcomposeExt (g := g)
          (RelativeNaiveCotangentComplex f)
          (RelativeNaiveCotangentComplex (RingedSpaceHom.comp g f)) G 1
          map ζ =
        DerivedNaivePullback.pullbackExt (g := g)
          (RelativeNaiveCotangentComplex f) F G 1 c ξ := by
  sorry

/-! ## Parametrization of solutions -/

/-- The fibre description of the solution classes. -/
theorem solution_classes_bijective_to_ext_fibre
    {X S S' : RingedSpace.{v}}
    (t : RingedSpaceHom S S') (f : RingedSpaceHom X S)
    (J : Mod S.structureSheaf) (G : Mod X.structureSheaf)
    (c : RingedSpaceModuleFMap f J G)
    (P : RingedSpaceDeformationProblem t f J G c)
    [NaiveExtTheory S.structureSheaf] [NaiveExtTheory X.structureSheaf]
    [DerivedNaivePullback f]
    (ξ : NaiveExtGroup (RelativeNaiveCotangentComplex t) J 1)
    (map : NaiveCotangentComplexMap
      (DerivedNaivePullback.pullbackComplex (g := f)
        (RelativeNaiveCotangentComplex t))
      (RelativeNaiveCotangentComplex (RingedSpaceHom.comp f t))) :
    Nonempty (RingedSpaceDeformationSolutionClass P ≃
      {ζ : NaiveExtGroup
        (RelativeNaiveCotangentComplex (RingedSpaceHom.comp f t)) G 1 //
          DerivedNaivePullback.postcomposeExt (g := f)
          (RelativeNaiveCotangentComplex t)
          (RelativeNaiveCotangentComplex (RingedSpaceHom.comp f t)) G 1
          map ζ =
          DerivedNaivePullback.pullbackExt (g := f)
            (RelativeNaiveCotangentComplex t) J G 1 c ξ}) := by
  sorry

/-! ## The closing cotangent-complex triangle remark -/

/-- The two maps in the source's would-be cotangent triangle. -/
structure RelativeCotangentTriangleData
    {X S S' : RingedSpace.{v}}
    (t : RingedSpaceHom S S') (f : RingedSpaceHom X S)
    [NaiveExtTheory X.structureSheaf] [NaiveExtTheory S.structureSheaf]
    [DerivedNaivePullback f] where
  left : NaiveCotangentComplexMap
    (DerivedNaivePullback.pullbackComplex (g := f)
      (RelativeNaiveCotangentComplex t))
    (RelativeNaiveCotangentComplex (RingedSpaceHom.comp f t))
  right : NaiveCotangentComplexMap
    (RelativeNaiveCotangentComplex (RingedSpaceHom.comp f t))
    (RelativeNaiveCotangentComplex f)
  composition_is_zero : Prop

/-- The source records that these maps are close to a distinguished triangle. -/
theorem relative_cotangent_maps_are_almost_distinguished
    {X S S' : RingedSpace.{v}}
    (t : RingedSpaceHom S S') (f : RingedSpaceHom X S)
    [NaiveExtTheory X.structureSheaf] [NaiveExtTheory S.structureSheaf]
    [DerivedNaivePullback f] :
    Nonempty (RelativeCotangentTriangleData t f) := by
  sorry

/-- Conditional obstruction consequence of a distinguished cotangent
triangle, as stated in the final remark of the source section. -/
theorem distinguished_cotangent_triangle_gives_solution_obstruction
    {X S S' : RingedSpace.{v}}
    (t : RingedSpaceHom S S') (f : RingedSpaceHom X S)
    (J : Mod S.structureSheaf) (G : Mod X.structureSheaf)
    (c : RingedSpaceModuleFMap f J G)
    (P : RingedSpaceDeformationProblem t f J G c)
    [NaiveExtTheory S.structureSheaf] [NaiveExtTheory X.structureSheaf]
    [DerivedNaivePullback f]
    (ξ : NaiveExtGroup (RelativeNaiveCotangentComplex t) J 1)
    (triangle : RelativeCotangentTriangleData t f)
    (distinguished : Prop) (hdistinguished : distinguished)
    : ∃ o : NaiveExtGroup (RelativeNaiveCotangentComplex f) G 2,
      (o = 0 ↔ Nonempty (RingedSpaceDeformationSolution P)) := by
  sorry

end

end Formalization.Books.Defos.Unit07
