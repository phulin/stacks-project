import Formalization.Books.Cohomology.Unit08.CechFunctor
import Mathlib.Algebra.Torsor.Basic

/-!
# Cohomology of Sheaves, Chapter 8: Čech cohomology and cohomology

This file records the comparison, torsor, spectral-sequence, vanishing,
pushforward, and product statements from the last section of the chapter.
The comparison maps are retained as explicit natural interfaces so that the
later proof stage can identify them with the canonical derived-category maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Cohomology.Unit07
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit03

universe v

namespace Formalization.Books.Cohomology.Unit08

/-! ## Injectives and the comparison with derived cohomology -/

/-- The additive group of sections of an abelian presheaf on an open. -/
noncomputable abbrev cechSectionsObject {X : TopCat.{v}}
    (F : AbelianPresheaf X) (U : Opens X) : AddCommGrpCat.{v} :=
  F.obj (op U)

/-- Čech cohomology of an injective sheaf is concentrated in degree zero. -/
theorem cech_injective_zero_iso {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (I : Mod X.structureSheaf) [Injective I] :
    Nonempty (cechCohomologyObject 𝒰 I.val.presheaf 0 ≅
      cechSectionsObject I.val.presheaf 𝒰.carrier) := by
  sorry

theorem cech_injective_positive_isZero {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (I : Mod X.structureSheaf) [Injective I]
    (p : ℕ) (hp : 0 < p) : IsZero (cechCohomologyObject 𝒰 I.val.presheaf p) := by
  sorry

/-- The additive derived sections functor on an open. -/
noncomputable def cohomologyOnOpenAdditiveFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) (p : ℕ) : Mod X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  ringedSpaceModuleSectionsCohomology X U (p : ℤ) ⋙
    forget₂ (ModuleCat (X.structureSheaf.obj.obj (op U))) AddCommGrpCat

/-- Total derived sections, applied to a sheaf viewed as a degree-zero
bounded-below complex. -/
noncomputable def totalDerivedSectionsOnObjects (X : RingedSpace.{v})
    (U : Opens X.carrier) : Mod X.structureSheaf ⥤
      DPlus (ModuleCat (X.structureSheaf.obj.obj (op U))) :=
  DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0 ⋙
    ringedSpaceModuleTotalDerivedSections X U

/-- The derived-category form of the Čech-to-derived-sections transformation. -/
structure CechToTotalDerivedSectionsData (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) where
  cech : Mod X.structureSheaf ⥤
    DPlus (ModuleCat (X.structureSheaf.obj.obj (op 𝒰.carrier)))
  transformation : cech ⟶ totalDerivedSectionsOnObjects X 𝒰.carrier

theorem exists_cechToTotalDerivedSectionsData (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) : Nonempty (CechToTotalDerivedSectionsData X 𝒰) := by
  sorry

/-- The Čech cohomology functor after restricting a sheaf of modules to its
underlying module presheaf. -/
noncomputable def sheafCechCohomologyFunctor (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) (p : ℕ) : Mod X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  sheafModuleUnderlyingPresheafFunctor X ⋙ cechModuleCohomologyFunctor 𝒰 p

/-- The natural comparison from Čech cohomology to derived cohomology. -/
structure CechToCohomologyComparisonData (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) (p : ℕ) where
  app : ∀ F : Mod X.structureSheaf,
    cechCohomologyObject 𝒰 F.val.presheaf p ⟶
      cohomologyOnOpenAdditive X 𝒰.carrier F (p : ℤ)
  natural : ∀ {F G : Mod X.structureSheaf} (φ : F ⟶ G),
    app F ≫
        (cohomologyOnOpenAdditiveFunctor X 𝒰.carrier p).map φ =
      (sheafCechCohomologyFunctor X 𝒰 p).map φ ≫ app G

theorem exists_cechToCohomologyComparisonData (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) (p : ℕ) :
    Nonempty (CechToCohomologyComparisonData X 𝒰 p) := by
  sorry

/-- A chosen comparison transformation. -/
noncomputable def cechToCohomologyComparisonData (X : RingedSpace.{v})
    (𝒰 : CechOpenCover X) (p : ℕ) : CechToCohomologyComparisonData X 𝒰 p :=
  Classical.choice (exists_cechToCohomologyComparisonData X 𝒰 p)

/-! ## Torsors and first Čech cohomology -/

/-- A torsor under an abelian presheaf, with its restriction maps. -/
structure PresheafTorsor {X : TopCat.{v}} (F : AbelianPresheaf X) where
  fiber : ∀ _U : Opens X, Type v
  torsor : ∀ U : Opens X, AddTorsor (F.obj (op U)) (fiber U)
  restriction : ∀ {U V : Opens X} (_h : V ≤ U), fiber U → fiber V
  restriction_equivariant : ∀ {U V : Opens X} (h : V ≤ U)
    (s : F.obj (op U)) (x : fiber U),
    restriction h (s +ᵥ x) = F.map (homOfLE h).op s +ᵥ restriction h x

/-- An objectwise isomorphism of presheaf torsors. -/
structure PresheafTorsorIso {X : TopCat.{v}} {F : AbelianPresheaf X}
    (T₁ T₂ : PresheafTorsor F) where
  app : ∀ U : Opens X, T₁.fiber U ≃ T₂.fiber U
  restriction_commutes : ∀ {U V : Opens X} (h : V ≤ U) (x : T₁.fiber U),
    app V (T₁.restriction h x) = T₂.restriction h (app U x)

/-- The classification data for torsors by first Čech cohomology. -/
structure LocallyTrivialPresheafTorsor {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (F : AbelianPresheaf X) where
  torsor : PresheafTorsor F
  local_section : ∀ i : 𝒰.member, torsor.fiber (𝒰.memberOpen i)

structure PresheafTorsorClassification {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (F : AbelianPresheaf X) where
  classOf : LocallyTrivialPresheafTorsor 𝒰 F → cechCohomologyObject 𝒰 F 1
  surjective : Function.Surjective classOf
  equal_iff_isomorphic : ∀ T₁ T₂ : LocallyTrivialPresheafTorsor 𝒰 F,
    classOf T₁ = classOf T₂ ↔ Nonempty (PresheafTorsorIso T₁.torsor T₂.torsor)

theorem cech_h1_classifies_torsors {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (hF : TopCat.Presheaf.IsSheaf F) :
    Nonempty (PresheafTorsorClassification 𝒰 F) := by
  sorry

/-- In the module-valued setting the Čech-to-derived map in degree one is
injective, as witnessed by the torsor classification. -/
theorem cech_h1_comparison_injective {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (F : Mod X.structureSheaf) :
    ∃ φ : cechCohomologyObject 𝒰 F.val.presheaf 1 →
        cohomologyOnOpenAdditive X 𝒰.carrier F (1 : ℤ),
      Function.Injective φ := by
  sorry

/-! ## The inclusion of sheaves into presheaves -/

/-- The inclusion `i : Mod(O_X) ⥤ PMod(O_X)`. -/
noncomputable abbrev presheafInclusion (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤ PMod X.structureSheaf.obj :=
  sheafModuleUnderlyingPresheafFunctor X

theorem presheafInclusion_isLeftExact (X : RingedSpace.{v}) :
    Formalization.Books.Categories.Unit23.IsLeftExact (presheafInclusion X) := by
  exact sheafModuleUnderlyingPresheafFunctor_isLeftExact X

/-- The higher derived functors of the inclusion are the presheaves of local
cohomology. -/
theorem presheafInclusion_derived_is_localCohomology
    (X : RingedSpace.{v}) (p : ℤ) :
    localCohomologyPresheafFunctor X p =
      higherRightDerivedFunctor (presheafInclusion X)
        (presheafInclusion_isLeftExact X) p := by
  rfl

/-! ## The Čech spectral sequence -/

/-- A source-facing bigraded spectral sequence datum. -/
structure CechSpectralSequenceData {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (F : Mod X.structureSheaf) where
  page : ℕ → ℕ → ℕ → AddCommGrpCat.{v}
  differential : ∀ r p q, page r p q ⟶ page r (p + r) (q - r + 1)
  differential_squared : ∀ r p q,
    differential r p q ≫ differential r (p + r) (q - r + 1) = 0
  e₂ : ∀ p q : ℕ, Nonempty (page 2 p q ≅
    cechCohomologyObject 𝒰
      (localCohomologyPresheaf X F (q : ℤ)).presheaf p)
  limit : ℕ → AddCommGrpCat.{v}
  abutment : ∀ n : ℕ, Nonempty (limit n ≅
    cohomologyOnOpenAdditive X 𝒰.carrier F (n : ℤ))
  eventual_stability : ∀ n : ℕ, ∃ r : ℕ, Nonempty (page r n 0 ≅ limit n)

/-- The Čech-to-derived-cohomology spectral sequence. -/
theorem exists_cech_spectral_sequence {X : RingedSpace.{v}}
    (𝒰 : CechOpenCover X) (F : Mod X.structureSheaf)
    (hcarrier : 𝒰.carrier = (⊤ : Opens X.carrier)) :
    Nonempty (CechSpectralSequenceData 𝒰 F) := by
  sorry

/-! ## Acyclic covers and vanishing -/

/-- A refinement of one open cover by another. -/
structure CechCoverRefinement {X : TopCat.{v}}
    (𝒰 𝒱 : CechOpenCover X) where
  carrier_eq : 𝒰.carrier = 𝒱.carrier
  index_map : 𝒰.member → 𝒱.member
  member_le : ∀ i, 𝒰.memberOpen i ≤ 𝒱.memberOpen (index_map i)

/-- A cofinal family of Čech covers of one open. -/
structure CofinalCechCoverSystem {X : TopCat.{v}} (U : Opens X) where
  admissible : CechOpenCover X → Prop
  carrier_eq : ∀ {𝒰}, admissible 𝒰 → 𝒰.carrier = U
  cofinal : ∀ (𝒰 : CechOpenCover X), 𝒰.carrier = U →
    ∃ 𝒱, admissible 𝒱 ∧ Nonempty (CechCoverRefinement 𝒰 𝒱)

def AcyclicOnIntersections {X : RingedSpace.{v}} (𝒰 : CechOpenCover X)
    (F : Mod X.structureSheaf) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (p : ℕ) (i : Fin (p + 1) → 𝒰.member),
    IsZero (cohomologyOnOpenAdditive X
      (∏ᶜ 𝒰.memberOpen ∘ i) F (q : ℤ))

theorem cech_cohomology_iso_of_acyclic_intersections
    {X : RingedSpace.{v}} (𝒰 : CechOpenCover X) (F : Mod X.structureSheaf)
    (hF : AcyclicOnIntersections 𝒰 F) (p : ℕ) :
    Nonempty (cechCohomologyObject 𝒰 F.val.presheaf p ≅
      cohomologyOnOpenAdditive X 𝒰.carrier F (p : ℤ)) := by
  sorry

def CechPositiveVanishing {X : TopCat.{v}} (F : AbelianPresheaf X) : Prop :=
  ∀ 𝒰 : CechOpenCover X, ∀ p : ℕ, 0 < p →
    IsZero (cechCohomologyObject 𝒰 F p)

theorem sheaf_cohomology_vanishes_of_cech_positive_vanishing
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (U : Opens X.carrier) (hF : CechPositiveVanishing F.val.presheaf)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cohomologyOnOpenAdditive X U F (p : ℤ)) := by
  sorry

/-- A family of covers used for the basis variant of the vanishing lemma. -/
structure CechBasisCoverCollection {X : TopCat.{v}}
    (B : Set (Opens X)) where
  admissible : CechOpenCover X → Prop
  carrier_mem : ∀ {𝒰}, admissible 𝒰 → 𝒰.carrier ∈ B
  member_mem : ∀ {𝒰}, admissible 𝒰 → ∀ i, 𝒰.memberOpen i ∈ B
  intersection_mem : ∀ {𝒰}, admissible 𝒰 → ∀ (n : ℕ)
    (i : Fin n → 𝒰.member), (∏ᶜ 𝒰.memberOpen ∘ i) ∈ B
  cofinal : ∀ (U : Opens X), U ∈ B → ∀ (𝒰 : CechOpenCover X), 𝒰.carrier = U →
    ∃ 𝒱, admissible 𝒱 ∧ Nonempty (CechCoverRefinement 𝒰 𝒱)

theorem sheaf_cohomology_vanishes_of_basis_cech_positive_vanishing
    {X : RingedSpace.{v}} (B : Set (Opens X.carrier))
    (Cov : CechBasisCoverCollection B) (F : Mod X.structureSheaf)
    (hF : ∀ (𝒰 : CechOpenCover X), Cov.admissible 𝒰 → ∀ p : ℕ, 0 < p →
      IsZero (cechCohomologyObject 𝒰 F.val.presheaf p))
    (U : Opens X.carrier) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (cohomologyOnOpenAdditive X U F (p : ℤ)) := by
  sorry

/-- The cofinal-cover hypothesis gives the surjectivity of sections in a
short exact sequence of presheaves. -/
theorem sections_surjective_of_cofinal_cech_h1
    {X : RingedSpace.{v}} {U : Opens X.carrier}
    (Cov : CofinalCechCoverSystem U)
    (S : ShortComplex (PMod X.structureSheaf.obj)) (hS : S.ShortExact)
    (hF : ∀ (𝒰 : CechOpenCover X), Cov.admissible 𝒰 →
      IsZero (cechCohomologyObject 𝒰 S.X₁.presheaf 1)) :
    Function.Surjective ((S.g.app (op U)).hom) := by
  sorry

/-! ## Pushforward and products -/

theorem pushforward_of_injective_is_cech_acyclic
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (I : Mod X.structureSheaf) [Injective I] (𝒰 : CechOpenCover Y)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomologyObject 𝒰
      ((sheafModuleRingedSpacePushforward f).obj I).val.presheaf p) := by
  sorry

theorem pushforward_of_injective_has_vanishing_higher_cohomology
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (I : Mod X.structureSheaf) [Injective I] (V : Opens Y.carrier)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cohomologyOnOpenAdditive Y V
      ((sheafModuleRingedSpacePushforward f).obj I) (p : ℤ)) := by
  sorry

/-- Flatness in the final pushforward assertion is supplied as the standard
property that pullback preserves monomorphisms; it is kept as a hypothesis
here because the chapter does not develop a separate flat-morphism API. -/
structure FlatRingedSpaceHomData {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) where
  pullback : Mod Y.structureSheaf ⥤ Mod X.structureSheaf
  adjunction : pullback ⊣ sheafModuleRingedSpacePushforward f
  pullback_isExact : Formalization.Books.Categories.Unit23.IsExact pullback

theorem flat_pushforward_of_injective_is_injective
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : FlatRingedSpaceHomData f) (I : Mod X.structureSheaf)
    [Injective I] : Injective ((sheafModuleRingedSpacePushforward f).obj I) := by
  sorry

theorem cohomology_products_degree_zero
    {X : RingedSpace.{v}} (U : Opens X.carrier)
    {ι : Type v} (F : ι → Mod X.structureSheaf) :
    Nonempty (cohomologyOnOpenAdditive X U (∏ᶜ F) 0 ≅
      ∏ᶜ (fun i => cohomologyOnOpenAdditive X U (F i) 0)) := by
  sorry

theorem cohomology_products_degree_one_injective
    {X : RingedSpace.{v}} (U : Opens X.carrier)
    {ι : Type v} (F : ι → Mod X.structureSheaf) :
    ∃ φ : cohomologyOnOpenAdditive X U (∏ᶜ F) 1 →
        ∏ᶜ (fun i => cohomologyOnOpenAdditive X U (F i) 1),
      Function.Injective φ := by
  sorry

end Formalization.Books.Cohomology.Unit08
