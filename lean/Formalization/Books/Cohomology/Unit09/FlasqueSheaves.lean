import Formalization.Books.Cohomology.Unit08
import Formalization.Books.Sheaves.Unit04.AbelianPresheaves

/-!
# Cohomology of Sheaves, Chapter 9: flasque sheaves

This file records the definition of flasqueness and the vanishing statements
for flasque sheaves from the source section.  Restriction maps, Čech
cohomology, cohomology on an open, and higher direct images use the canonical
APIs established in earlier chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit09

/-! ## Flasqueness -/

/- The source first defines flasqueness for set-valued presheaves. -/

/-- A set-valued presheaf is flasque when every restriction map is
surjective. -/
def FlasquePresheaf (X : TopCat.{v})
    (F : TopCat.Presheaf (Type v) X) : Prop :=
  ∀ {U V : Opens X} (h : U ≤ V),
    Function.Surjective (F.map (homOfLE h).op)

/-- An additive-group-valued presheaf is flasque when every restriction map
is surjective on the underlying sets. -/
def FlasqueAbelianPresheaf (X : TopCat.{v})
    (F : AbelianPresheaf X) : Prop :=
  ∀ {U V : Opens X} (h : U ≤ V),
    Function.Surjective (F.map (homOfLE h).op).hom

/-- A sheaf of modules on a ringed space is flasque when its underlying
abelian presheaf is flasque. -/
def FlasqueModule (X : RingedSpace.{v}) (F : Mod X.structureSheaf) : Prop :=
  FlasqueAbelianPresheaf X F.val.presheaf

/-- Flasqueness for an additive sheaf, used in the final Čech vanishing
lemma. -/
def FlasqueAbelianSheaf (X : TopCat.{v})
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) : Prop :=
  FlasqueAbelianPresheaf X F.presheaf

/-- It is enough to check surjectivity from the whole space for a
set-valued presheaf. -/
theorem flasquePresheaf_iff_global_sections_surjective (X : TopCat.{v})
    (F : TopCat.Presheaf (Type v) X) :
    FlasquePresheaf X F ↔
      ∀ U : Opens X, Function.Surjective
        (F.map (homOfLE (show U ≤ (⊤ : Opens X) from le_top)).op) := by
  sorry

/-- The analogous global-sections criterion for sheaves of modules. -/
theorem flasqueModule_iff_global_sections_surjective
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    FlasqueModule X F ↔
      ∀ U : Opens X.carrier,
        Function.Surjective (moduleRestriction F.val (show U ≤ ⊤ from le_top)).hom := by
  sorry

/- Every injective sheaf of modules is flasque.  The existing injective
   restriction-surjectivity API supplies the proof route. -/
theorem injective_module_is_flasque (X : RingedSpace.{v})
    (I : Mod X.structureSheaf) [Injective I] :
    FlasqueModule X I := by
  sorry

/-! ## Acyclicity of flasque modules -/

/-- Positive cohomology of a sheaf of modules vanishes on the open `U`. -/
def SectionsAcyclicOnOpen (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) : Prop :=
  ∀ p : ℕ, 0 < p →
    IsZero (ringedSpaceModuleSectionsCohomologyObject X U F (p : ℤ))

/-- A sheaf of modules is acyclic for derived sections on every open. -/
def SectionsAcyclic (X : RingedSpace.{v}) (F : Mod X.structureSheaf) : Prop :=
  ∀ U : Opens X.carrier, SectionsAcyclicOnOpen X U F

/-- Flasque modules are acyclic for derived sections on the whole space and
on every open subspace. -/
theorem flasque_module_is_sections_acyclic (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (hF : FlasqueModule X F) :
    SectionsAcyclic X F := by
  sorry

/-! ## Čech and pushforward vanishing -/

/- The source explicitly warns that the next assertion is a sheaf statement;
   it is not asserted for arbitrary flasque presheaves. -/

/-- A flasque sheaf of modules has no positive Čech cohomology for any open
cover. -/
theorem flasque_module_cech_cohomology_isZero
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf)
    (𝒰 : CechOpenCover X) (hF : FlasqueModule X F)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomologyObject 𝒰 F.val.presheaf p) := by
  sorry

/-- A flasque sheaf has no positive higher direct images. -/
theorem flasque_module_higher_direct_image_isZero
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (hF : FlasqueModule X F)
    (p : ℕ) (hp : 0 < p) :
    IsZero (ringedSpaceModuleHigherDirectImageObject f F (p : ℤ)) := by
  sorry

/-! ## The arbitrary-union Čech vanishing criterion -/

/-- A finite nonempty intersection of members of a Čech cover. -/
def CechIntersection {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (p : ℕ) (i : Fin (p + 1) → 𝒰.member) : Opens X :=
  ∏ᶜ 𝒰.memberOpen ∘ i

/-- The predicate that an open is one of the finite intersections occurring in
the Čech complex. -/
def IsCechIntersection {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (V : Opens X) : Prop :=
  ∃ p : ℕ, ∃ i : Fin (p + 1) → 𝒰.member, CechIntersection 𝒰 p i = V

/-- The union of a family of opens, written in a form convenient for the
arbitrary-union hypothesis in the source. -/
def CechIntersectionUnion {X : TopCat.{v}} (S : Set (Opens X)) : Opens X :=
  ⨆ V : S, (V : Opens X)

/-- Every Čech intersection lies in the open covered by the Čech cover. -/
theorem cechIntersection_le_carrier {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (p : ℕ)
    (i : Fin (p + 1) → 𝒰.member) :
    CechIntersection 𝒰 p i ≤ 𝒰.carrier := by
  exact le_trans
    (leOfHom (Pi.π (fun a : Fin (p + 1) => 𝒰.memberOpen (i a)) 0))
    (𝒰.memberOpen_le_carrier (i 0))

/-- The union of arbitrary Čech intersections is still contained in the
covered open. -/
theorem cechIntersectionUnion_le_carrier {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (S : Set (Opens X))
    (hS : ∀ V ∈ S, IsCechIntersection 𝒰 V) :
    CechIntersectionUnion S ≤ 𝒰.carrier := by
  refine iSup_le ?_
  intro V
  obtain ⟨p, i, hi⟩ := hS V.1 V.2
  rw [← hi]
  exact cechIntersection_le_carrier 𝒰 p i

/-- Surjectivity on every arbitrary union of finite Čech intersections, as in
the hypothesis of the final source lemma. -/
def RaviSectionSurjectivity {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) : Prop :=
  ∀ (S : Set (Opens X)) (hS : ∀ V ∈ S, IsCechIntersection 𝒰 V),
    let hU := cechIntersectionUnion_le_carrier 𝒰 S hS
    Function.Surjective (F.map (homOfLE hU).op).hom

/-- The vanishing lemma for an abelian sheaf under the source's
arbitrary-union restriction hypothesis. -/
theorem cech_cohomology_isZero_of_ravi_section_surjectivity
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (𝒰 : CechOpenCover X)
    (hF : RaviSectionSurjectivity 𝒰 F.presheaf)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomologyObject 𝒰 F.presheaf p) := by
  sorry

end Formalization.Books.Cohomology.Unit09
