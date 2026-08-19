import Formalization.Books.Modules.Unit11.FinitePresentation
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Sheaves of Modules, Chapter 12: Coherent modules

The source definition is expressed using the canonical finite-type condition
from Chapter 9 and the canonical free-sheaf map associated to sections from
Chapter 4.  Finite presentation and quasi-coherence are the interfaces from
Chapter 11 and Chapter 10.  The weak-Serre and exact-inclusion statements use
the established categorical interfaces from Homological Algebra, Chapter 10.
-/

namespace Formalization.Books.Modules.Unit12

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit11
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Homology.Unit10

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## Definition `definition-coherent` -/

/- The source quantifies over finite collections of sections on every open.
   `I` is an arbitrary finite index type, and `globalGenerationMap` is the
   canonical map from the free sheaf on those sections. -/
def RelationsFiniteOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∀ (I : Type v), Finite I →
    ∀ (s : I → ((openModuleRestrictionFunctor X U).obj F).sections),
      finiteType (kernel (globalGenerationMap s))

/-- The source's coherence condition for a sheaf of modules. -/
def IsCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  finiteType F ∧ ∀ U : Opens X.carrier, RelationsFiniteOn F U

/-- The object property defining the coherent-module category. -/
def coherentModuleProperty (X : RingedSpace.{v}) :
    ObjectProperty (Mod X.structureSheaf) :=
  fun F => IsCoherent F

/-- The category denoted by `Coh(𝒪_X)` in the source. -/
abbrev Coh (X : RingedSpace.{v}) :=
  (coherentModuleProperty X).FullSubcategory

/-! ## Lemma `lemma-coherent-finite-presentation` -/

/-- A coherent module is finitely presented and therefore quasi-coherent. -/
theorem coherent_isFinitePresentation_and_isQuasiCoherent
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsCoherent F) :
    IsFinitePresentation F ∧ IsQuasiCoherent F := by
  sorry

/-! ## Example `example-coherent-not-Noetherian` -/

/- The source's countably generated polynomial ring is represented by the
   multivariable polynomial ring on `ℕ`; the indexing convention starts at
   zero and is equivalent to the source's `x₁, x₂, ...`. -/
abbrev infiniteComplexPolynomialRing := MvPolynomial ℕ ℂ

/-- The polynomial ring `ℂ[x₁, x₂, x₃, ...]` is coherent but not Noetherian. -/
theorem infiniteComplexPolynomialRing_isCoherent_not_noetherian :
    (∀ I : Ideal infiniteComplexPolynomialRing, I.FG →
      Module.FinitePresentation infiniteComplexPolynomialRing (I : Type)) ∧
      ¬ IsNoetherianRing infiniteComplexPolynomialRing := by
  sorry

/-! ## Lemma `lemma-coherent-abelian` -/

/-- A finite-type subsheaf of a coherent sheaf is coherent. -/
theorem finiteType_subsheaf_isCoherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (ι : G ⟶ F) [Mono ι] (hG : finiteType G) (hF : IsCoherent F) :
    IsCoherent G := by
  sorry

/-- The kernel of a map from a finite-type sheaf to a coherent sheaf is
finite type. -/
theorem kernel_finiteType_of_finiteType_to_coherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (hF : finiteType F) (hG : IsCoherent G) :
    finiteType (kernel φ) := by
  sorry

/-- Kernels and cokernels of maps between coherent modules are coherent. -/
theorem kernel_and_cokernel_isCoherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : F ⟶ G) (hF : IsCoherent F) (hG : IsCoherent G) :
    IsCoherent (kernel φ) ∧ IsCoherent (cokernel φ) := by
  sorry

/-- In a short exact sequence, any two coherent terms imply coherence of the
third term. -/
theorem coherent_of_shortExact_two_of_three
    {X : RingedSpace.{v}}
    {F₁ F₂ F₃ : Mod X.structureSheaf}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (hfg : f ≫ g = 0)
    (hS : (sheafModuleShortComplex X.structureSheaf f g hfg).ShortExact) :
    (IsCoherent F₁ ∧ IsCoherent F₂ → IsCoherent F₃) ∧
      (IsCoherent F₁ ∧ IsCoherent F₃ → IsCoherent F₂) ∧
        (IsCoherent F₂ ∧ IsCoherent F₃ → IsCoherent F₁) := by
  sorry

/- The source's final categorical assertion is represented by the canonical
   weak-Serre class and exact full-subcategory inclusion interfaces. -/
noncomputable instance coherentModuleProperty_isWeakSerreClass
    (X : RingedSpace.{v}) :
    (coherentModuleProperty X).IsWeakSerreClass := by
  sorry

/-- The coherent-module category is abelian and its inclusion is exact. -/
theorem coherentCategory_is_abelian_and_inclusion_exact
    (X : RingedSpace.{v}) :
    Nonempty (Abelian (Coh X)) ∧
      exactFunctor (Coh X) (Mod X.structureSheaf)
        (coherentModuleProperty X).ι := by
  sorry

/- The abelian structure is made available as the categorical instance used
   by the source's phrase “the category of coherent modules is abelian”. -/
noncomputable instance coherentCategory_abelian (X : RingedSpace.{v}) :
    Abelian (Coh X) :=
  (coherentCategory_is_abelian_and_inclusion_exact X).1.some

/-! ## Lemma `lemma-coherent-structure-sheaf` -/

/-- If the structure sheaf is coherent as a module over itself, coherence is
equivalent to finite presentation. -/
theorem isCoherent_iff_isFinitePresentation_of_coherent_structureSheaf
    {X : RingedSpace.{v}}
    (hO : IsCoherent (SheafOfModules.unit X.structureSheaf))
    (F : Mod X.structureSheaf) :
    IsCoherent F ↔ IsFinitePresentation F := by
  sorry

/-! ## Lemma `lemma-finite-type-to-coherent-injective-on-stalk` -/

/-- A map from a finite-type sheaf to a coherent sheaf which is injective on a
stalk is injective on some neighbourhood of that point. -/
theorem finiteType_to_coherent_injective_on_stalk
    {X : RingedSpace.{v}} {G F : Mod X.structureSheaf}
    (φ : G ⟶ F) (x : X) (hG : finiteType G) (hF : IsCoherent F)
    (hφx : Function.Injective
      ((sheafModuleStalkFunctor X.structureSheaf x).map φ).hom) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Mono ((openModuleRestrictionFunctor X U).map φ) := by
  sorry

end

end Formalization.Books.Modules.Unit12
