import Formalization.Books.Duality.Unit01.CompactSupportPreliminaries

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def LowerShriek {U X : Scheme.{u}} (j : U ⟶ X) :
    DerivedObject U ⥤ DerivedObject X :=
  RPushforward j

def CompactlySupportedCohomology {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) : DerivedObject X :=
  (LowerShriek j).obj K

structure CompactSupportH0Data {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) where
  compactSections : Type u
  globalSections : Type u
  inclusion : compactSections → globalSections
  injective : Function.Injective inclusion
  vanishesNearBoundary : globalSections → Prop
  imageCharacterization : ∀ s : compactSections,
    vanishesNearBoundary (inclusion s)
  surjectiveOnVanishing : ∀ t : globalSections,
    vanishesNearBoundary t → ∃ s : compactSections, inclusion s = t

structure LowerShriekData {U X : Scheme.{u}} (j : U ⟶ X) where
  functor : DerivedObject U ⥤ DerivedObject X
  comparison : Nonempty (functor ≅ LowerShriek j)

theorem lemma_lower_shriek_well_defined {U X : Scheme.{u}} (j : U ⟶ X)
    (hopen : IsOpenImmersionMorphism j) : Nonempty (LowerShriekData j) := by
  exact ⟨⟨LowerShriek j, ⟨Iso.refl _⟩⟩⟩

structure CompactSupportDualityData {U X : Scheme.{u}} (j : U ⟶ X)
    (a : RightAdjointData j) where
  K : DerivedObject U
  dual : DerivedObject U
  pairing : Isomorphic dual (a.rightAdjoint.obj (StructureSheaf X))
  cohomology : Type u
  dualCohomology : Type u
  duality : Nonempty (cohomology ≃ dualCohomology)

theorem proposition_duality_compactly_supported {U X : Scheme.{u}}
    (j : U ⟶ X) (a : RightAdjointData j) (K : DerivedObject U)
    (hcoherent : IsCoherent K) : Nonempty (CompactSupportDualityData j a) := by
  sorry

theorem lemma_compactly_supported_triangle {U X : Scheme.{u}}
    (j : U ⟶ X) (K L M : DerivedObject U)
    (t : DerivedTriangleData K L M) :
    Nonempty (ExtensionByZeroTriangleData j t) := by
  sorry

def remark_compose_inverse_systems {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) : Prop :=
  IsOpenImmersionMorphism j ∧ IsOpenImmersionMorphism k

def remark_composition_lower_shriek {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) : Prop :=
  IsOpenImmersionMorphism (k ≫ j)

theorem lemma_composition_lower_shriek {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) :
    Nonempty (LowerShriekData (k ≫ j)) := by
  sorry

def remark_covariance_open_lower_shriek {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) : Prop :=
  IsOpenImmersionMorphism j

def remark_covariance_etale_lower_shriek {U X : Scheme.{u}} (j : U ⟶ X) : Prop :=
  IsOpenImmersionMorphism j

def remark_covariance_lower_shriek {U X : Scheme.{u}} (j : U ⟶ X) : Prop :=
  IsOpenImmersionMorphism j

end

end Formalization.Books.Duality.Unit01
