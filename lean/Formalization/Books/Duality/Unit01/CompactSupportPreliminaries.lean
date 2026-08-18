import Formalization.Books.Duality.Unit01.ExtensionByZero

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure InverseSystem (X : Scheme.{u}) where
  term : ℕ → DerivedObject X
  transition : ∀ n, term (n + 1) ⟶ term n

structure CompactSupportPreData {U X : Scheme.{u}} (j : U ⟶ X) where
  system : InverseSystem X
  openImmersion : IsOpenImmersionMorphism j
  supportedTerms : Prop

theorem lemma_well_defined_pre {U X : Scheme.{u}} (j : U ⟶ X)
    (d : CompactSupportPreData j) : Nonempty (CompactSupportPreData j) := by
  exact ⟨d⟩

theorem lemma_well_defined {U X : Scheme.{u}} (j : U ⟶ X)
    (hopen : IsOpenImmersionMorphism j) :
    ∃ d : CompactSupportPreData j, IsOpenImmersionMorphism j := by
  sorry

def remark_covariance_open_j_lower_shriek {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) : Prop :=
  IsOpenImmersionMorphism j ∧ IsOpenImmersionMorphism k

end

end Formalization.Books.Duality.Unit01
