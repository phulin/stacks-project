import Formalization.Books.Duality.Unit01.CompactSupportCoherent

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

theorem lemma_duality_compact_support {U X : Scheme.{u}}
    (j : U ⟶ X) (a : RightAdjointData j) (K : DerivedObject U)
    (hcoherent : IsCoherent K) :
    Nonempty (CompactSupportDualityData j a) := by
  exact proposition_duality_compactly_supported j a K hcoherent

theorem lemma_duality_compact_support_restrict_open {U X V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) (K : DerivedObject V)
    (hopen : IsOpenImmersionMorphism k) :
    Isomorphic ((RPushforward j).obj ((RPushforward k).obj K))
      ((RPushforward (k ≫ j)).obj K) := by
  sorry

theorem lemma_h0_compactly_supported {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) (hcoherent : IsCoherent K) :
    Nonempty (CompactSupportH0Data j K) := by
  sorry

end

end Formalization.Books.Duality.Unit01
