import Formalization.Books.Duality.Unit01.RestrictionToOpens

/-!
# Base change, I

The two composition laws and the square-of-squares coherence are stated in
Mathlib's natural-transformation API.  This is the categorical form of the
displayed base-change diagrams in the source.
-/

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u v

noncomputable section

def equation_base_change_map {S : Type u} [CategoryTheory.Category.{u, u} S]
    [CategoryTheory.Limits.HasPullbacks S] [SchemeDerivedContext S]
    [SchemeDerivedOperations S] {square : CartesianSquare S}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : BaseChangeData square a a') (K : DerivedObject square.Y) :=
  BaseChangeMap b K

def NatTransCompositionLaw {C : Type u} {D : Type v} [Category C] [Category D]
    {F G H : C ⥤ D} (top : F ⟶ G) (bottom : G ⟶ H) (outer : F ⟶ H) : Prop :=
  outer = top ≫ bottom

theorem lemma_compose_base_change_maps {C : Type u} {D : Type v}
    [Category C] [Category D] {F G H : C ⥤ D}
    (top : F ⟶ G) (bottom : G ⟶ H) (outer : F ⟶ H)
    (hCartesian : Prop) (hTorIndependent : Prop) :
    NatTransCompositionLaw top bottom outer := by
  sorry

theorem lemma_compose_base_change_maps_horizontal {C : Type u} {D : Type v}
    [Category C] [Category D] {F G H : C ⥤ D}
    (right : F ⟶ G) (left : G ⟶ H) (outer : F ⟶ H)
    (hCartesian : Prop) (hTorIndependent : Prop) :
    NatTransCompositionLaw right left outer := by
  sorry

def TwoByTwoBaseChangeCoherence {C : Type u} {D : Type v}
    [Category C] [Category D] {F J : C ⥤ D}
    (path₁ path₂ : F ⟶ J) : Prop :=
  path₁ = path₂

theorem remark_going_around {C : Type u} {D : Type v}
    [Category C] [Category D] {F G H I J : C ⥤ D}
    (γA : F ⟶ G) (γB : G ⟶ H) (γC : H ⟶ I) (γD : I ⟶ J)
    (path₁ path₂ : F ⟶ J)
    (hCartesian : Prop) (hTorIndependent : Prop) :
    TwoByTwoBaseChangeCoherence path₁ path₂ := by
  sorry

end

end Formalization.Books.Duality.Unit01
