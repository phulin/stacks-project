import Formalization.Books.SpacesCohomology.Unit01.HigherDirectImageVanishing

/-!
# Cohomology with support in a closed subspace
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

def sectionsWithSupport (X : AlgebraicSpace.{u}) (Z : Set X) (F : SheafObj X) : Type u :=
  {s : Sections X F // sectionSupport s ⊆ Z}

structure AdditiveType where
  carrier : Type u
  group : AddCommGroup carrier

instance additiveTypeGroup (A : AdditiveType) : AddCommGroup A.carrier := A.group

structure SupportTheory (X : AlgebraicSpace.{u}) (Z : ClosedSubspace X) where
  derived : DerivedObj X → Type u
  supportSheaf : SheafObj X → SheafObj Z.carrier
  higherSupportSheaf : ℕ → SheafObj X → SheafObj Z.carrier
  supportCohomology : SheafObj X → ℕ → AdditiveType
  supportCohomologyDerived : DerivedObj X → ℕ → AdditiveType
  supportFunctor_left_exact : Prop

def supportCohomologyGroup {X : AlgebraicSpace.{u}} {Z : ClosedSubspace X}
    (T : SupportTheory X Z) (F : SheafObj X) (p : ℕ) : Type u :=
  (T.supportCohomology F p).carrier

instance supportCohomologyGroupInstance {X : AlgebraicSpace.{u}} {Z : ClosedSubspace X}
    (T : SupportTheory X Z) (F : SheafObj X) (p : ℕ) :
    AddCommGroup (supportCohomologyGroup T F p) :=
  (T.supportCohomology F p).group

def supportCohomologyDerivedGroup {X : AlgebraicSpace.{u}} {Z : ClosedSubspace X}
    (T : SupportTheory X Z) (K : DerivedObj X) (p : ℕ) : Type u :=
  (T.supportCohomologyDerived K p).carrier

structure SupportTriangleStatement {X : AlgebraicSpace.{u}}
    (Z U : ClosedSubspace X) (T : SupportTheory X Z) where
  triangle : Prop
  long_exact : Prop

structure SectionsWithSupportLeftExactStatement (X : AlgebraicSpace.{u})
    (Z : ClosedSubspace X) where
  sections : SheafObj X → Type u
  identified : ∀ F, sections F =
    sectionsWithSupport X (Set.range Z.inclusion) F
  left_exact : Prop

theorem sections_with_support_left_exact
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (Z : ClosedSubspace X) :
    Nonempty (SectionsWithSupportLeftExactStatement X Z) := by
  sorry

theorem support_distinguished_triangle
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (Z : ClosedSubspace X) (U : OpenSubspace X) (hU_complement : Prop)
    (T : SupportTheory X Z) (K : DerivedObj X) :
    Nonempty (SupportTriangleStatement Z
      { carrier := U.carrier, inclusion := U.inclusion, closed := U.is_open } T) := by
  sorry

structure InjectiveSheaf (X : AlgebraicSpace.{u}) (I : SheafObj X) where
  injective_property : Prop

theorem sections_with_support_preserves_injectives
    (S X Z : AlgebraicSpace.{u}) (hS : IsScheme S)
    (i : SpaceHom Z X) (hi : IsClosedImmersion i)
    (I : SheafObj X) (hI : InjectiveSheaf X I)
    (T : SupportTheory X ⟨Z, i, IsClosedImmersion i⟩) :
    Nonempty (InjectiveSheaf Z (T.supportSheaf I)) := by
  sorry

theorem cohomology_with_support_grothendieck_spectral_sequence
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (Z : ClosedSubspace X) (T : SupportTheory X Z) (F : SheafObj X) :
    Nonempty (SpectralSequenceStatement
      (fun p q => supportCohomologyGroup T F q.natAbs)
      (fun n => supportCohomologyGroup T F n.natAbs)) := by
  sorry

theorem cohomology_with_support_sheaf_on_support
    (S X Z : AlgebraicSpace.{u}) (hS : IsScheme S)
    (i : SpaceHom Z X) (hi : IsClosedImmersion i)
    (G : SheafObj Z) (hG : InjectiveSheaf Z G)
    (T : SupportTheory X ⟨Z, i, IsClosedImmersion i⟩) (p : ℕ) (hp : 0 < p) :
    Subsingleton (supportCohomologyGroup T (pushforwardSheaf i G) p) := by
  sorry

theorem etale_localization_sheaf_with_support
    (S X Y Z : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsEtale f)
    (i : SpaceHom Z Y) (hi : IsClosedImmersion i)
    (pullback_isomorphism : Prop) (F : SheafObj X)
    (TX : SupportTheory (baseChange i f)
      { carrier := baseChange i f,
        inclusion := 𝟙 (baseChange i f),
        closed := IsClosedImmersion (𝟙 (baseChange i f)) })
    (TY : SupportTheory Y ⟨Z, i, IsClosedImmersion i⟩) (q : ℕ) :
    Nonempty (AddEquiv
      (supportCohomologyGroup TY (pushforwardSheaf f F) q)
      (supportCohomologyGroup TX
        (pullbackSheaf (baseChangeTarget i f) F) q)) := by
  sorry

structure SupportedDerivedEquivalence (X Z : AlgebraicSpace.{u}) where
  forward : Type u → Type u
  backward : Type u → Type u
  fully_faithful : Prop
  essentially_surjective : Prop
  supported_objects : Prop

theorem closed_immersion_derived_support_equivalence
    (S X Z : AlgebraicSpace.{u}) (hS : IsScheme S)
    (i : SpaceHom Z X) (hi : IsClosedImmersion i) :
    Nonempty (SupportedDerivedEquivalence X Z) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
