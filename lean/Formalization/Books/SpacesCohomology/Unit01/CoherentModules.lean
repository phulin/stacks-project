import Formalization.Books.SpacesCohomology.Unit01.BaseChange

/-!
# Coherent modules on locally Noetherian algebraic spaces

The source section packages the usual local characterizations of coherent
modules and the closure properties used later.  The chapter-wide model in
`Core` exposes the sheaf operations and the geometric predicates needed to
state these results without importing a later chapter.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

def IsCoherentModule (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  IsQuasiCoherent F ∧ IsCoherent F

def IsFiniteTypeModule (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  IsQuasiCoherent F ∧ IsFiniteTypeSheaf F

def IsEtaleLocallyCoherent (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  ∀ (U : AlgebraicSpace.{u}) (φ : SpaceHom U X),
    IsScheme U → IsEtale φ → IsCoherentModule U (pullbackSheaf φ F)

def IsCoherentOnOneEtaleCover (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  ∃ (U : AlgebraicSpace.{u}) (φ : SpaceHom U X),
    IsScheme U ∧ IsEtale φ ∧ IsSurjective φ ∧
      IsCoherentModule U (pullbackSheaf φ F)

def CoherentCharacterization (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) : Prop :=
  IsCoherentModule X F ↔
    (IsFiniteTypeModule X F ∧ IsFinitePresentation F ∧
      IsEtaleLocallyCoherent X F ∧ IsCoherentOnOneEtaleCover X F)

theorem coherent_module_characterization
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (hX : IsLocallyNoetherian X) :
    CoherentCharacterization X F := by
  sorry

structure CoherentStandardObjects (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  structure_sheaf : IsCoherentModule X (structureSheaf X)
  invertible : ∀ (F : SheafObj X), IsInvertible F → IsCoherentModule X F
  finite_locally_free : ∀ (F : SheafObj X), IsFiniteLocallyFree F →
    IsCoherentModule X F

theorem coherent_standard_objects
    (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (hX : IsLocallyNoetherian X) :
    CoherentStandardObjects X := by
  sorry

structure CoherentAbelianStatement (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  kernel : ∀ (F G : SheafObj X), SheafHom F G → SheafObj X
  cokernel : ∀ (F G : SheafObj X), SheafHom F G → SheafObj X
  kernel_is_coherent : ∀ (F G : SheafObj X) (φ : SheafHom F G),
    IsCoherentModule X F → IsCoherentModule X G →
      IsCoherentModule X (kernel F G φ)
  cokernel_is_coherent : ∀ (F G : SheafObj X) (φ : SheafHom F G),
    IsCoherentModule X F → IsCoherentModule X G →
      IsCoherentModule X (cokernel F G φ)
  extension_is_coherent : ∀ (E : ShortExactSheaves X),
    IsCoherentModule X E.F₁ → IsCoherentModule X E.F₃ →
      IsCoherentModule X E.F₂

theorem coherent_modules_abelian
    (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (hX : IsLocallyNoetherian X) :
    Nonempty (CoherentAbelianStatement X) := by
  sorry

structure CoherentSubmoduleWitness (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X) where
  inclusion : SheafHom G F
  quasi_coherent : IsQuasiCoherent G
  is_submodule : Prop

structure CoherentQuotientWitness (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X) where
  projection : SheafHom F G
  quasi_coherent : IsQuasiCoherent G
  is_quotient : Prop

theorem coherent_submodule
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X)
    (H : CoherentSubmoduleWitness X F G)
    (hX : IsLocallyNoetherian X) (hF : IsCoherentModule X F) :
    IsCoherentModule X G := by
  sorry

theorem coherent_quotient
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X)
    (H : CoherentQuotientWitness X F G)
    (hX : IsLocallyNoetherian X) (hF : IsCoherentModule X F) :
    IsCoherentModule X G := by
  sorry

theorem coherent_tensor_internal_hom
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X)
    (hX : IsLocallyNoetherian X) (hF : IsCoherentModule X F)
    (hG : IsCoherentModule X G) :
    IsCoherentModule X (tensorSheaf X F G) ∧
      IsCoherentModule X (internalHomSheaf X F G) := by
  sorry

structure StalkMapData (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X) (x : X) where
  map : Stalk X F x →+ Stalk X G x

def OpenContainsPoint (U : OpenSubspace X) (x : X) : Prop :=
  ∃ u : U.carrier, U.inclusion u = x

structure LocalZeroWitness (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) (x : X) where
  open_subspace : OpenSubspace X
  contains : OpenContainsPoint open_subspace x
  vanishes : restrictSheaf open_subspace.inclusion F = zeroSheaf open_subspace.carrier

structure LocalMapWitness (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X)
    (φ : SheafHom G F) (x : X) where
  open_subspace : OpenSubspace X
  contains : OpenContainsPoint open_subspace x
  property : Prop

structure LocalStalkCriteria (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F G : SheafObj X)
    (φ : SheafHom G F) (x : X) where
  zero : Subsingleton (Stalk X F x) → Nonempty (LocalZeroWitness X F x)
  injective : ∀ (D : StalkMapData X G F x),
    Function.Injective D.map → Nonempty (LocalMapWitness X F G φ x)
  surjective : ∀ (D : StalkMapData X G F x),
    Function.Surjective D.map → Nonempty (LocalMapWitness X F G φ x)
  isomorphism : ∀ (D : StalkMapData X G F x),
    Function.Bijective D.map → Nonempty (LocalMapWitness X F G φ x)

theorem coherent_local_stalk_criteria
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X) (φ : SheafHom G F) (x : X)
    (hX : IsLocallyNoetherian X) (hF : IsCoherentModule X F)
    (hG : IsCoherentModule X G) :
    LocalStalkCriteria X F G φ x := by
  sorry

structure CoherentSupportStatement (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) where
  coherent_F : IsCoherentModule X F
  support : ClosedSubspace X
  support_identification : support = schemeTheoreticSupport F
  descended : SheafObj support.carrier
  pushforward_identification :
    Nonempty (SheafIso X (pushforwardSheaf support.inclusion descended) F)
  descended_coherent : IsCoherentModule support.carrier descended

theorem coherent_scheme_theoretic_support
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (hX : IsLocallyNoetherian X) (hF : IsCoherentModule X F) :
    Nonempty (CoherentSupportStatement X F) := by
  sorry

structure CoherentClosedImmersionEquivalence (X Z : AlgebraicSpace.{u})
    (i : SpaceHom Z X) [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  closed_immersion : IsClosedImmersion i
  ideal : IdealSheaf X
  ideal_property : Prop
  pushforward : SheafObj Z → SheafObj X
  pullback : SheafObj X → SheafObj Z
  fully_faithful : Prop
  essential_surjectivity : Prop
  annihilated_objects : Prop

theorem coherent_closed_immersion_equivalence
    (X Z : AlgebraicSpace.{u}) (i : SpaceHom Z X)
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (_hX : IsLocallyNoetherian X) (_hZ : IsLocallyNoetherian Z)
    (hi : IsClosedImmersion i) :
    Nonempty (CoherentClosedImmersionEquivalence X Z i) := by
  sorry

theorem finite_pushforward_coherent
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X)
    (hY : IsLocallyNoetherian Y) (hf : IsFinite f)
    (hF : IsCoherentModule X F) :
    (∀ p : ℕ, 0 < p →
      higherDirectImage p f F = zeroSheaf Y) ∧
      IsCoherentModule Y (pushforwardSheaf f F) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
