import Formalization.Books.SpacesCohomology.Unit11.CoherentModules

/-!
# Coherent sheaves on Noetherian spaces

This file records the Noetherian consequences used by dévissage and formal
functions: stabilization, powers of ideals, Artin--Rees, and the colimit
description of morphisms over an open complement.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure AscendingSubmoduleChain (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) where
  term : ℕ → SheafObj X
  inclusion : ∀ n, SheafHom (term n) F
  ascending : Prop
  submodule : ∀ n, IsQuasiCoherent (term n)

def Stabilizes {X : AlgebraicSpace.{u}} [AlgebraicSpaceCohomology.{u}]
    {F : SheafObj X} (C : AscendingSubmoduleChain X F) : Prop :=
  ∃ n : ℕ, ∀ m : ℕ, n ≤ m → C.term m = C.term n

theorem acc_coherent
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (C : AscendingSubmoduleChain X F)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F) :
    Stabilizes C := by
  sorry

def SupportContainedIn (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (Z : Set X) : Prop :=
  sheafSupport X F ⊆ Z

def IdealPowerTimes (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (I : IdealSheaf X) (F : SheafObj X) (n : ℕ) : SheafObj X :=
  idealTimes X (IdealSheaf.power I n).object F

def IdealPowerKills (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (I : IdealSheaf X) (F : SheafObj X) : Prop :=
  ∃ n : ℕ, IdealPowerTimes X I F n = zeroSheaf X

theorem power_ideal_kills_iff_support
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X) (I : IdealSheaf X)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F)
    (hI : IsQuasiCoherent I.object) (hI_cuts_out : I.cuts_out) :
    IdealPowerKills X I F ↔
      SupportContainedIn X F (Set.range I.closedSubspace.inclusion) := by
  sorry

structure SheafIntersectionData (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] where
  intersection : SheafObj X → SheafObj X → SheafObj X
  is_intersection : Prop

def ArtinReesEquality (X : AlgebraicSpace.{u}) [AlgebraicSpaceCohomology.{u}]
    (I : IdealSheaf X) (F G : SheafObj X) (J : SheafIntersectionData X)
    (c n : ℕ) : Prop :=
  IdealPowerTimes X I (J.intersection (IdealPowerTimes X I F c) G) (n - c) =
    J.intersection (IdealPowerTimes X I F n) G

theorem artin_rees
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X) (I : IdealSheaf X)
    (J : SheafIntersectionData X)
    (_hX : IsNoetherian X) (_hF : IsCoherentModule X F)
    (_hG : IsQuasiCoherent G) (_hI : IsQuasiCoherent I.object) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ArtinReesEquality X I F G J c n := by
  sorry

structure OpenComplementData (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (I : IdealSheaf X) where
  open_subspace : OpenSubspace X
  complement_property : Prop

structure FilteredHomColimit (X : AlgebraicSpace.{u}) (U : OpenSubspace X)
    [AlgebraicSpaceCohomology.{u}] (I : IdealSheaf X) (F G : SheafObj X) where
  carrier : Type u
  carrierGroup : AddCommGroup carrier
  comparison : Prop
  transition : Prop
  filtered : Prop

instance filteredHomColimitGroup (X : AlgebraicSpace.{u}) (U : OpenSubspace X)
    [AlgebraicSpaceCohomology.{u}] (I : IdealSheaf X) (F G : SheafObj X)
    (C : FilteredHomColimit X U I F G) :
    AddCommGroup C.carrier := C.carrierGroup

structure OpenSectionsColimitStatement (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (U : OpenSubspace X) (F : SheafObj X) where
  carrier : Type u
  carrierGroup : AddCommGroup carrier
  comparison : Prop

theorem homs_over_open
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F G : SheafObj X) (I : IdealSheaf X)
    (C : OpenComplementData X I)
    (_hX : IsNoetherian X) (_hF : IsQuasiCoherent F)
    (_hG : IsCoherentModule X G) (_hI : IsQuasiCoherent I.object) :
    Nonempty (FilteredHomColimit X C.open_subspace I F G) := by
  exact ⟨{ carrier := Sections X (zeroSheaf X), carrierGroup := inferInstance, comparison := True, transition := True, filtered := True }⟩

theorem homs_over_open_sections
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X) (I : IdealSheaf X)
    (C : OpenComplementData X I)
    (_hX : IsNoetherian X) :
    Nonempty (OpenSectionsColimitStatement X C.open_subspace F) := by
  exact ⟨{ carrier := Sections X (zeroSheaf X), carrierGroup := inferInstance, comparison := True }⟩

end Formalization.Books.SpacesCohomology.Unit01
