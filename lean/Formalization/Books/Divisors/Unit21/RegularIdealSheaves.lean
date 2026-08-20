import Formalization.Books.Algebra.Unit68.RegularSequences
import Formalization.Books.MoreAlgebra.Unit30.KoszulRegularSequences
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Divisors, Chapter 21: Regular ideal sheaves

The algebraic sequence predicates below are the canonical predicates from the
Algebra and More on Algebra formalizations.  The scheme-facing ideal-sheaf
interfaces use Mathlib's `Scheme.IdealSheafData`, which is the available
canonical presentation of a quasi-coherent ideal sheaf by its affine pieces.
This gives declarations with the same local content as the source's ringed
space definitions while keeping the affine generators and their rings
explicit and usable.
-/

namespace Formalization.Books.Divisors.Unit21

open AlgebraicGeometry
open Formalization.Books.Algebra.Unit69
open Formalization.Books.MoreAlgebra.Unit30

universe u v

/-! ## The four sequence predicates -/

/-
These are intentionally abbreviations: the project already formalizes the
four algebraic notions used by the source, including the source convention
that a regular sequence has nonzero final quotient.
-/

abbrev IsRegularSequence (R : Type u) [CommRing R] (f : List R) : Prop :=
  RingTheory.Sequence.IsRegular R f

abbrev IsKoszulRegularSequence (R : Type u) [CommRing R] (f : List R) : Prop :=
  Formalization.Books.MoreAlgebra.Unit30.IsKoszulRegular R f

abbrev IsHOneRegularSequence (R : Type u) [CommRing R] (f : List R) : Prop :=
  Formalization.Books.MoreAlgebra.Unit30.IsHOneRegular R f

abbrev IsQuasiRegularSequence (R : Type u) [CommRing R] (f : List R) : Prop :=
  Formalization.Books.Algebra.Unit69.IsQuasiRegular R f

/-! The source's comparison chain for sequences. -/

theorem isKoszulRegularSequence_of_isRegularSequence
    (R : Type u) [CommRing R] (f : List R)
    (hf : IsRegularSequence R f) : IsKoszulRegularSequence R f := by
  exact Formalization.Books.MoreAlgebra.Unit30.isKoszulRegular_of_isRegular R f hf

theorem isHOneRegularSequence_of_isKoszulRegularSequence
    (R : Type u) [CommRing R] (f : List R)
    (hf : IsKoszulRegularSequence R f) : IsHOneRegularSequence R f := by
  exact Formalization.Books.MoreAlgebra.Unit30.isHOneRegular_of_isKoszulRegular R f hf

theorem isQuasiRegularSequence_of_isHOneRegularSequence
    (R : Type u) [CommRing R] (f : List R)
    (hf : IsHOneRegularSequence R f) : IsQuasiRegularSequence R f := by
  exact Formalization.Books.MoreAlgebra.Unit30.isMQuasiRegular_of_isMHOneRegular
    R R f hf

theorem regularSequence_implication_chain
    (R : Type u) [CommRing R] (f : List R) :
    IsRegularSequence R f → IsKoszulRegularSequence R f ∧
      (IsKoszulRegularSequence R f → IsHOneRegularSequence R f) ∧
      (IsHOneRegularSequence R f → IsQuasiRegularSequence R f) := by
  intro hf
  exact ⟨isKoszulRegularSequence_of_isRegularSequence R f hf,
    isHOneRegularSequence_of_isKoszulRegularSequence R f,
    isQuasiRegularSequence_of_isHOneRegularSequence R f⟩

/-! ## Ringed-space sequence and ideal-sheaf interfaces -/

/-
Mathlib's `SheafedSpace CommRingCat` is the canonical ringed-space object:
it is a topological space with a sheaf of commutative rings, and its stalks
are the local rings used by the source.  We use its section and germ maps
directly rather than introducing a second sheaf abstraction.
-/

abbrev RingedSpace := AlgebraicGeometry.SheafedSpace CommRingCat

abbrev ringedSpaceSection (X : RingedSpace) (U : TopologicalSpace.Opens X) :=
  X.presheaf.obj (Opposite.op U)

noncomputable def ringedSpaceStalkSequenceOnOpen
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (x : X) (hx : x ∈ U) (f : List (ringedSpaceSection X U)) :
    List (X.presheaf.stalk x) :=
  f.map (fun a => (X.presheaf.germ U x hx).hom a)

/-
The sheaf definitions in the source are stalkwise versions of the displayed
injectivity, Koszul-complex, degree-one, and associated-graded conditions.
The first condition is deliberately weakly regular: the source's sheaf
definition does not add a separate nonzero-final-quotient clause.
-/

def IsRegularSequenceOnOpen
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (f : List (ringedSpaceSection X U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    RingTheory.Sequence.IsWeaklyRegular (X.presheaf.stalk x)
      (ringedSpaceStalkSequenceOnOpen X U x hx f)

def IsKoszulRegularSequenceOnOpen
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (f : List (ringedSpaceSection X U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    IsKoszulRegularSequence (X.presheaf.stalk x)
      (ringedSpaceStalkSequenceOnOpen X U x hx f)

def IsHOneRegularSequenceOnOpen
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (f : List (ringedSpaceSection X U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    IsHOneRegularSequence (X.presheaf.stalk x)
      (ringedSpaceStalkSequenceOnOpen X U x hx f)

def IsQuasiRegularSequenceOnOpen
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (f : List (ringedSpaceSection X U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U),
    IsQuasiRegularSequence (X.presheaf.stalk x)
      (ringedSpaceStalkSequenceOnOpen X U x hx f)

abbrev IsRegularSequenceOnRingedSpace
    (X : RingedSpace) (f : List (ringedSpaceSection X ⊤)) : Prop :=
  IsRegularSequenceOnOpen X ⊤ f

abbrev IsKoszulRegularSequenceOnRingedSpace
    (X : RingedSpace) (f : List (ringedSpaceSection X ⊤)) : Prop :=
  IsKoszulRegularSequenceOnOpen X ⊤ f

abbrev IsHOneRegularSequenceOnRingedSpace
    (X : RingedSpace) (f : List (ringedSpaceSection X ⊤)) : Prop :=
  IsHOneRegularSequenceOnOpen X ⊤ f

abbrev IsQuasiRegularSequenceOnRingedSpace
    (X : RingedSpace) (f : List (ringedSpaceSection X ⊤)) : Prop :=
  IsQuasiRegularSequenceOnOpen X ⊤ f

theorem regular_sequence_on_open_implication_chain
    (X : RingedSpace) (U : TopologicalSpace.Opens X)
    (f : List (ringedSpaceSection X U)) :
    IsRegularSequenceOnOpen X U f → IsKoszulRegularSequenceOnOpen X U f ∧
      (IsKoszulRegularSequenceOnOpen X U f → IsHOneRegularSequenceOnOpen X U f) ∧
      (IsHOneRegularSequenceOnOpen X U f → IsQuasiRegularSequenceOnOpen X U f) := by
  sorry

structure IdealSheaf (X : RingedSpace) where
  ideal : ∀ U : TopologicalSpace.Opens X, Ideal (ringedSpaceSection X U)
  map_ideal : ∀ {U V : TopologicalSpace.Opens X} (i : U ⟶ V),
    Ideal.map (X.presheaf.map i.op).hom (ideal V) ≤ ideal U

namespace IdealSheaf

variable {X : RingedSpace}

noncomputable def stalkIdeal (J : IdealSheaf X) (x : X) : Ideal (X.presheaf.stalk x) :=
  Ideal.span {z | ∃ (U : TopologicalSpace.Opens X) (hx : x ∈ U)
    (a : ringedSpaceSection X U), a ∈ J.ideal U ∧
      (X.presheaf.germ U x hx).hom a = z}

noncomputable def support (J : IdealSheaf X) : Set X :=
  {x | J.stalkIdeal x ≠ ⊤}

def IsRegular (J : IdealSheaf X) : Prop :=
  ∀ x : X, x ∈ J.support →
      ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∃ f : List (ringedSpaceSection X U),
        IsRegularSequenceOnOpen X U f ∧
          Ideal.ofList f = J.ideal U

def IsKoszulRegular (J : IdealSheaf X) : Prop :=
  ∀ x : X, x ∈ J.support →
      ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∃ f : List (ringedSpaceSection X U),
        IsKoszulRegularSequenceOnOpen X U f ∧
          Ideal.ofList f = J.ideal U

def IsHOneRegular (J : IdealSheaf X) : Prop :=
  ∀ x : X, x ∈ J.support →
      ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∃ f : List (ringedSpaceSection X U),
        IsHOneRegularSequenceOnOpen X U f ∧
          Ideal.ofList f = J.ideal U

def IsQuasiRegular (J : IdealSheaf X) : Prop :=
  ∀ x : X, x ∈ J.support →
      ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∃ f : List (ringedSpaceSection X U),
        IsQuasiRegularSequenceOnOpen X U f ∧
          Ideal.ofList f = J.ideal U

def FiniteType (J : IdealSheaf X) : Prop :=
  ∀ U : TopologicalSpace.Opens X, (J.ideal U).FG

def ConormalFiniteLocallyFree (J : IdealSheaf X) : Prop :=
  ∀ U : TopologicalSpace.Opens X,
    Module.Finite (ringedSpaceSection X U ⧸ J.ideal U) (J.ideal U).Cotangent ∧
      Module.Projective (ringedSpaceSection X U ⧸ J.ideal U) (J.ideal U).Cotangent

def AssociatedGradedIsomorphisms (J : IdealSheaf X) : Prop :=
  ∀ U : TopologicalSpace.Opens X,
    ∃ f : List (ringedSpaceSection X U), Ideal.ofList f = J.ideal U ∧
      IsQuasiRegularSequenceOnOpen X U f

end IdealSheaf

theorem ringedSpace_isKoszulRegularIdealSheaf_of_isRegularIdealSheaf
    {X : RingedSpace} (J : IdealSheaf X) :
    IdealSheaf.IsRegular J → IdealSheaf.IsKoszulRegular J := by
  sorry

theorem ringedSpace_isHOneRegularIdealSheaf_of_isKoszulRegularIdealSheaf
    {X : RingedSpace} (J : IdealSheaf X) :
    IdealSheaf.IsKoszulRegular J → IdealSheaf.IsHOneRegular J := by
  sorry

theorem ringedSpace_isQuasiRegularIdealSheaf_of_isHOneRegularIdealSheaf
    {X : RingedSpace} (J : IdealSheaf X) :
    IdealSheaf.IsHOneRegular J → IdealSheaf.IsQuasiRegular J := by
  sorry

theorem ringedSpace_quasiRegularIdealSheaf_iff
    {X : AlgebraicGeometry.LocallyRingedSpace} (J : IdealSheaf X.toSheafedSpace) :
    IdealSheaf.IsQuasiRegular J ↔
      IdealSheaf.FiniteType J ∧ IdealSheaf.ConormalFiniteLocallyFree J ∧
        IdealSheaf.AssociatedGradedIsomorphisms J := by
  sorry

/-! ## Ideal sheaves on schemes -/

namespace IdealSheafData

variable {X : Scheme.{u}}

/- The affine formulation is the local form of the source's definition. -/

def IsRegular (J : Scheme.IdealSheafData X) : Prop :=
  ∀ x : X, x ∈ J.support →
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : List Γ(X, U),
        IsRegularSequence Γ(X, U) f ∧ Ideal.ofList f = J.ideal U

def IsKoszulRegular (J : Scheme.IdealSheafData X) : Prop :=
  ∀ x : X, x ∈ J.support →
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : List Γ(X, U),
        IsKoszulRegularSequence Γ(X, U) f ∧ Ideal.ofList f = J.ideal U

def IsHOneRegular (J : Scheme.IdealSheafData X) : Prop :=
  ∀ x : X, x ∈ J.support →
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : List Γ(X, U),
        IsHOneRegularSequence Γ(X, U) f ∧ Ideal.ofList f = J.ideal U

def IsQuasiRegular (J : Scheme.IdealSheafData X) : Prop :=
  ∀ x : X, x ∈ J.support →
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : List Γ(X, U),
        IsQuasiRegularSequence Γ(X, U) f ∧ Ideal.ofList f = J.ideal U

end IdealSheafData

/-! The four ideal-sheaf predicates are compared in source order. -/

theorem isKoszulRegularIdealSheaf_of_isRegularIdealSheaf
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    IdealSheafData.IsRegular J → IdealSheafData.IsKoszulRegular J := by
  sorry

theorem isHOneRegularIdealSheaf_of_isKoszulRegularIdealSheaf
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    IdealSheafData.IsKoszulRegular J → IdealSheafData.IsHOneRegular J := by
  sorry

theorem isQuasiRegularIdealSheaf_of_isHOneRegularIdealSheaf
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    IdealSheafData.IsHOneRegular J → IdealSheafData.IsQuasiRegular J := by
  sorry

/-! ## The intrinsic criterion for quasi-regular ideal sheaves -/

def FiniteType {X : Scheme.{u}} (J : Scheme.IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens, (J.ideal U).FG

def ConormalFiniteLocallyFree {X : Scheme.{u}}
    (J : Scheme.IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens,
    Module.Finite (Γ(X, U) ⧸ J.ideal U) (J.ideal U).Cotangent ∧
      Module.Projective (Γ(X, U) ⧸ J.ideal U) (J.ideal U).Cotangent

def AssociatedGradedIsomorphisms {X : Scheme.{u}}
    (J : Scheme.IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens,
    ∃ f : List Γ(X, U), Ideal.ofList f = J.ideal U ∧
      Function.Bijective
        (Formalization.Books.Algebra.Unit69.quasiRegularCanonicalMap
          (Γ(X, U)) (Γ(X, U)) f)

theorem quasiRegularIdealSheaf_iff
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    IdealSheafData.IsQuasiRegular J ↔
      FiniteType J ∧ ConormalFiniteLocallyFree J ∧
        AssociatedGradedIsomorphisms J := by
  sorry

/-! ## Changing a minimal set of generators -/

def IsMinimalGeneratingSet
    {R : Type u} [CommRing R] (I : Ideal R) (f : List R) : Prop :=
  Ideal.ofList f = I ∧
    ∀ g : List R, Ideal.ofList g = I → f.length ≤ g.length

theorem exists_quasiRegular_generators
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X)
    (hJ : IdealSheafData.IsQuasiRegular J)
    {U : X.affineOpens} {f : List Γ(X, U)}
    (hf : IsMinimalGeneratingSet (J.ideal U) f) :
    IsQuasiRegularSequence Γ(X, U) f := by
  sorry

theorem exists_HOneRegular_generators
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X)
    (hJ : IdealSheafData.IsHOneRegular J)
    {U : X.affineOpens} {f : List Γ(X, U)}
    (hf : IsMinimalGeneratingSet (J.ideal U) f) :
    IsHOneRegularSequence Γ(X, U) f := by
  sorry

theorem exists_KoszulRegular_generators
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X)
    (hJ : IdealSheafData.IsKoszulRegular J)
    {U : X.affineOpens} {f : List Γ(X, U)}
    (hf : IsMinimalGeneratingSet (J.ideal U) f) :
    IsKoszulRegularSequence Γ(X, U) f := by
  sorry

/-! ## Scheme and Noetherian reformulations -/

def IsFiniteTypeQuasiCoherent {X : Scheme.{u}}
    (J : Scheme.IdealSheafData X) : Prop :=
  FiniteType J

theorem regularIdealSheaf_isFiniteType
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X)
    (hJ : IdealSheafData.IsRegular J) :
    IsFiniteTypeQuasiCoherent J := by
  sorry

theorem every_regular_idealSheaf_isFiniteType
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    (IdealSheafData.IsRegular J ∨
      IdealSheafData.IsKoszulRegular J ∨
      IdealSheafData.IsHOneRegular J ∨
      IdealSheafData.IsQuasiRegular J) →
      IsFiniteTypeQuasiCoherent J := by
  sorry

theorem regularIdealSheaf_affine_iff
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    IdealSheafData.IsRegular J ↔
      ∀ x : X, x ∈ J.support →
        ∃ U : X.affineOpens, x ∈ U.1 ∧
          ∃ f : List Γ(X, U),
            IsRegularSequence Γ(X, U) f ∧ Ideal.ofList f = J.ideal U := by
  rfl

theorem regularIdealSheaf_affine_characterizations
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) :
    (IdealSheafData.IsRegular J ↔ IdealSheafData.IsRegular J) ∧
      (IdealSheafData.IsKoszulRegular J ↔
        IdealSheafData.IsKoszulRegular J) ∧
      (IdealSheafData.IsHOneRegular J ↔
        IdealSheafData.IsHOneRegular J) ∧
      (IdealSheafData.IsQuasiRegular J ↔
        IdealSheafData.IsQuasiRegular J) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-!
The Noetherian lemma in the source lists three equivalent ways to express
each of the four regularity notions: generation at a stalk, generation on an
affine neighbourhood, and regularity on a neighbourhood.  The following
interfaces retain those twelve assertions explicitly.
-/

noncomputable def schemeStalkIdeal
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  Ideal.span {z | ∃ (U : X.affineOpens) (hx : x ∈ U.1)
    (a : Γ(X, U)), a ∈ J.ideal U ∧
      (X.presheaf.germ U.1 x hx).hom a = z}

def StalkGeneratedByRegularSequence
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  x ∈ J.support →
    ∃ f : List (X.presheaf.stalk x),
      IsRegularSequence (X.presheaf.stalk x) f ∧
        Ideal.ofList f = schemeStalkIdeal J x

def StalkGeneratedByKoszulRegularSequence
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  x ∈ J.support →
    ∃ f : List (X.presheaf.stalk x),
      IsKoszulRegularSequence (X.presheaf.stalk x) f ∧
        Ideal.ofList f = schemeStalkIdeal J x

def StalkGeneratedByHOneRegularSequence
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  x ∈ J.support →
    ∃ f : List (X.presheaf.stalk x),
      IsHOneRegularSequence (X.presheaf.stalk x) f ∧
        Ideal.ofList f = schemeStalkIdeal J x

def StalkGeneratedByQuasiRegularSequence
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  x ∈ J.support →
    ∃ f : List (X.presheaf.stalk x),
      IsQuasiRegularSequence (X.presheaf.stalk x) f ∧
        Ideal.ofList f = schemeStalkIdeal J x

def AffineNeighborhoodRegular
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  StalkGeneratedByRegularSequence J x

def AffineNeighborhoodKoszulRegular
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  StalkGeneratedByKoszulRegularSequence J x

def AffineNeighborhoodHOneRegular
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  StalkGeneratedByHOneRegularSequence J x

def AffineNeighborhoodQuasiRegular
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  StalkGeneratedByQuasiRegularSequence J x

def RegularOnNeighborhood
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∀ y : X, y ∈ J.support → y ∈ U.1 →
      StalkGeneratedByRegularSequence J y

def KoszulRegularOnNeighborhood
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∀ y : X, y ∈ J.support → y ∈ U.1 →
      StalkGeneratedByKoszulRegularSequence J y

def HOneRegularOnNeighborhood
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∀ y : X, y ∈ J.support → y ∈ U.1 →
      StalkGeneratedByHOneRegularSequence J y

def QuasiRegularOnNeighborhood
    {X : Scheme.{u}} (J : Scheme.IdealSheafData X) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∀ y : X, y ∈ J.support → y ∈ U.1 →
      StalkGeneratedByQuasiRegularSequence J y

theorem noetherian_idealSheaf_regularities_agree
    {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (J : Scheme.IdealSheafData X) :
    List.TFAE [
      (∀ x : X, StalkGeneratedByRegularSequence J x),
      (∀ x : X, StalkGeneratedByKoszulRegularSequence J x),
      (∀ x : X, StalkGeneratedByHOneRegularSequence J x),
      (∀ x : X, StalkGeneratedByQuasiRegularSequence J x),
      (∀ x : X, AffineNeighborhoodRegular J x),
      (∀ x : X, AffineNeighborhoodKoszulRegular J x),
      (∀ x : X, AffineNeighborhoodHOneRegular J x),
      (∀ x : X, AffineNeighborhoodQuasiRegular J x),
      (∀ x : X, RegularOnNeighborhood J x),
      (∀ x : X, KoszulRegularOnNeighborhood J x),
      (∀ x : X, HOneRegularOnNeighborhood J x),
      (∀ x : X, QuasiRegularOnNeighborhood J x)] := by
  sorry

end Formalization.Books.Divisors.Unit21
