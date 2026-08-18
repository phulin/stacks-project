import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Commutative Algebra, Chapter 159: Constructing flat ring maps

This file records the four construction lemmas in the chapter.  The
ring-theoretic predicates use Mathlib's flatness, local-homomorphism,
finite-étale, residue-field, directed-colimit, and cardinal interfaces.
-/

namespace Formalization.Books.Algebra.Unit159

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

noncomputable section

universe u v w

/-! ## Flat local maps with a prescribed residue-field extension -/

/-- The source's condition on a flat local algebra with prescribed residue
field.  The quotient is given the canonical algebra structure induced by the
residue-field algebra of the base local ring. -/
def FlatLocalResidueFieldExtension
    (R : Type u) (S : Type v) (K : Type w)
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K] : Prop :=
  letI : Algebra (IsLocalRing.ResidueField R)
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :=
    inferInstanceAs
      (Algebra (R ⧸ IsLocalRing.maximalIdeal R)
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
  IsLocalHom (algebraMap R S) ∧
    Module.Flat R S ∧
      Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal S ∧
        Nonempty
          ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
            ≃ₐ[IsLocalRing.ResidueField R] K)

/-- A local ring admits a flat local extension with any prescribed extension
of its residue field. -/
theorem exists_flat_local_residueField_extension
    (R : Type u) [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : IsLocalRing S)
      (_ : Algebra R S),
      FlatLocalResidueFieldExtension R S K := by
  sorry

/-! ## Finite étale local systems -/

/-- A directed system of finite étale local `R`-algebras, together with a
local colimit and its prescribed residue field.  `presentation` is a chosen
directed-colimit presentation; the remaining fields record the locality and
finite-étale conditions on its stages and the residue-field identification.
The maximal-ideal equality records that the colimit has the local structure
constructed in the source lemma. -/
structure FiniteEtaleLocalAlgebraColimit
    {R A : Type u} {K : Type v}
    [CommRing R] [IsLocalRing R] [CommRing A] [Field K]
    (f : R →+* A)
    [Algebra (IsLocalRing.ResidueField R) K] where
  presentation : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit f
  targetLocal : IsLocalRing A
  targetLocalMap : IsLocalHom f
  targetMaximalIdeal :
    Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal A
  stagesLocal :
    ∀ i, letI : Preorder presentation.index := presentation.indexPreorder
      IsLocalRing (presentation.diagram.obj i).right
  stagesLocalMap :
    ∀ i, letI : Preorder presentation.index := presentation.indexPreorder
      IsLocalHom (presentation.diagram.obj i).hom.hom
  stagesInjective :
    ∀ i, letI : Preorder presentation.index := presentation.indexPreorder
      Function.Injective (presentation.diagram.obj i).hom.hom
  stagesFiniteEtale :
    ∀ i, letI : Preorder presentation.index := presentation.indexPreorder
      RingHom.Finite (presentation.diagram.obj i).hom.hom ∧
        RingHom.Etale (presentation.diagram.obj i).hom.hom
  transitionLocal :
    ∀ {i j},
      letI : Preorder presentation.index := presentation.indexPreorder
      ∀ (h : i ≤ j),
        IsLocalHom (presentation.diagram.map (homOfLE h)).right.hom
  residueField :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra (IsLocalRing.ResidueField R)
        (A ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)) :=
      (Ideal.quotientMap (Ideal.map f (IsLocalRing.maximalIdeal R)) f
        Ideal.le_comap_map).toAlgebra
    Nonempty
      ((A ⧸ Ideal.map f (IsLocalRing.maximalIdeal R))
        ≃ₐ[IsLocalRing.ResidueField R] K)

/-- A separable algebraic residue-field extension is obtained as the residue
field of a directed colimit of finite étale local extensions. -/
theorem exists_finiteEtale_local_colimit_residueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A)
      (_ : Algebra R A),
      Nonempty
        (FiniteEtaleLocalAlgebraColimit
          (f := algebraMap R A) (R := R) (A := A) (K := K)) := by
  sorry

/-! ## Finite free maps with a prescribed finite residue-field extension -/

/-- The residue-field algebra induced by a map of prime quotients. -/
def ResidueFieldExtensionAtPrime
    {R : Type u} {S : Type w} {L : Type v} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) (f : R →+* S)
    (hq : q.comap f = p)
    (hqprime : q.IsPrime) [Field L] [Algebra p.ResidueField L] : Prop :=
  letI : q.IsPrime := hqprime
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q f hq.symm).toAlgebra
  Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L)

/-- The source's conclusion for a finite free extension at a prime.  The
lying-over equality is included so that the residue-field algebra structure
and the stated extension are canonical. -/
def FiniteFreeResidueFieldExtension
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (L : Type v) [Field L]
    [Algebra p.asIdeal.ResidueField L] : Prop :=
  let q : Ideal S := Ideal.map (algebraMap R S) p.asIdeal
  Module.Finite R S ∧ Module.Free R S ∧
    ∃ hq : q.IsPrime,
      ∃ hcomp : q.comap (algebraMap R S) = p.asIdeal,
        ResidueFieldExtensionAtPrime p.asIdeal q (algebraMap R S)
          (L := L) hcomp hq

/-- A finite extension of a residue field is realized by a finite free ring
map whose extended prime has exactly that residue-field extension. -/
theorem exists_finiteFree_residueField_extension
    (R : Type u) [CommRing R]
    (p : PrimeSpectrum R)
    (L : Type v) [Field L]
    [Algebra p.asIdeal.ResidueField L]
    [Module.Finite p.asIdeal.ResidueField L] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S),
      FiniteFreeResidueFieldExtension (R := R) (S := S) p L := by
  sorry

/-! ## Bounded flat subalgebras -/

/-- The cardinal bound `κ = max(|A|, aleph_0)` from the source. -/
def flatSubalgebraCardinal (A : Type u) : Cardinal :=
  Cardinal.mk A ⊔ Cardinal.aleph0

/-- A subalgebra satisfying the source's cardinal bound and flatness
condition. -/
def BoundedFlatSubalgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (S : Subalgebra A B) : Prop :=
  Module.Flat A S ∧ Cardinal.mk S ≤ flatSubalgebraCardinal A

/-- A cofinal filtered family of bounded flat subalgebras whose union is the
target.  The order relation between subalgebras supplies the canonical
transition maps, so this is the concrete directed-union form of the
corresponding filtered colimit. -/
structure DirectedBoundedFlatSubalgebraFamily
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] where
  index : Type v
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  stage : index → Subalgebra A B
  boundedFlat : ∀ i, BoundedFlatSubalgebra A B (stage i)
  stage_mono : Monotone stage
  cofinal : ∀ S : Subalgebra A B, BoundedFlatSubalgebra A B S →
    ∃ i, S ≤ stage i
  covers : ∀ b : B, ∃ i, b ∈ stage i

/-- Every flat algebra is the filtered union (equivalently, filtered
colimit) of its bounded flat subalgebras. -/
theorem exists_directed_boundedFlatSubalgebraFamily
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    Nonempty (DirectedBoundedFlatSubalgebraFamily A B) := by
  sorry

/-- If the original algebra is faithfully flat, each bounded flat subalgebra
occurring in the construction is faithfully flat over the base. -/
theorem boundedFlatSubalgebra_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (S : Subalgebra A B)
    (hS : BoundedFlatSubalgebra A B S) :
    Module.FaithfullyFlat A S := by
  sorry

end

end Formalization.Books.Algebra.Unit159
