import Formalization.Books.MoreAlgebra.Unit32.RegularIdeals
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.Algebra.Unit136.SyntomicMorphisms
import Formalization.Books.Algebra.Unit155.Henselization
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 33: Local complete intersection maps

The presentations in this chapter use Mathlib's `Algebra.Generators`: a
generator family is the same data as a surjective map from a polynomial
algebra.  The Koszul-regular ideal predicate is the local predicate from
More on Algebra, Chapter 32.  Cotangent and exact-sequence statements use
the presentation-independent maps from the earlier Algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit33

open Formalization.Books.MoreAlgebra.Unit30
open Formalization.Books.MoreAlgebra.Unit32
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Local complete intersection maps -/

/-- A ring map is local complete intersection when it is of finite type and
has a finite polynomial presentation with Koszul-regular kernel. -/
def IsLocalCompleteIntersection
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  RingHom.FiniteType (algebraMap R S) ∧
    ∃ (n : ℕ) (P : Algebra.Generators R S (Fin n)),
      IsKoszulRegularIdeal P.toExtension.Ring P.toExtension.ker

/-! ## Independence of a polynomial presentation -/

/-- The kernel of a Koszul-regular finite polynomial presentation remains
Koszul-regular for every other finite polynomial presentation of the same
algebra. -/
theorem koszulRegularIdeal_kernel_independent_of_presentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n m : ℕ} (P : Algebra.Generators R S (Fin n))
    (Q : Algebra.Generators R S (Fin m))
    (hP : IsKoszulRegularIdeal P.toExtension.Ring P.toExtension.ker) :
    IsKoszulRegularIdeal Q.toExtension.Ring Q.toExtension.ker := by
  sorry

/-- For a fixed finite polynomial presentation, the kernel condition is
equivalent to the intrinsic local-complete-intersection predicate. -/
theorem isLocalCompleteIntersection_iff_presentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (P : Algebra.Generators R S (Fin n)) :
    IsLocalCompleteIntersection R S ↔
      IsKoszulRegularIdeal P.toExtension.Ring P.toExtension.ker := by
  sorry

/-! ## Locality -/

/-- Local complete intersection maps can be checked on a finite principal
open cover of the target. -/
theorem isLocalCompleteIntersection_of_principalCover
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {m : ℕ} (g : Fin m → S)
    (hgen : Ideal.span (Set.range g) = (⊤ : Ideal S))
    (hlocal : ∀ i, IsLocalCompleteIntersection R
      (Localization.Away (g i))) :
    IsLocalCompleteIntersection R S := by
  sorry

/-! ## Relative global complete intersections -/

/-- In a relative global complete-intersection presentation, the defining
relations form a Koszul-regular sequence. -/
theorem isKoszulRegular_of_relativeGlobalCompleteIntersectionPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ} (P : Algebra.Generators R S (Fin n))
    (f : Fin c → P.toExtension.Ring)
    (h : Formalization.Books.Algebra.Unit136.IsPolynomialQuotientPresentation
      P f ∧
      ∀ p : PrimeSpectrum R,
        Nonempty (PrimeSpectrum
          (Formalization.Books.Algebra.Unit136.Fiber R S p)) →
          ringKrullDim
              (Formalization.Books.Algebra.Unit136.Fiber R S p) =
            (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    IsKoszulRegular P.toExtension.Ring (List.ofFn f) := by
  sorry

/-! ## Syntomic maps -/

/-- Syntomicity is equivalent to flatness together with the intrinsic local
complete-intersection condition. -/
theorem isSyntomic_iff_flat_and_isLocalCompleteIntersection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Formalization.Books.Algebra.Unit136.IsSyntomic (algebraMap R S) ↔
      RingHom.Flat (algebraMap R S) ∧ IsLocalCompleteIntersection R S := by
  sorry

/-! ## The transitive conormal and cotangent exact sequences -/

/-- The exactness package appearing at the end of the transitivity lemma.
The first two conjuncts are the top and bottom rows of the conormal diagram;
the remaining conjuncts are the six-term Jacobi--Zariski sequence with a zero
on the left. -/
def TransitiveLciExactConclusion
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {σ ι : Type v} (P : Algebra.Generators A B σ)
    (Q : Algebra.Generators B C ι) : Prop :=
  Function.Exact
      (LinearMap.liftBaseChange C
        (Algebra.Extension.CotangentSpace.map
          (Q.toComp P).toExtensionHom))
      (Algebra.Extension.CotangentSpace.map
        (Q.ofComp P).toExtensionHom) ∧
    Function.Exact
      ((Algebra.Extension.Cotangent.map
        (Q.toComp P).toExtensionHom).liftBaseChange C)
      (Algebra.Extension.Cotangent.map
        (Q.ofComp P).toExtensionHom) ∧
    Function.Injective (Algebra.H1Cotangent.map A B C C) ∧
    Function.Exact (Algebra.H1Cotangent.map A B C C)
        (Algebra.H1Cotangent.δ A B C) ∧
      Function.Exact (Algebra.H1Cotangent.δ A B C)
        (KaehlerDifferential.mapBaseChange A B C) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange A B C)
        (KaehlerDifferential.map A B C C) ∧
      Function.Surjective (KaehlerDifferential.map A B C C)

/-- For presentations `A → B` and `B → C`, the canonical conormal and
cotangent-space rows are exact.  If `B → C` is local complete intersection,
the first cotangent-homology map is injective, so the Jacobi--Zariski
sequence has a zero on the left and is exact through the final Kähler map.

The two row maps are Mathlib's canonical maps for `Q.toComp P` and
`Q.ofComp P`; thus the displayed exactness records the source's canonical
commutative diagram without introducing a second presentation API. -/
theorem transitive_lci_conormal_and_cotangent_exact
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {σ ι : Type v} (P : Algebra.Generators A B σ)
    (Q : Algebra.Generators B C ι)
    (hBC : IsLocalCompleteIntersection B C) :
    TransitiveLciExactConclusion P Q := by
  sorry

/-! ## Filtered colimits and henselizations -/

/-- A filtered colimit of local complete intersection maps, in the same
filtered-ring-colimit presentation used by the earlier Algebra chapters. -/
structure FilteredLocalCompleteIntersectionColimit
    {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C)
    extends Formalization.Books.Algebra.Unit154.FilteredColimitData f where
  stage : ∀ i,
    letI : Algebra B (diagram.obj i).right :=
      (diagram.obj i).hom.hom.toAlgebra
    IsLocalCompleteIntersection B (diagram.obj i).right

/-- The transitive exact-sequence conclusion is unchanged when `B → C` is a
filtered colimit of local complete intersection maps. -/
theorem transitive_colimit_lci_at_end
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {σ ι : Type v} (P : Algebra.Generators A B σ)
    (Q : Algebra.Generators B C ι)
    (hcolim : Nonempty
      (FilteredLocalCompleteIntersectionColimit (algebraMap B C))) :
    TransitiveLciExactConclusion P Q := by
  sorry

/- The earlier Algebra API exposes the degree-one homology of the naive
cotangent complex and its degree-zero cokernel.  A comparison package records
the two induced cohomology isomorphisms without pretending that a full
derived cotangent-complex object has already been formalized. -/
structure NaiveCotangentCohomologyComparison
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A B']
    [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] where
  h1Map : B' ⊗[B] Algebra.H1Cotangent A B →ₗ[B']
    Algebra.H1Cotangent A' B'
  h1Bijective : Function.Bijective h1Map
  h0Map : B' ⊗[B]
      Formalization.Books.Algebra.Unit134.NaiveCotangentCokernel A B →ₗ[B']
    Formalization.Books.Algebra.Unit134.NaiveCotangentCokernel A' B'
  h0Bijective : Function.Bijective h0Map

/-- Henselization preserves both cohomology groups of the naive cotangent
complex.  The maps `ψ` are the functorial maps between chosen henselizations;
the comparison structure records the two induced isomorphisms. -/
theorem henselization_NL_cohomology_iso
    {A B Ah Bh : Type u} [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing Ah] [IsLocalRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh]
    [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]
    (φ : A →+* B) (hφ : IsLocalHom φ)
    (ιA : A →+* Ah)
    (hιA : Formalization.Books.Algebra.Unit155.IsHenselizationMap A Ah ιA)
    (ιB : B →+* Bh)
    (hιB : Formalization.Books.Algebra.Unit155.IsHenselizationMap B Bh ιB) :
    ∃ ψ : Ah →+* Bh,
      IsLocalHom ψ ∧ ψ.comp ιA = ιB.comp φ ∧
        Nonempty (NaiveCotangentCohomologyComparison (A := A) (B := B)
          (A' := Ah) (B' := Bh)) := by
  sorry

/-- The strict-henselization analogue of the preceding comparison, with the
induced local map between chosen strict henselizations included in the
conclusion. -/
theorem strict_henselization_NL_cohomology_iso
    {A B Ash Bsh : Type u} [CommRing A] [CommRing B] [CommRing Ash]
    [CommRing Bsh] [IsLocalRing A] [IsLocalRing B] [IsLocalRing Ash]
    [IsLocalRing Bsh] [Algebra A B] [Algebra A Ash] [Algebra B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh]
    (φ : A →+* B) (hφ : IsLocalHom φ)
    (ιA : A →+* Ash)
    (hιA : Formalization.Books.Algebra.Unit155.IsStrictHenselization A Ash ιA)
    (ιB : B →+* Bsh)
    (hιB : Formalization.Books.Algebra.Unit155.IsStrictHenselization B Bsh ιB) :
    ∃ ψ : Ash →+* Bsh,
      IsLocalHom ψ ∧ ψ.comp ιA = ιB.comp φ ∧
        Nonempty (NaiveCotangentCohomologyComparison (A := A) (B := B)
          (A' := Ash) (B' := Bsh)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit33
