import Formalization.Books.MoreAlgebra.Unit17.FlatteningArtinian
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation

/-!
# More on Algebra, Chapter 18: Flattening over a closed subset of the base

The source's stalkwise condition is expressed using the canonical
`flatAtPrimeOverBase` predicate.  Base changes use the extension-of-scalars
model from Chapter 14, and directed colimits use the established
`DirectedAlgebraColimit` interface.
-/

namespace Formalization.Books.MoreAlgebra.Unit18

open scoped TensorProduct

universe u

noncomputable section

/-! ## The flatness condition along a closed subset -/

/-- `M` is flat over `R` at every prime of `S` lying over `I`.

The inequality `I.map f ≤ q.asIdeal` is the canonical ideal-theoretic form of
`q ∈ V(IS)`.  The localized flatness predicate itself is the earlier
chapter's `flatAtPrimeOverBase`, which uses `LocalizedModule` and the
restriction of scalars from the localized `S`-algebra.
-/
def flatAtPrimesOver
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (I : Ideal R) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  ∀ q : PrimeSpectrum S, I.map f ≤ q.asIdeal →
    Formalization.Books.Algebra.Unit99.flatAtPrimeOverBase
      (R := R) (S := S) (M := M) q

/- The source's Noetherian finite-module observation is stated with the
  canonical quotient modules `M ⧸ (I ^ n • ⊤)`.  It is not a new definition:
  `flatAtPrimesOver` is the pointwise condition above, and the displayed
  equivalence is the source-facing form of Algebra, Lemma
  `algebra-lemma-flat-module-powers`. -/
theorem flatAtPrimesOver_iff_flat_quotient_powers
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (f : R →+* S) (I : Ideal R) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R M := Module.compHom M f
    letI : IsScalarTower R S M := SMul.comp.isScalarTower f
    flatAtPrimesOver (M := M) f I ↔
      ∀ n : ℕ, 0 < n →
        Module.Flat (R ⧸ I ^ n)
          (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  sorry

/-! ## Base change -/

/-- Flatness along `V(I)` is preserved by base change.

The target triple is the canonical `S ⊗[R] R'` and extension-of-scalars
model for `M ⊗[R] R'`; `hI` is the source's inclusion `IR' ⊆ I'`.
-/
theorem flatAtPrimesOver_baseChange
    {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (I : Ideal R)
    (g : R →+* R') (I' : Ideal R')
    (hI : I.map g ≤ I')
    (hflat : flatAtPrimesOver (M := M) f I) :
    flatAtPrimesOver
      (M := Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) I'
      := by
  sorry

/-! ## Descent -/

/-- Flatness along `V(I)` descends from a base change satisfying the two
closed-subset hypotheses in the source.

`hsurj` is the surjectivity of the induced map `V(I') → V(I)`, written in
the equivalent pointwise form.  `hflatLocal` says that every localized target
ring `R'_{p'}` with `p' ∈ V(I')` is flat over `R`, represented by the
canonical `RingHom.Flat` predicate.
-/
theorem flatAtPrimesOver_descent
    {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (I : Ideal R)
    (g : R →+* R') (I' : Ideal R')
    (hI : I.map g ≤ I')
    (hsurj : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      ∃ p' : PrimeSpectrum R', I' ≤ p'.asIdeal ∧
        PrimeSpectrum.comap g p' = p)
    (hflatLocal : ∀ p' : PrimeSpectrum R', I' ≤ p'.asIdeal →
      RingHom.Flat
        ((algebraMap R' (Localization.AtPrime p'.asIdeal)).comp g)) :
    flatAtPrimesOver
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) I'
        → flatAtPrimesOver (M := M) f I := by
  sorry

/-! ## Directed colimits -/

/-- A compatible family of ideals whose union in the represented target ideal
is exactly the colimit ideal.

The existing `DirectedAlgebraColimit` supplies the directed system and its
colimit cocone.  The membership characterization below is the concrete
set-level meaning of `I' = colim I_λ`; the first conjunct records the source's
compatibility `I_λ R_μ ⊆ I_μ`.
-/
/- The source presentation uses the stage-to-base maps of the directed
  algebra system.  This small wrapper supplies that canonical map with the
  dependent preorder instance already installed. -/
def directedAlgebraStageMap
    {R R' : Type u} [CommRing R] [CommRing R']
    {g : R →+* R'}
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit g)
    (i : D.index) :
    R →+* Formalization.Books.Algebra.Unit127.directedAlgebraStageRing D i := by
  letI : Preorder D.index := D.indexPreorder
  exact (D.diagram.obj i).hom.hom

def DirectedIdealColimit
    {R R' : Type u} [CommRing R] [CommRing R']
    {g : R →+* R'}
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit g)
    (I : ∀ i : D.index,
      Ideal (Formalization.Books.Algebra.Unit127.directedAlgebraStageRing D i))
    (I' : Ideal R') : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact
    (∀ {i j : D.index} (hij : D.indexPreorder.le i j),
      (I i).map (D.transitionMap hij) ≤ I j) ∧
      (∀ x : R', x ∈ I' ↔
        ∃ i : D.index,
          ∃ y : Formalization.Books.Algebra.Unit127.directedAlgebraStageRing D i,
          y ∈ I i ∧ D.stageToTarget i y = x)

/-- The flatness-along-`V(I')` condition on a directed colimit descends to a
sufficiently large stage when the original ring map and module are finitely
presented.

The proof-only open flat locus, its finite basic-open cover of `V(I'S')`, and
the eventual stage equation used to descend that cover are internal proof
scaffolding; the theorem records their source-level consequence.
-/
theorem flatAtPrimesOver_limit
    {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : RingHom.FinitePresentation f)
    (hM : Module.FinitePresentation S M)
    (g : R →+* R')
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit g)
    (I : ∀ i : D.index,
      Ideal (Formalization.Books.Algebra.Unit127.directedAlgebraStageRing D i))
    (I' : Ideal R')
    (hI : DirectedIdealColimit D I I')
    (hflat :
      flatAtPrimesOver
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) I'
        ) :
    ∃ i : D.index,
      flatAtPrimesOver
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f
          (directedAlgebraStageMap D i))
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f
          (directedAlgebraStageMap D i)) (I i) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit18
