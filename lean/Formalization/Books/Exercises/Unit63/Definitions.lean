import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Exercises, Chapter 63: Definitions

The six requested definitions are represented by the canonical Mathlib
notions. In particular, the spectrum carries Mathlib's topology, and Tor is
the categorical left-derived tensor functor.
-/

namespace Formalization.Books.Exercises.Unit63

open CategoryTheory

universe u v

noncomputable section

/-! ## Definitions -/

/-- A multiplicative subset of a ring is Mathlib's `Submonoid`. -/
abbrev MultiplicativeSubset (A : Type u) [Monoid A] := Submonoid A

/-- The predicate that a ring is Artinian. -/
abbrev ArtinianRing (A : Type u) [Semiring A] : Prop := IsArtinianRing A

/-- The spectrum of a commutative ring, with its canonical topology. -/
abbrev RingSpectrum (A : Type u) [CommRing A] := PrimeSpectrum A

/-- Flatness of a ring map. -/
abbrev FlatRingMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop := RingHom.Flat f

/-- The height of a prime ideal. -/
def PrimeIdealHeight {A : Type u} [CommRing A] (p : PrimeSpectrum A) : ℕ∞ :=
  p.asIdeal.height

/-! The Tor functors in the category of modules. -/

/-- The `i`th Tor bifunctor over a commutative ring. -/
noncomputable def TorFunctor (A : Type u) [CommRing A] (i : ℕ) :
    ModuleCat A ⥤ ModuleCat A ⥤ ModuleCat A :=
  CategoryTheory.Tor (ModuleCat A) i

/-- The `i`th Tor module of two `A`-modules. -/
noncomputable abbrev TorModule (A : Type u) [CommRing A]
    (M N : ModuleCat A) (i : ℕ) : ModuleCat A :=
  ((TorFunctor A i).obj M).obj N

end

end Formalization.Books.Exercises.Unit63
