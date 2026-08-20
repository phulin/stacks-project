import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Divided Power Algebra, Chapter 10: Smooth ring maps and diagonals

This section records the two perfect-diagonal criteria for smooth ring maps.
The diagonal is the canonical multiplication map from the tensor square.
-/

namespace Formalization.Books.Dpa.Unit10

open scoped TensorProduct

noncomputable section

universe u

/-! ## The diagonal and its smooth localizations -/

/-- The multiplication map `B ⊗[A] B → B` attached to a ring map `f : A → B`.

The algebra structure on `B` is the canonical one induced by `f`, and the
map is Mathlib's canonical tensor-product multiplication map. -/
noncomputable def diagonalMap
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    letI : Algebra A B := f.toAlgebra
    (B ⊗[A] B) →+* B :=
  letI : Algebra A B := f.toAlgebra
  (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom

/-- A factorization of a ring map through a smooth algebra whose target is a
localization of that algebra. -/
structure SmoothLocalizationFactorization
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) where
  C : Type u
  [commRingC : CommRing C]
  [algebraAC : Algebra A C]
  [algebraCB : Algebra C B]
  g : C
  smooth : Algebra.Smooth A C
  localization : IsLocalization (Submonoid.powers g) B
  factorization : (algebraMap C B).comp (algebraMap A C) = f

/-! ## Perfect diagonals -/

/-- A local flat essentially-finite-type map of Noetherian local rings with a
perfect diagonal is the localization of a smooth algebra. -/
theorem local_perfect_diagonal
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hflat : RingHom.Flat f) (hessentiallyFiniteType : RingHom.EssFiniteType f)
    (hdiagonal : Formalization.Books.MoreAlgebra.Unit83.IsPerfectRingMap
      (diagonalMap f)) :
    Nonempty (SmoothLocalizationFactorization f) := by
  sorry

/-- A flat finite-type map of Noetherian rings with a perfect diagonal is
smooth. -/
theorem perfect_diagonal
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B)
    (hflat : RingHom.Flat f) (hfiniteType : RingHom.FiniteType f)
    (hdiagonal : Formalization.Books.MoreAlgebra.Unit83.IsPerfectRingMap
      (diagonalMap f)) :
    RingHom.Smooth f := by
  sorry

end

end Formalization.Books.Dpa.Unit10
