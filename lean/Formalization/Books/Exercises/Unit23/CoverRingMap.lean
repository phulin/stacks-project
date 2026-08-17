import Formalization.Books.Exercises.Unit23.Cover

import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Exercises, Chapter 23: Glueing

This file records the ring-map locality exercise.  The map from `A_a` to
`B_{ab}` is the canonical localization map induced by the algebra map
`A → B`; its body is built from the universal property of localization.
-/

namespace Formalization.Books.Exercises.Unit23

universe u v w z

noncomputable section

/-! ## Exercise `cover-ring-map` -/

/-- The canonical map `A_a → B_{(algebraMap A B a) b}`. -/
noncomputable def baseLocalizationToProductLocalization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (b : B) :
    Localization.Away a →+* Localization.Away (algebraMap A B a * b) :=
  IsLocalization.Away.lift (R := A) (S := Localization.Away a)
    (P := Localization.Away (algebraMap A B a * b))
    (g := (algebraMap B (Localization.Away (algebraMap A B a * b))).comp
      (algebraMap A B)) a
    (IsLocalization.Away.isUnit_of_dvd
      (S := Localization.Away (algebraMap A B a * b))
      (x := algebraMap A B a * b)
      (r := algebraMap A B a)
      (dvd_mul_right (algebraMap A B a) b))

/-- Finite type of a ring map can be checked on basic-open covers of source
and target, using the maps `A_{f_i} → B_{f_i g_j}`. -/
theorem finiteType_ringHom_of_basicOpenCovers
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type w} {κ : Type z} (f : ι → A) (g : κ → B)
    (hA : TopologicalSpace.IsOpenCover
      (fun i : ι => PrimeSpectrum.basicOpen (f i)))
    (hB : TopologicalSpace.IsOpenCover
      (fun j : κ => PrimeSpectrum.basicOpen (g j)))
    (hlocal : ∀ (i : ι) (j : κ),
      RingHom.FiniteType
        (baseLocalizationToProductLocalization (A := A) (B := B) (f i) (g j))) :
    RingHom.FiniteType (algebraMap A B) := by
  sorry

end

end Formalization.Books.Exercises.Unit23
