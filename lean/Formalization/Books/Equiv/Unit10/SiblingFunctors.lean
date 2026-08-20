import Formalization.Books.Equiv.Unit10.Core

/-!
# Derived Categories of Varieties, Chapter 10: sibling functors

The declarations below formalize the definition, lemmas, and proposition in
the source section.  Proofs are intentionally deferred to the prove stage.
-/

namespace Formalization.Books.Equiv.Unit10

open CategoryTheory
open CategoryTheory.Limits

variable {A C D : Type*} [Category A] [Abelian A]
  [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]

/-! ## Siblings and their formal consequences -/

/-- If negative Exts between the images of heart objects vanish, then two
exact functors with isomorphic restrictions to the heart are siblings. -/
theorem siblings_of_negative_ext_vanishing
    (ι : A ⥤ C) (F F' : ExactTriangulatedFunctor C D)
    (hι : Nonempty (ι ⋙ F.toFunctor ≅ ι ⋙ F'.toFunctor))
    (hneg : ∀ X Y : A, ∀ q : ℤ, q < 0 →
      ExtVanishes (D := D) (F.toFunctor.obj (ι.obj X))
        (F.toFunctor.obj (ι.obj Y)) q) :
    Siblings (A := A) (C := C) (D := D) ι F F' := by
  sorry

/-- A sibling of an essentially surjective functor is essentially surjective. -/
theorem sibling_essSurj
    (ι : A ⥤ C) (F F' : ExactTriangulatedFunctor C D)
    (h : Siblings (A := A) (C := C) (D := D) ι F F')
    (hF : F.toFunctor.EssSurj) :
    F'.toFunctor.EssSurj := by
  sorry

/-- A sibling of a fully faithful functor is fully faithful. -/
theorem sibling_fullyFaithful
    (ι : A ⥤ C) (F F' : ExactTriangulatedFunctor C D)
    (h : Siblings (A := A) (C := C) (D := D) ι F F')
    (hF : F.toFunctor.Full)
    (hF' : F.toFunctor.Faithful) :
    F'.toFunctor.Full ∧ F'.toFunctor.Faithful := by
  sorry

/-! ## Auxiliary maps and the main sibling-isomorphism theorem -/

/-- The good map lemma: the top cohomology of a bounded-above object admits a
surjection from a heart object with no maps back into that heart object. -/
theorem exists_good_map
    (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (hneg : HasEnoughNegativeObjects A) (X : C) (b : ℤ)
    (hX : CohomologyVanishesAbove (A := A) (C := C) ι X b) :
    ∃ (N : A)
      (f : (shiftFunctor C (-b)).obj (ι.obj N) ⟶ X),
      Epi (inducedCohomologyMap (A := A) (C := C) ι N X b f) ∧
        (∀ g : Cohomology (A := A) (C := C) ι X b ⟶ N, g = 0) := by
  sorry

/-- The good-map-zero lemma: when the target has no cohomology in degrees at
least `b`, the good map can be chosen to factor to zero through the target. -/
theorem exists_good_map_zero
    (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (hneg : HasEnoughNegativeObjects A)
    {X X' : C} (f : X ⟶ X') (b : ℤ)
    (hX : CohomologyVanishesAbove (A := A) (C := C) ι X b)
    (hX' : CohomologyVanishesAtLeast (A := A) (C := C) ι X' b) :
    ∃ (N : A)
      (g : (shiftFunctor C (-b)).obj (ι.obj N) ⟶ X),
      Epi (inducedCohomologyMap (A := A) (C := C) ι N X b g) ∧
        (∀ u : Cohomology (A := A) (C := C) ι X b ⟶ N, u = 0) ∧
        g ≫ f = 0 := by
  sorry

/-- For an object with finite cohomology width, `Width` is attained by an
interval of the form used in the source. -/
theorem width_spec
    (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι] (X : C)
    (hX : ∃ w : ℕ, HasWidth (A := A) (C := C) ι X w) :
    HasWidth (A := A) (C := C) ι X
      (Width (A := A) (C := C) ι X hX) := by
  sorry

/-- The minimality clause implicit in the source's definition of width. -/
theorem width_min
    (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι] (X : C)
    (hX : ∃ w : ℕ, HasWidth (A := A) (C := C) ι X w)
    (v : ℕ) (hv : HasWidth (A := A) (C := C) ι X v) :
    Width (A := A) (C := C) ι X hX ≤ v := by
  sorry

/-- Under full faithfulness of `F` and enough negative objects in the heart,
sibling functors are naturally isomorphic. -/
theorem siblings_isomorphic
    (ι : A ⥤ C) [CohomologyData (A := A) (C := C) ι]
    (F F' : ExactTriangulatedFunctor C D)
    (h : Siblings (A := A) (C := C) (D := D) ι F F')
    (hF : F.toFunctor.Full)
    (hF' : F.toFunctor.Faithful)
    (hneg : HasEnoughNegativeObjects A) :
    Nonempty (F.toFunctor ≅ F'.toFunctor) := by
  sorry

end Formalization.Books.Equiv.Unit10
