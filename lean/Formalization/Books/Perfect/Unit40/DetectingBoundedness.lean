import Formalization.Books.Perfect.Unit40.Core

/-!
# Detecting Boundedness

This file contains the declarations corresponding to Section 40 of
*Derived Categories of Schemes*.  The proofs are intentionally deferred; the
interfaces retain the source hypotheses and all six auxiliary criteria in
each of the two boundedness propositions.
-/

namespace Formalization.Books.Perfect.Unit40

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

variable {X U : Scheme} {C D : Type*}
  [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  [DerivedCategoryData X C] [DerivedCategoryData U D]

/-- Orthogonality to `K` in degrees at least `a`. -/
def OrthogonalAbove (K E : C) (a : ℤ) : Prop :=
  ∀ n : ℤ, a ≤ n → HomVanishes
    (Shift (X := X) (C := C) K (-n)) E

/-- Orthogonality to `K` in degrees at most `a`. -/
def OrthogonalBelow (K E : C) (a : ℤ) : Prop :=
  ∀ n : ℤ, n ≤ a → HomVanishes
    (Shift (X := X) (C := C) K (-n)) E

/-- Lemma 40.1 (the first orthogonal Koszul variant). -/
theorem orthogonal_koszul_first_variant
    (R : OpenImmersionData X U C D)
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    (K : KoszulObject R A r f) (E : C) (a : ℤ)
    (_hE : IsQCoh (X := X) (C := C) E) :
    OrthogonalAbove (X := X) (C := C) K.object E a →
      IsIso (TruncGEComparison R E a) ∧
        (IsIso (TruncGEComparison R E a) →
          OrthogonalAbove (X := X) (C := C) K.object E (a + 1)) := by
  sorry

/-- Lemma 40.2 (the second orthogonal Koszul variant). -/
theorem orthogonal_koszul_second_variant
    (R : OpenImmersionData X U C D)
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    (K : KoszulObject R A r f) (E : C) (a : ℤ)
    (_hE : IsQCoh (X := X) (C := C) E) :
    OrthogonalBelow (X := X) (C := C) K.object E a →
      IsIso (TruncLEComparison R E a) ∧
        (IsIso (TruncLEComparison R E a) →
          OrthogonalBelow (X := X) (C := C) K.object E (a - 1)) := by
  sorry

section BoundedTruncation

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- Lemma 40.3 (bounded truncation). -/
theorem bounded_truncation
    (P E : C) (a : ℤ)
    (_hP : IsPerfect (X := X) (C := C) P)
    (_hE : IsQCoh (X := X) (C := C) E) :
    HomVanishesAbove (X := X) (C := C) P E ↔
      HomVanishesAbove (X := X) (C := C) P
        (TruncGE (X := X) (C := C) E a) := by
  sorry

/-- Lemma 40.4 (bounded-below truncation). -/
theorem bounded_below_truncation
    (P E : C) (a : ℤ)
    (_hP : IsPerfect (X := X) (C := C) P)
    (_hE : IsQCoh (X := X) (C := C) E) :
    HomVanishesBelow (X := X) (C := C) P E ↔
      HomVanishesBelow (X := X) (C := C) P
        (TruncLE (X := X) (C := C) E a) := by
  sorry

end BoundedTruncation

/-- The five tests attached to a fixed perfect object in the bounded-above
proposition.  The first three are the source's assertions (7)(a), and the
last two are (7)(b) and (7)(c). -/
def PerfectTestsAbove (E : C) : Prop :=
  ∀ P : C, IsPerfect (X := X) (C := C) P →
    HomVanishesAbove (X := X) (C := C) P E ∧
      ExtVanishesAbove (X := X) (C := C) P E ∧
      InDMinus (RHom (X := X) (C := C) P E) ∧
      CohomologyVanishesAbove
        (RΓ (X := X) (C := C)
          (Tensor (X := X) (C := C) P E)) ∧
      InDMinus
        (RΓ (X := X) (C := C)
          (Tensor (X := X) (C := C) P E))

/-- The five tests attached to a fixed perfect object in the bounded-below
proposition. -/
def PerfectTestsBelow (E : C) : Prop :=
  ∀ P : C, IsPerfect (X := X) (C := C) P →
    HomVanishesBelow (X := X) (C := C) P E ∧
      ExtVanishesBelow (X := X) (C := C) P E ∧
      InDPlus (RHom (X := X) (C := C) P E) ∧
      CohomologyVanishesBelow
        (RΓ (X := X) (C := C)
          (Tensor (X := X) (C := C) P E)) ∧
      InDPlus
        (RΓ (X := X) (C := C)
          (Tensor (X := X) (C := C) P E))

/-- The displayed pushforward identity used in the bounded-above proof.

The source writes equality for objects of a derived category; the second
component uses the canonical categorical isomorphism supplied by
`OpenImmersionData`. -/
theorem detecting_bounded_above_pushforward_identity
    (R : OpenImmersionData X U C D) (K : D) :
    KoszulExtension R K = R.pushforwardStar K ∧
      Nonempty (KoszulExtension R K ≅ R.pushforwardShriek K) :=
  ⟨koszulExtension_eq_pushforwardStar R K,
    koszulExtension_iso_pushforwardShriek R K⟩

/-- Proposition 40.5 (detecting boundedness above). -/
theorem detecting_bounded_above
    [CompactSpace X] [QuasiSeparatedSpace X]
    (G E : C)
    (_hG : IsPerfect (X := X) (C := C) G)
    (_hGenerator : GeneratesQCoh (X := X) (C := C) G)
    (_hE : IsQCoh (X := X) (C := C) E) :
    ObjectBoundedAbove (X := X) (C := C) E ↔
      HomVanishesAbove (X := X) (C := C) G E ∧
        ExtVanishesAbove (X := X) (C := C) G E ∧
        InDMinus (RHom (X := X) (C := C) G E) ∧
        CohomologyVanishesAbove
          (RΓ (X := X) (C := C)
            (Tensor (X := X) (C := C)
              (Dual (X := X) (C := C) G) E)) ∧
        InDMinus
          (RΓ (X := X) (C := C)
            (Tensor (X := X) (C := C)
              (Dual (X := X) (C := C) G) E)) ∧
        PerfectTestsAbove (X := X) (C := C) E := by
  sorry

/-- The displayed pushforward identity used in the bounded-below proof. -/
theorem detecting_bounded_below_pushforward_identity
    (R : OpenImmersionData X U C D) (K : D) :
    KoszulExtension R K = R.pushforwardStar K ∧
      Nonempty (KoszulExtension R K ≅ R.pushforwardShriek K) :=
  ⟨koszulExtension_eq_pushforwardStar R K,
    koszulExtension_iso_pushforwardShriek R K⟩

/-- Proposition 40.6 (detecting boundedness below). -/
theorem detecting_bounded_below
    [CompactSpace X] [QuasiSeparatedSpace X]
    (G E : C)
    (_hG : IsPerfect (X := X) (C := C) G)
    (_hGenerator : GeneratesQCoh (X := X) (C := C) G)
    (_hE : IsQCoh (X := X) (C := C) E) :
    ObjectBoundedBelow (X := X) (C := C) E ↔
      HomVanishesBelow (X := X) (C := C) G E ∧
        ExtVanishesBelow (X := X) (C := C) G E ∧
        InDPlus (RHom (X := X) (C := C) G E) ∧
        CohomologyVanishesBelow
          (RΓ (X := X) (C := C)
            (Tensor (X := X) (C := C)
              (Dual (X := X) (C := C) G) E)) ∧
        InDPlus
          (RΓ (X := X) (C := C)
            (Tensor (X := X) (C := C)
              (Dual (X := X) (C := C) G) E)) ∧
        PerfectTestsBelow (X := X) (C := C) E := by
  sorry

end Formalization.Books.Perfect.Unit40
