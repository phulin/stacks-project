import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Fields, Chapter 1: Introduction

The source recalls the definition of a field and records three standard
consequences: fields have only the zero and unit ideals, maps between fields
are injective, and domains embed in their quotient fields.  It also
introduces the residue field of a local ring.

The file uses Mathlib's canonical `IsField` predicate and `Field` typeclass;
it does not introduce a parallel field definition.  Likewise, the quotient
field is Mathlib's `FractionRing`, and the residue field is Mathlib's
`IsLocalRing.ResidueField`, whose defining body is the quotient by the
maximal ideal.

All propositions below use the weakest source hypotheses that Mathlib's
canonical constructions require.
-/

universe u

namespace Formalization.Books.Fields.Unit01

/-! ## Fields and their ideals -/

/- The source's field definition is exactly Mathlib's data-free `IsField`
   predicate after fixing the book's commutative-ring convention. -/
/-- A commutative ring is a field exactly when it is nonzero and every
nonzero element is a unit. -/
theorem isField_iff_nontrivial_forall_isUnit (R : Type u) [CommRing R] :
    IsField R ↔ Nontrivial R ∧ ∀ x : R, x ≠ 0 → IsUnit x := by
  constructor
  · intro h
    exact ⟨h.nontrivial, fun x hx =>
      let ⟨y, hy⟩ := h.mul_inv_cancel hx
      IsUnit.of_mul_eq_one y hy⟩
  · rintro ⟨hR, hunit⟩
    refine
      { exists_pair_ne := hR.exists_pair_ne
        mul_comm := mul_comm
        mul_inv_cancel := ?_ }
    intro x hx
    exact (hunit x hx).exists_right_inv

/- Mathlib's `Ring.isField_iff_isSimpleOrder_ideal` is the canonical
   equivalence behind the source's formulation in terms of the only two
   ideals `(0)` and `(1)`.  `⊥` and `⊤` are the ideal-lattice forms of those
   two ideals. -/
/-- A nonzero commutative ring is a field exactly when all its ideals are
either the zero ideal or the unit ideal. -/
theorem isField_iff_ideal_eq_bot_or_top (R : Type u) [CommRing R]
    [Nontrivial R] :
    IsField R ↔ ∀ I : Ideal R, I = ⊥ ∨ I = ⊤ := by
  rw [Ring.isField_iff_isSimpleOrder_ideal]
  constructor
  · intro h I
    exact h.eq_bot_or_eq_top I
  · intro h
    exact
      { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
        eq_bot_or_eq_top := h }

/-! ## Maps and quotient fields -/

/- The source's injectivity assertion is a field-specialized interface to
   Mathlib's stronger `RingHom.injective` theorem for maps out of simple
   rings. -/
/-- A ring homomorphism between fields is injective. -/
theorem field_hom_injective {K L : Type*} [Field K] [Field L]
    (f : K →+* L) : Function.Injective f := by
  exact RingHom.injective f

/- `FractionRing R` is Mathlib's quotient-field construction.  Under
   `IsDomain R`, its canonical `Field` instance is available and the
   localization map is injective. -/
/-- Every domain embeds in its canonical quotient field. -/
theorem domain_embeds_in_fraction_ring (R : Type u) [CommRing R] [IsDomain R] :
    Function.Injective (algebraMap R (FractionRing R)) := by
  exact IsLocalization.injective (FractionRing R) (le_refl _)

/-! ## Local rings and residue fields -/

/- Mathlib's `IsLocalRing` is the source's local-ring notion. -/
/-- A local ring has a unique maximal ideal. -/
theorem local_ring_has_unique_maximal_ideal (R : Type u) [CommRing R]
    [IsLocalRing R] :
    ∃! I : Ideal R, I.IsMaximal :=
  IsLocalRing.maximal_ideal_unique R

/- The source's residue-field phrase is definitionally represented by this
   quotient identity. -/
/-- The residue field is the quotient by the unique maximal ideal. -/
theorem local_ring_residue_field_eq_quotient (R : Type u) [CommRing R]
    [IsLocalRing R] :
    IsLocalRing.ResidueField R = (R ⧸ IsLocalRing.maximalIdeal R) := rfl

/-- The residue field of a local ring is a field. -/
theorem local_ring_residue_field_isField (R : Type u) [CommRing R]
    [IsLocalRing R] :
    IsField (IsLocalRing.ResidueField R) :=
  Field.toIsField _

end Formalization.Books.Fields.Unit01
