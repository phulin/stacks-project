import Formalization.Books.Fields.Unit17.RootsOfUnity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Fields, Chapter 18: Finite fields

Finite fields are represented by Mathlib's canonical `Finite`/`Fintype`
instances.  The prime field is represented by the bottom `Subfield`, the
unit group by `Fˣ`, roots of unity by `rootsOfUnity`, and the exponent by
`Monoid.exponent`.  The declarations below expose the source-facing claims
without introducing parallel finite-field, exponent, or primitive-element
predicates.
-/

namespace Formalization.Books.Fields.Unit18

noncomputable section

open IntermediateField

universe u

/-! ## Characteristic, prime field, and cardinality -/

/- A finite field cannot have characteristic zero; the prime characteristic
   theorem also records the `p > 0` and primality assertions used by the source. -/
/-- A finite field has positive characteristic. -/
theorem finite_field_characteristic_pos
    (F : Type u) [Field F] [Finite F] :
    0 < ringChar F :=
  Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)

/-- The characteristic of a finite field is prime. -/
theorem finite_field_characteristic_prime
    (F : Type u) [Field F] [Finite F] :
    Nat.Prime (ringChar F) :=
  CharP.prime_ringChar F

/- `ZMod p` is Mathlib's canonical `𝔽_p`.  The local module structure in the
   conclusion is the canonical one induced by the characteristic map. -/
/-- The extension of a finite field over its prime field is finite-dimensional. -/
theorem finite_field_prime_field_extension_finite
    (F : Type u) [Field F] [Finite F] :
    let p := ringChar F
    letI : Fact (Nat.Prime p) := ⟨CharP.prime_ringChar F⟩
    letI : Module (ZMod p) F := (ZMod.castHom dvd_rfl F).toModule
    FiniteDimensional (ZMod p) F :=
  let p := ringChar F
  letI : Fact (Nat.Prime p) := ⟨CharP.prime_ringChar F⟩
  letI : Module (ZMod p) F := (ZMod.castHom dvd_rfl F).toModule
  (Module.finite_iff_finite (R := ZMod p) (M := F)).mpr inferInstance

/- `FiniteField.card` is the canonical Mathlib form of the source's
   `q = p^f`, with `ℕ+` recording `f ≥ 1`. -/
/-- A finite field has prime-power cardinality, with exponent at least one. -/
theorem finite_field_card_eq_prime_pow
    (F : Type u) [Field F] [Finite F] :
    ∃ f : ℕ+, Nat.Prime (ringChar F) ∧
      Nat.card F = ringChar F ^ (f : ℕ) := by
  obtain ⟨f, hp, hcard⟩ :=
    @FiniteField.card F _ (Fintype.ofFinite F) (ringChar F) inferInstance
  exact ⟨f, hp, (@Fintype.card_eq_nat_card F (Fintype.ofFinite F)).symm.trans hcard⟩

/-! ## Units, exponent, and roots of unity -/

/- The finite abelian group in the source is the canonical unit group. -/
/-- The unit group of a finite field has a positive exponent. -/
theorem finite_field_units_exponent_pos
    (F : Type u) [Field F] [Finite F] :
    0 < Monoid.exponent Fˣ :=
  Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Fˣ))

/-- Every unit of a finite field is killed by the exponent of its unit group. -/
theorem finite_field_units_pow_exponent_eq_one
    (F : Type u) [Field F] [Finite F] (u : Fˣ) :
    u ^ Monoid.exponent Fˣ = 1 :=
  Monoid.pow_exponent_eq_one u

/- The source's equality `F^* = μₑ(F)` is expressed in Mathlib's canonical
   subgroup representation as `rootsOfUnity e F = ⊤` in `Fˣ`. -/
/-- The roots of unity for the unit-group exponent are all of `Fˣ`. -/
theorem finite_field_units_eq_rootsOfUnity_exponent
    (F : Type u) [Field F] [Finite F] :
    rootsOfUnity (Monoid.exponent Fˣ) F = (⊤ : Subgroup Fˣ) := by
  ext u
  rw [mem_rootsOfUnity]
  constructor
  · intro _
    exact (show u ∈ (⊤ : Subgroup Fˣ) from Subgroup.mem_top u)
  · intro _
    exact Monoid.pow_exponent_eq_one u

/-- The multiplicative group of a finite field is cyclic. -/
theorem finite_field_units_is_cyclic
    (F : Type u) [Field F] [Finite F] :
    IsCyclic Fˣ := by
  infer_instance

/-- The unit group of a finite field has order `#F - 1`. -/
theorem finite_field_units_card
    (F : Type u) [Field F] [Finite F] :
    Nat.card Fˣ = Nat.card F - 1 :=
  Nat.card_units F

/- Once cyclicity is known, the exponent is the order of the group, so the
   source's parenthetical `e = q - 1` is an immediate canonical corollary. -/
/-- The exponent of the unit group is `#F - 1`. -/
theorem finite_field_units_exponent_eq_card_sub_one
    (F : Type u) [Field F] [Finite F] :
    Monoid.exponent Fˣ = Nat.card F - 1 := by
  calc
    Monoid.exponent Fˣ = Nat.card Fˣ := IsCyclic.exponent_eq_card
    _ = Nat.card F - 1 := finite_field_units_card F

/-! ## Primitive generation -/

/- The bottom subfield is the source's prime field `𝔽ₚ`; Unit 5 and
   Mathlib's `Subfield.bot_eq_of_zMod_algebra` identify it with `ZMod p`. -/
/-- A generator of the unit group generates the field over its prime subfield. -/
theorem field_adjoin_prime_subfield_eq_top_of_unit_generator
    (F : Type u) [Field F] (α : Fˣ)
    (hα : ∀ x : Fˣ, x ∈ Subgroup.zpowers α) :
    IntermediateField.adjoin (⊥ : Subfield F) ({(α : F)} : Set F) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  by_cases hx : x = 0
  · rw [hx]
    exact (IntermediateField.adjoin (⊥ : Subfield F) ({(α : F)} : Set F)).zero_mem
  · obtain ⟨n, hn⟩ := Set.mem_range.mp (hα (Units.mk0 x hx))
    rw [show x = (α : F) ^ n by
      norm_cast
      rw [hn, Units.val_mk0]]
    exact zpow_mem (mem_adjoin_simple_self (⊥ : Subfield F) (E := F) (α : F)) n

/-- A finite field has a unit generator that generates it over its prime field. -/
theorem finite_field_exists_unit_generator
    (F : Type u) [Field F] [Finite F] :
    ∃ α : Fˣ,
      IntermediateField.adjoin (⊥ : Subfield F) ({(α : F)} : Set F) = ⊤ := by
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Fˣ)
  exact ⟨α, field_adjoin_prime_subfield_eq_top_of_unit_generator F α hα⟩

/- Mathlib's finite-field primitive-element theorem gives the final assertion
   for an arbitrary finite extension of finite fields. -/
/-- A finite-dimensional extension of a finite field is generated by one element. -/
theorem finite_field_extension_has_primitive_element
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite F] [FiniteDimensional F E] :
    ∃ α : E, IntermediateField.adjoin F ({α} : Set E) = ⊤ :=
  Field.exists_primitive_element_of_finite_bot F E

end

end Formalization.Books.Fields.Unit18
