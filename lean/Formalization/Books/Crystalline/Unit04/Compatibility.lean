import Formalization.Books.Dpa.Unit04
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Crystalline Cohomology, Chapter 4: Compatibility

The source section introduces compatibility of divided powers and describes
the objects of Berthelot's big affine crystalline site.  The divided-power
ring and homomorphism interfaces are reused from the divided-power algebra
formalization; this file adds only the compatibility and site-object data
owned by this chapter.
-/

namespace Formalization.Books.Crystalline.Unit04

open CategoryTheory

universe u

noncomputable section

open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing
open Formalization.Books.Dpa.Unit04

/-! ## Compatibility of divided powers -/

/-- The divided-power ring with ideal `J + I B` occurring in the source's
compatibility definition. -/
def compatibilityEnvelope (A B : DividedPowerRing.{u})
    (f : (A : Type u) →+* (B : Type u))
    (bar : DividedPowers (B.ideal ⊔ Ideal.map f A.ideal)) : DividedPowerRing.{u} :=
  { toCommRing := B.toCommRing
    ideal := B.ideal ⊔ Ideal.map f A.ideal
    dividedPowers := bar }

/-- Berthelot compatibility: a divided-power structure on `J + I B` makes
both the given map from `(A, I, γ)` and the identity map from `(B, J, δ)`
homomorphisms of divided-power rings. -/
def DividedPowerCompatible (A B : DividedPowerRing.{u})
    (f : (A : Type u) →+* (B : Type u)) : Prop :=
  ∃ bar : DividedPowers (B.ideal ⊔ Ideal.map f A.ideal),
    (∃ h : DividedPowerRing.Hom A (compatibilityEnvelope A B f bar),
      h.hom = f) ∧
    (∃ h : DividedPowerRing.Hom B (compatibilityEnvelope A B f bar),
      h.hom = RingHom.id B)

/-- The source's simplified condition that the specified ring map is a
homomorphism of divided-power rings. -/
def IsDividedPowerHomAlong (A B : DividedPowerRing.{u})
    (f : (A : Type u) →+* (B : Type u)) : Prop :=
  ∃ h : DividedPowerRing.Hom A B, h.hom = f

/-! ## The setup used in the affine crystalline site -/

/-- The hypotheses fixed before the source's description of the big affine
crystalline site. -/
structure CompatibilitySetup where
  p : ℕ
  hp : Nat.Prime p
  A : DividedPowerRing.{u}
  C : Type u
  [commRingC : CommRing C]
  AtoC : (A : Type u) →+* C
  p_nilpotent : IsNilpotent (p : C)
  gamma_extends : DpExtends A AtoC

attribute [instance] CompatibilitySetup.commRingC

/-- The ideal `I C` used in the source is the image ideal under `A → C`. -/
def idealExtension (S : CompatibilitySetup.{u}) : Ideal S.C :=
  Ideal.map S.AtoC S.A.ideal

/-- The special case used in the rest of the source section, namely `I C = 0`.
The canonical image ideal is used rather than introducing a second notion of
extension of an ideal. -/
def IsZeroIdealExtension (S : CompatibilitySetup.{u}) : Prop :=
  idealExtension S = ⊥

/-! ## Systems defining the big affine crystalline site -/

/-- An object of the category whose opposite is Berthelot's big affine
crystalline site of `Spec(C)` over `Spec(A)`.

The fields are precisely the data displayed in the source: a divided-power
ring `(B, J, δ)`, the two maps, the nilpotence condition, compatibility, and
commutativity of the quotient square. -/
structure CrystallineSystem (S : CompatibilitySetup.{u}) where
  B : DividedPowerRing.{u}
  p_nilpotent : IsNilpotent (S.p : (B : Type u))
  AtoB : (S.A : Type u) →+* (B : Type u)
  CtoQuotient : S.C →+* ((B : Type u) ⧸ B.ideal)
  compatible : DividedPowerCompatible S.A B AtoB
  commutes : CtoQuotient.comp S.AtoC =
    (Ideal.Quotient.mk B.ideal).comp AtoB

/-- The map on ideal quotients induced by a ring map carrying one ideal into
the other. -/
def quotientMapOfIdealMap {R T : Type u} [CommRing R] [CommRing T]
    {I : Ideal R} {J : Ideal T} (f : R →+* T)
    (hf : ∀ {x : R}, x ∈ I → f x ∈ J) :
    (R ⧸ I) →+* (T ⧸ J) :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp f) (by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf hx))

theorem quotientMapOfIdealMap_comp {R T U : Type u} [CommRing R] [CommRing T]
    [CommRing U] {I : Ideal R} {J : Ideal T} {K : Ideal U}
    (f : R →+* T) (hf : ∀ {x : R}, x ∈ I → f x ∈ J)
    (g : T →+* U) (hg : ∀ {x : T}, x ∈ J → g x ∈ K) :
    quotientMapOfIdealMap (g.comp f) (fun hx => hg (hf hx)) =
      (quotientMapOfIdealMap g hg).comp (quotientMapOfIdealMap f hf) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

theorem quotientMapOfIdealMap_id {R : Type u} [CommRing R] {I : Ideal R} :
    quotientMapOfIdealMap (RingHom.id R)
        (show ∀ {x : R}, x ∈ I → RingHom.id R x ∈ I from by
          intro x hx
          simpa using hx) = RingHom.id (R ⧸ I) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

/-- A morphism of source systems is a divided-power-ring map on the `B`'s
that commutes with both displayed maps. -/
structure CrystallineSystem.Hom {S : CompatibilitySetup.{u}}
    (X Y : CrystallineSystem S) where
  hom : (X.B : Type u) →+* (Y.B : Type u)
  ideal_map : ∀ {x : X.B}, x ∈ X.B.ideal → hom x ∈ Y.B.ideal
  dpow_comm : ∀ {n : ℕ} {x : X.B}, x ∈ X.B.ideal →
    Y.B.dividedPowers.dpow n (hom x) = hom (X.B.dividedPowers.dpow n x)
  commutes_A : hom.comp X.AtoB = Y.AtoB
  commutes_C :
    (quotientMapOfIdealMap hom ideal_map).comp X.CtoQuotient = Y.CtoQuotient

namespace CrystallineSystem.Hom

@[ext]
theorem ext {S : CompatibilitySetup.{u}} {X Y : CrystallineSystem S}
    (f g : CrystallineSystem.Hom X Y) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  congr

end CrystallineSystem.Hom

instance (S : CompatibilitySetup.{u}) : Category (CrystallineSystem S) where
  Hom := CrystallineSystem.Hom
  id X :=
    { hom := RingHom.id _
      ideal_map := by
        intro x hx
        simpa using hx
      dpow_comm := by
        intro n x hx
        simp
      commutes_A := by
        ext x
        rfl
      commutes_C := by
        rw [quotientMapOfIdealMap_id]
        rfl }
  comp f g :=
    { hom := g.hom.comp f.hom
      ideal_map := by
        intro x hx
        exact g.ideal_map (f.ideal_map hx)
      dpow_comm := by
        intro n x hx
        simp only [RingHom.comp_apply]
        rw [g.dpow_comm (f.ideal_map hx), f.dpow_comm hx]
      commutes_A := by
        rw [RingHom.comp_assoc, f.commutes_A, g.commutes_A]
      commutes_C := by
        rw [quotientMapOfIdealMap_comp f.hom f.ideal_map g.hom g.ideal_map,
          RingHom.comp_assoc, f.commutes_C, g.commutes_C] }
  id_comp := by
    intro X Y f
    apply CrystallineSystem.Hom.ext _ _
    ext x
    rfl
  comp_id := by
    intro X Y f
    apply CrystallineSystem.Hom.ext _ _
    ext x
    rfl
  assoc := by
    intro W X Y Z f g h
    apply CrystallineSystem.Hom.ext _ _
    ext x
    rfl

/-- The big affine crystalline site in the source's presentation. -/
abbrev bigAffineCrystallineSite (S : CompatibilitySetup.{u}) :=
  (CrystallineSystem S)ᵒᵖ

/-! ## The `I C = 0` simplification -/

/-- In the special case `I C = 0`, commutativity of the quotient square forces
the extended ideal `I B` to lie in `J`. -/
theorem idealMap_le_of_zeroIdealExtension
    (S : CompatibilitySetup.{u}) (hIC : IsZeroIdealExtension S)
    (X : CrystallineSystem S) :
    Ideal.map X.AtoB S.A.ideal ≤ X.B.ideal := by
  sorry

/-- Under the same hypotheses, the source's compatibility condition is
equivalent to the fixed map `(A, I, γ) → (B, J, δ)` being a divided-power-ring
homomorphism. -/
theorem compatible_iff_dividedPowerHom
    (S : CompatibilitySetup.{u}) (hIC : IsZeroIdealExtension S)
    (X : CrystallineSystem S) :
    DividedPowerCompatible S.A X.B X.AtoB ↔
      IsDividedPowerHomAlong S.A X.B X.AtoB := by
  sorry

/-!
The source also explains that Berthelot uses extension of `γ` to `I C` and
compatibility to compare crystalline cohomology for `C` and `C / I C`.
This chapter does not define a crystalline cohomology object, so that
comparison is intentionally recorded as explanatory scope here; its exact
cohomological interface belongs to the later crystalline-cohomology chapters.
-/

end
end Formalization.Books.Crystalline.Unit04
