import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Examples, Chapter 15: Regular sequences and base change

This file formalizes the explicit module and square-zero-extension example in
the source section “Regular sequences and base change”.  The localizations and
quotients are the canonical Mathlib module constructions; the assertions in
the source are theorem interfaces because their proofs belong to the prove
stage.
-/

noncomputable section

universe u

namespace Formalization.Books.Examples.Unit15

open scoped Pointwise

/-- The three variables in the polynomial ring used by the example. -/
inductive RegularSequenceVariable where
  | x
  | y
  | z
deriving DecidableEq

/-- The polynomial ring `k[x, y, z]`. -/
abbrev PolynomialRing (k : Type u) [Field k] :=
  MvPolynomial RegularSequenceVariable k

/-- The image of one of the three polynomial variables. -/
def polynomialVariable (k : Type u) [Field k] (v : RegularSequenceVariable) : PolynomialRing k :=
  MvPolynomial.X v

def xPolynomial (k : Type u) [Field k] : PolynomialRing k :=
  polynomialVariable k .x

def yPolynomial (k : Type u) [Field k] : PolynomialRing k :=
  polynomialVariable k .y

def zPolynomial (k : Type u) [Field k] : PolynomialRing k :=
  polynomialVariable k .z

/-- `k[x,y,z,y⁻¹]`. -/
abbrev YLocalization (k : Type u) [Field k] :=
  Localization.Away (yPolynomial k)

/-- `k[x,y,z,x⁻¹]`. -/
abbrev XLocalization (k : Type u) [Field k] :=
  Localization.Away (xPolynomial k)

/-- `k[x,y,z,x⁻¹,y⁻¹]`, represented as a localization away from `xy`. -/
abbrev XYLocalization (k : Type u) [Field k] :=
  Localization.Away (xPolynomial k * yPolynomial k)

/-- The canonical maps from the two one-variable localizations into the two-variable one. -/
noncomputable def xLocalizationToXY (k : Type u) [Field k] :
    XLocalization k →+* XYLocalization k :=
  IsLocalization.Away.awayToAwayRight (xPolynomial k) (yPolynomial k)

noncomputable def yLocalizationToXY (k : Type u) [Field k] :
    YLocalization k →+* XYLocalization k :=
  IsLocalization.Away.awayToAwayLeft (yPolynomial k) (xPolynomial k)

/-- The submodule `x k[x,y,z,y⁻¹]` of `k[x,y,z,y⁻¹]`. -/
def xTimesYLocalization (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (YLocalization k) :=
  LinearMap.range
    (LinearMap.lsmul (PolynomialRing k) (YLocalization k) (xPolynomial k))

/-- The submodule `z k[x,y,z,y⁻¹]`. -/
def zTimesYLocalization (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (YLocalization k) :=
  LinearMap.range
    (LinearMap.lsmul (PolynomialRing k) (YLocalization k) (zPolynomial k))

/-- The submodule `yz k[x,y,z]` inside `k[x,y,z,y⁻¹]`. -/
def yzPolynomialSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (YLocalization k) :=
  Submodule.span (PolynomialRing k)
    {algebraMap (PolynomialRing k) (YLocalization k)
      (yPolynomial k * zPolynomial k)}

/-- The image of `y k[x,y,z,x⁻¹]` in the two-variable localization. -/
def yTimesXLocalizationInXY (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (XYLocalization k) :=
  Submodule.span (PolynomialRing k) (Set.range fun a : XLocalization k =>
    algebraMap (PolynomialRing k) (XYLocalization k) (yPolynomial k) *
      xLocalizationToXY k a)

/-- The image of `x k[x,y,z,y⁻¹]` in the two-variable localization. -/
def xTimesYLocalizationInXY (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (XYLocalization k) :=
  Submodule.span (PolynomialRing k) (Set.range fun a : YLocalization k =>
    algebraMap (PolynomialRing k) (XYLocalization k) (xPolynomial k) *
      yLocalizationToXY k a)

/-- The top-middle term of the displayed diagram. -/
abbrev StrangeTopMiddle (k : Type u) [Field k] :=
  XYLocalization k ⧸ yTimesXLocalizationInXY k

/-- The bottom-left term of the displayed diagram. -/
abbrev StrangeBottomLeft (k : Type u) [Field k] :=
  YLocalization k ⧸ yzPolynomialSubmodule k

/-- The common right-hand term of the displayed diagram. -/
def strangeRightDenominator (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (XYLocalization k) :=
  yTimesXLocalizationInXY k ⊔ xTimesYLocalizationInXY k

abbrev StrangeRight (k : Type u) [Field k] :=
  XYLocalization k ⧸ strangeRightDenominator k

/-- The numerator `x k[x,y,z,y⁻¹]`, regarded as a submodule object. -/
abbrev StrangeTopLeftNumerator (k : Type u) [Field k] :=
  xTimesYLocalization k

/-- The denominator `xy k[x,y,z]` inside the numerator of the top-left term. -/
def strangeTopLeftDenominator (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeTopLeftNumerator k) :=
  (Submodule.span (PolynomialRing k)
      {algebraMap (PolynomialRing k) (YLocalization k)
        (xPolynomial k * yPolynomial k)}).comap
    (xTimesYLocalization k).subtype

/-- The top-left term of the displayed diagram. -/
abbrev StrangeTopLeft (k : Type u) [Field k] :=
  StrangeTopLeftNumerator k ⧸ strangeTopLeftDenominator k

/-- The generator of the relation used to form the push-out module `E`.

The signs follow the source's explicit equivalence relation:
`(f,g) ~ (f + xh, g - zh)`, after taking the two quotient modules. -/
def strangeRelationGenerator (k : Type u) [Field k] (h : YLocalization k) :
    StrangeTopMiddle k × StrangeBottomLeft k :=
  ((yTimesXLocalizationInXY k).mkQ
      (algebraMap (PolynomialRing k) (XYLocalization k) (xPolynomial k) *
        yLocalizationToXY k h),
      (yzPolynomialSubmodule k).mkQ
      (-(algebraMap (PolynomialRing k) (YLocalization k) (zPolynomial k) * h)))

/-- The source equivalence relation on the two quotient representatives. -/
def strangePairEquivalent (k : Type u) [Field k]
    (p q : StrangeTopMiddle k × StrangeBottomLeft k) : Prop :=
  ∃ h : YLocalization k, p = q + strangeRelationGenerator k h

/-- The submodule generated by the push-out relations. -/
def strangeRelationSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeTopMiddle k × StrangeBottomLeft k) :=
  Submodule.span (PolynomialRing k) (Set.range (strangeRelationGenerator k))

/-- The module `E` in the source, defined by its explicit pair presentation. -/
def StrangeModule (k : Type u) [Field k] :=
  (StrangeTopMiddle k × StrangeBottomLeft k) ⧸ strangeRelationSubmodule k

instance strangeModule_addCommGroup (k : Type u) [Field k] :
    AddCommGroup (StrangeModule k) := by
  unfold StrangeModule
  infer_instance

instance strangeModule_module (k : Type u) [Field k] :
    Module (PolynomialRing k) (StrangeModule k) := by
  unfold StrangeModule
  infer_instance

/-- The class in `E` of the pair `(f,g)`. -/
def strangePairClass (k : Type u) [Field k] (f : XYLocalization k)
    (g : YLocalization k) : StrangeModule k :=
  (strangeRelationSubmodule k).mkQ
    ((yTimesXLocalizationInXY k).mkQ f, (yzPolynomialSubmodule k).mkQ g)

/-- The distinguished class `e` of `(1,0)`. -/
def strangeE (k : Type u) [Field k] : StrangeModule k :=
  strangePairClass k 1 0

/-- Multiplication by an ideal on the module `E`. -/
def strangeIdealMultiple (k : Type u) [Field k] (I : Ideal (PolynomialRing k)) :
    Submodule (PolynomialRing k) (StrangeModule k) :=
  I • (⊤ : Submodule (PolynomialRing k) (StrangeModule k))

def strangeXSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeModule k) :=
  strangeIdealMultiple k (Ideal.span {xPolynomial k})

def strangeYSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeModule k) :=
  strangeIdealMultiple k (Ideal.span {yPolynomial k})

def strangeZSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeModule k) :=
  strangeIdealMultiple k (Ideal.span {zPolynomial k})

def strangeXYSubmodule (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (StrangeModule k) :=
  strangeIdealMultiple k (Ideal.ofList [xPolynomial k, yPolynomial k])

abbrev StrangeModuleModX (k : Type u) [Field k] :=
  StrangeModule k ⧸ strangeXSubmodule k

abbrev StrangeModuleModXY (k : Type u) [Field k] :=
  StrangeModule k ⧸ strangeXYSubmodule k

abbrev StrangeModuleModZ (k : Type u) [Field k] :=
  StrangeModule k ⧸ strangeZSubmodule k

/-- The quotient displayed in the computation of `E/xE`. -/
def strangeDisplayedModXDenominator (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (YLocalization k) :=
  yzPolynomialSubmodule k ⊔ xTimesYLocalization k ⊔ zTimesYLocalization k

abbrev StrangeDisplayedModX (k : Type u) [Field k] :=
  YLocalization k ⧸ strangeDisplayedModXDenominator k

/-- The simplified quotient in the computation of `E/xE`. -/
def strangeSimplifiedModXDenominator (k : Type u) [Field k] :
    Submodule (PolynomialRing k) (YLocalization k) :=
  xTimesYLocalization k ⊔ zTimesYLocalization k

abbrev StrangeSimplifiedModX (k : Type u) [Field k] :=
  YLocalization k ⧸ strangeSimplifiedModXDenominator k

/-- The low-degree Koszul differential in degree two for two elements. -/
def koszulDifferential₂ {S : Type u} [CommRing S] (x y : S) :
    S →ₗ[S] S × S where
  toFun a := (-y * a, x * a)
  map_add' a b := by
    ext <;> simp [mul_add]
  map_smul' r a := by
    ext <;> simp [mul_comm, mul_left_comm]

/-- The low-degree Koszul differential in degree one for two elements. -/
def koszulDifferential₁ {S : Type u} [CommRing S] (x y : S) :
    (S × S) →ₗ[S] S where
  toFun a := x * a.1 + y * a.2
  map_add' a b := by
    simp [mul_add, add_assoc, add_left_comm]
  map_smul' r a := by
    change x * (r * a.1) + y * (r * a.2) =
      r * (x * a.1 + y * a.2)
    calc
      x * (r * a.1) + y * (r * a.2) =
          (r * x) * a.1 + (r * y) * a.2 := by
            rw [← mul_assoc x r a.1, ← mul_assoc y r a.2,
              mul_comm x r, mul_comm y r]
      _ = r * (x * a.1) + r * (y * a.2) := by
            rw [mul_assoc r x a.1, mul_assoc r y a.2]
      _ = r * (x * a.1 + y * a.2) := by
            rw [mul_add]

/-- The degree-two Koszul homology submodule for a pair. -/
def koszulH₂ {S : Type u} [CommRing S] (x y : S) : Submodule S S :=
  LinearMap.ker (koszulDifferential₂ x y)

/-- A concrete low-degree interface for Koszul-regularity of a pair.

Mathlib's regular-sequence API does not yet provide Koszul complexes.  For a
two-element sequence, the positive-degree condition is exactly injectivity of
the degree-two differential together with exactness at degree one, which is
the interface recorded here. -/
def IsKoszulRegularPair {S : Type u} [CommRing S] (x y : S) : Prop :=
  Function.Injective (koszulDifferential₂ x y) ∧
    Function.Exact (koszulDifferential₂ x y) (koszulDifferential₁ x y)

/-- A common annihilator gives a nonzero degree-two Koszul class. -/
theorem koszulH₂_ne_bot_of_common_annihilator
    {S : Type u} [CommRing S] {x y a : S}
    (ha : a ≠ 0) (hxa : x * a = 0) (hya : y * a = 0) :
    koszulH₂ x y ≠ ⊥ := by
  sorry

/-- The regular-sequence predicate used below, reusing Mathlib's list API. -/
abbrev IsRegularSequence (S : Type u) [CommRing S] (rs : List S) : Prop :=
  RingTheory.Sequence.IsRegular S rs

/-- The four-term diagram in the source, including both short exact rows and
the push-out universal property. -/
def StrangePushoutDiagram (k : Type u) [Field k] : Prop :=
  ∃ (a : StrangeTopLeft k →ₗ[PolynomialRing k] StrangeTopMiddle k)
    (b : StrangeTopMiddle k →ₗ[PolynomialRing k] StrangeRight k)
    (c : StrangeTopLeft k →ₗ[PolynomialRing k] StrangeBottomLeft k)
    (d : StrangeBottomLeft k →ₗ[PolynomialRing k] StrangeRight k)
    (e : StrangeTopMiddle k →ₗ[PolynomialRing k] StrangeModule k)
    (f : StrangeBottomLeft k →ₗ[PolynomialRing k] StrangeModule k)
    (g : StrangeModule k →ₗ[PolynomialRing k] StrangeRight k),
    Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      Function.Injective c ∧ Function.Exact f g ∧
        Function.Surjective g ∧
      e.comp a = f.comp c ∧ g.comp e = b ∧ g.comp f = d ∧
      (∀ {N : Type u} [AddCommGroup N] [Module (PolynomialRing k) N]
        (u : StrangeTopMiddle k →ₗ[PolynomialRing k] N)
        (v : StrangeBottomLeft k →ₗ[PolynomialRing k] N),
        u.comp a = v.comp c →
          ∃! t : StrangeModule k →ₗ[PolynomialRing k] N,
            t.comp e = u ∧ t.comp f = v)

/-- The source diagram has short exact rows and middle term `E` is its push-out. -/
theorem strange_pushout_diagram (k : Type u) [Field k] :
    StrangePushoutDiagram k := by
  sorry

theorem strangeE_not_mem_zE (k : Type u) [Field k] :
    strangeE k ∉ strangeZSubmodule k := by
  sorry

/-- The displayed class `δ` in `E/zE`. -/
def strangeDelta (k : Type u) [Field k] : StrangeModuleModZ k :=
  (strangeZSubmodule k).mkQ (strangeE k)

/-- The class of `e` in `E/zE` is nonzero. -/
theorem strangeDelta_ne_zero (k : Type u) [Field k] :
    strangeDelta k ≠ 0 := by
  sorry

theorem strangeE_y_smul_eq_zero (k : Type u) [Field k] :
    yPolynomial k • strangeE k = 0 := by
  sorry

/-- With the pair relation used above, `(x,0)` is identified with `(0,1)·z`.
This is the sign-corrected form of the corresponding source calculation. -/
theorem strangeE_x_smul_eq_z_smul_one (k : Type u) [Field k] :
    xPolynomial k • strangeE k =
      zPolynomial k • strangePairClass k 0 1 := by
  sorry

theorem strangeDelta_x_smul_eq_zero (k : Type u) [Field k] :
    xPolynomial k • strangeDelta k = 0 := by
  sorry

theorem strangeDelta_y_smul_eq_zero (k : Type u) [Field k] :
    yPolynomial k • strangeDelta k = 0 := by
  sorry

/-- The `x`-quotient calculation in the source. -/
theorem strange_mod_x_linearEquiv_displayed (k : Type u) [Field k] :
    Nonempty (StrangeModuleModX k ≃ₗ[PolynomialRing k] StrangeDisplayedModX k) := by
  sorry

/-- Multiplication by `x` is an isomorphism on the top-middle quotient. -/
theorem strange_x_on_top_middle_bijective (k : Type u) [Field k] :
    Function.Bijective
      (LinearMap.lsmul (PolynomialRing k) (StrangeTopMiddle k) (xPolynomial k)) := by
  sorry

theorem strange_displayed_mod_x_denominator_eq_simplified (k : Type u) [Field k] :
    strangeDisplayedModXDenominator k = strangeSimplifiedModXDenominator k := by
  sorry

theorem strange_mod_x_linearEquiv_simplified (k : Type u) [Field k] :
    Nonempty (StrangeModuleModX k ≃ₗ[PolynomialRing k] StrangeSimplifiedModX k) := by
  sorry

/-- Multiplication by `y` is an isomorphism on `E/xE`. -/
theorem strange_y_on_mod_x_bijective (k : Type u) [Field k] :
    Function.Bijective
      (LinearMap.lsmul (PolynomialRing k) (StrangeModuleModX k) (yPolynomial k)) := by
  sorry

/-- In particular, `y : E/xE → E/xE` is injective. -/
theorem strange_y_on_mod_x_injective (k : Type u) [Field k] :
    Function.Injective
      (LinearMap.lsmul (PolynomialRing k) (StrangeModuleModX k) (yPolynomial k)) := by
  exact (strange_y_on_mod_x_bijective k).1

/-- The quotient `E/(x,y)E` is zero. -/
theorem strange_mod_xy_subsingleton (k : Type u) [Field k] :
    Subsingleton (StrangeModuleModXY k) := by
  sorry

/-- The four claims about the peculiar module `E`. -/
theorem strange_module_claims (k : Type u) [Field k] :
    Function.Injective
        (LinearMap.lsmul (PolynomialRing k) (StrangeModule k) (xPolynomial k)) ∧
      Function.Injective
        (LinearMap.lsmul (PolynomialRing k) (StrangeModuleModX k) (yPolynomial k)) ∧
      Subsingleton (StrangeModuleModXY k) ∧
      ∃ δ : StrangeModuleModZ k,
        δ ≠ 0 ∧
          xPolynomial k • δ = 0 ∧ yPolynomial k • δ = 0 := by
  sorry

/-- The square-zero ring `k[x,y,z] ⊕ E`. -/
abbrev StrangeSquareZeroRing (k : Type u) [Field k] :=
  TrivSqZeroExt (PolynomialRing k) (StrangeModule k)

instance strangeModuleOppositeModule (k : Type u) [Field k] :
    Module (PolynomialRing k)ᵐᵒᵖ (StrangeModule k) :=
  Module.compHom (StrangeModule k)
    (RingEquiv.toOpposite (PolynomialRing k)).symm.toRingHom

instance strangeModuleIsCentralScalar (k : Type u) [Field k] :
    IsCentralScalar (PolynomialRing k) (StrangeModule k) where
  op_smul_eq_smul _ _ := rfl

/-- The canonical inclusion of the polynomial ring in the square-zero ring. -/
def strangeSquareZeroInclusion (k : Type u) [Field k] :
    PolynomialRing k →+* StrangeSquareZeroRing k :=
  TrivSqZeroExt.inlHom (PolynomialRing k) (StrangeModule k)

/-- The ideal `(x,y,z,E)` in the square-zero extension. -/
def strangeSquareZeroMaximalIdeal (k : Type u) [Field k] :
    Ideal (StrangeSquareZeroRing k) :=
  (Ideal.span {xPolynomial k, yPolynomial k, zPolynomial k}).comap
    (TrivSqZeroExt.fstHom (PolynomialRing k) (PolynomialRing k)
      (StrangeModule k)).toRingHom

instance strangeSquareZeroMaximalIdeal_isMaximal (k : Type u) [Field k] :
    (strangeSquareZeroMaximalIdeal k).IsMaximal := by
  sorry

/-- The local ring obtained by localizing the square-zero extension at its
displayed maximal ideal. -/
def StrangeLocalRing (k : Type u) [Field k] :=
  Localization (strangeSquareZeroMaximalIdeal k).primeCompl

instance strangeLocalRing_commRing (k : Type u) [Field k] :
    CommRing (StrangeLocalRing k) := by
  unfold StrangeLocalRing
  infer_instance

instance strangeLocalRing_algebra (k : Type u) [Field k] :
    Algebra (StrangeSquareZeroRing k) (StrangeLocalRing k) := by
  unfold StrangeLocalRing
  infer_instance

def strangeLocalRingMap (k : Type u) [Field k] :
    StrangeSquareZeroRing k →+* StrangeLocalRing k :=
  algebraMap _ _

instance strangeLocalRing_isLocalRing (k : Type u) [Field k] :
    IsLocalRing (StrangeLocalRing k) := by
  unfold StrangeLocalRing
  infer_instance

def strangeLocalX (k : Type u) [Field k] : StrangeLocalRing k :=
  strangeLocalRingMap k (TrivSqZeroExt.inl (xPolynomial k))

def strangeLocalY (k : Type u) [Field k] : StrangeLocalRing k :=
  strangeLocalRingMap k (TrivSqZeroExt.inl (yPolynomial k))

def strangeLocalZ (k : Type u) [Field k] : StrangeLocalRing k :=
  strangeLocalRingMap k (TrivSqZeroExt.inl (zPolynomial k))

def strangeLocalMaximalIdeal (k : Type u) [Field k] : Ideal (StrangeLocalRing k) :=
  IsLocalRing.maximalIdeal (StrangeLocalRing k)

def strangeLocalZIdeal (k : Type u) [Field k] : Ideal (StrangeLocalRing k) :=
  Ideal.span {strangeLocalZ k}

theorem strange_square_zero_maximal_isPrime (k : Type u) [Field k] :
    (strangeSquareZeroMaximalIdeal k).IsPrime := by
  infer_instance

theorem strange_local_ring_isLocalRing (k : Type u) [Field k] :
    IsLocalRing (StrangeLocalRing k) := by
  exact strangeLocalRing_isLocalRing k

theorem strange_local_regular_sequence (k : Type u) [Field k] :
    IsRegularSequence (StrangeLocalRing k)
      [strangeLocalX k, strangeLocalY k, strangeLocalZ k] := by
  sorry

theorem strange_local_delta_statement (k : Type u) [Field k] :
    ∃ δ : StrangeLocalRing k ⧸ strangeLocalZIdeal k,
      δ ≠ 0 ∧ strangeLocalX k • δ = 0 ∧ strangeLocalY k • δ = 0 := by
  sorry

/-- The local-ring example stated in the first source lemma. -/
def StrangeLocalRegularSequenceStatement (k : Type u) [Field k] : Prop :=
  IsLocalRing (StrangeLocalRing k) ∧
    IsRegularSequence (StrangeLocalRing k)
      [strangeLocalX k, strangeLocalY k, strangeLocalZ k] ∧
    strangeLocalX k ∈ strangeLocalMaximalIdeal k ∧
      strangeLocalY k ∈ strangeLocalMaximalIdeal k ∧
        strangeLocalZ k ∈ strangeLocalMaximalIdeal k ∧
    ∃ δ : StrangeLocalRing k ⧸ strangeLocalZIdeal k,
      δ ≠ 0 ∧ strangeLocalX k • δ = 0 ∧ strangeLocalY k • δ = 0

theorem strange_local_regular_sequence_statement (k : Type u) [Field k] :
    StrangeLocalRegularSequenceStatement k := by
  sorry

/-- The one-variable polynomial ring used for `A = k[z]_(z)`. -/
abbrev BasePolynomialRing (k : Type u) [Field k] := Polynomial k

def basePrimeIdeal (k : Type u) [Field k] : Ideal (BasePolynomialRing k) :=
  Ideal.span {Polynomial.X}

instance basePrimeIdeal_isPrime (k : Type u) [Field k] :
    (basePrimeIdeal k).IsPrime := by
  sorry

/-- `k[z]_(z)`, represented as localization at the complement of `(z)`. -/
abbrev BaseRing (k : Type u) [Field k] :=
  Localization (basePrimeIdeal k).primeCompl

def baseRingMaximalIdeal (k : Type u) [Field k] : Ideal (BaseRing k) :=
  (basePrimeIdeal k).map (algebraMap (BasePolynomialRing k) (BaseRing k))

abbrev baseChangeRing (k : Type u) [Field k] :=
  StrangeLocalRing k

def polynomialToSquareZero (k : Type u) [Field k] :
    BasePolynomialRing k →+* StrangeSquareZeroRing k :=
  Polynomial.eval₂RingHom
    ((strangeSquareZeroInclusion k).comp (algebraMap k (PolynomialRing k)))
    (TrivSqZeroExt.inl (zPolynomial k))

def polynomialToBaseChangeRing (k : Type u) [Field k] :
    BasePolynomialRing k →+* baseChangeRing k :=
  (strangeLocalRingMap k).comp (polynomialToSquareZero k)

theorem base_denominator_maps_to_unit (k : Type u) [Field k]
    (s : (basePrimeIdeal k).primeCompl) :
    IsUnit (polynomialToBaseChangeRing k s) := by
  sorry

/-- The local map `A → B` in the second source lemma. -/
noncomputable def baseChangeMap (k : Type u) [Field k] :
    BaseRing k →+* baseChangeRing k :=
  IsLocalization.lift (M := (basePrimeIdeal k).primeCompl)
    (S := BaseRing k) (P := baseChangeRing k) (g := polynomialToBaseChangeRing k)
    (base_denominator_maps_to_unit k)

def baseChangeX (k : Type u) [Field k] : baseChangeRing k :=
  strangeLocalX k

def baseChangeY (k : Type u) [Field k] : baseChangeRing k :=
  strangeLocalY k

def baseChangeIdealXY (k : Type u) [Field k] : Ideal (baseChangeRing k) :=
  Ideal.span {baseChangeX k, baseChangeY k}

abbrev baseChangeQuotient (k : Type u) [Field k] :=
  baseChangeRing k ⧸ baseChangeIdealXY k

def baseMaximalExtension (k : Type u) [Field k] : Ideal (baseChangeRing k) :=
  (baseRingMaximalIdeal k).map (baseChangeMap k)

abbrev baseChangeFiber (k : Type u) [Field k] :=
  baseChangeRing k ⧸ baseMaximalExtension k

def baseChangeFiberX (k : Type u) [Field k] : baseChangeFiber k :=
  Ideal.Quotient.mk (baseMaximalExtension k) (baseChangeX k)

def baseChangeFiberY (k : Type u) [Field k] : baseChangeFiber k :=
  Ideal.Quotient.mk (baseMaximalExtension k) (baseChangeY k)

/-- Flatness of a module over a ring map, with the module structure induced by
the map. -/
def FlatOver {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Type u) [AddCommGroup M] [Module B M] : Prop :=
  @Module.Flat A M _ _ (Module.compHom M f)

/-- Torsion-freeness of a module over the source ring of a ring map. -/
def TorsionFreeOver {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Type u) [AddCommGroup M] [Module B M] : Prop :=
  @Module.IsTorsionFree A M _ _ (Module.compHom M f)

theorem base_ring_prime_isPrime (k : Type u) [Field k] :
    (basePrimeIdeal k).IsPrime := by
  exact basePrimeIdeal_isPrime k

theorem base_change_map_isLocalHom (k : Type u) [Field k] :
    IsLocalHom (baseChangeMap k) := by
  sorry

theorem base_change_quotient_torsion_free (k : Type u) [Field k] :
    TorsionFreeOver (baseChangeMap k) (baseChangeQuotient k) := by
  sorry

theorem base_change_quotient_flat (k : Type u) [Field k] :
    FlatOver (baseChangeMap k) (baseChangeQuotient k) := by
  sorry

theorem base_change_fiber_common_annihilator (k : Type u) [Field k] :
    ∃ δ : baseChangeFiber k,
      δ ≠ 0 ∧ baseChangeFiberX k * δ = 0 ∧ baseChangeFiberY k * δ = 0 := by
  sorry

theorem base_change_fiber_koszul_h₂_ne_bot (k : Type u) [Field k] :
    koszulH₂ (baseChangeFiberX k) (baseChangeFiberY k) ≠ ⊥ := by
  obtain ⟨δ, hδ, hxδ, hyδ⟩ := base_change_fiber_common_annihilator k
  exact koszulH₂_ne_bot_of_common_annihilator hδ hxδ hyδ

theorem base_change_fiber_not_regular (k : Type u) [Field k] :
    ¬ IsRegularSequence (baseChangeFiber k)
      [baseChangeFiberX k, baseChangeFiberY k] := by
  sorry

theorem base_change_fiber_not_koszul_regular (k : Type u) [Field k] :
    ¬ IsKoszulRegularPair (baseChangeFiberX k) (baseChangeFiberY k) := by
  sorry

/-- The local base-change counterexample stated in the second source lemma. -/
def BaseChangeRegularSequenceStatement (k : Type u) [Field k] : Prop :=
  IsLocalRing (BaseRing k) ∧
    IsLocalRing (baseChangeRing k) ∧
    IsLocalHom (baseChangeMap k) ∧
    IsRegularSequence (baseChangeRing k) [baseChangeX k, baseChangeY k] ∧
    baseChangeX k ∈ strangeLocalMaximalIdeal k ∧
      baseChangeY k ∈ strangeLocalMaximalIdeal k ∧
    FlatOver (baseChangeMap k) (baseChangeQuotient k) ∧
    ¬ IsRegularSequence (baseChangeFiber k)
      [baseChangeFiberX k, baseChangeFiberY k] ∧
    ¬ IsKoszulRegularPair (baseChangeFiberX k) (baseChangeFiberY k)

theorem base_change_regular_sequence_statement (k : Type u) [Field k] :
    BaseChangeRegularSequenceStatement k := by
  sorry

end Formalization.Books.Examples.Unit15
