import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RingHom.Flat
import Formalization.Books.MoreAlgebra.Unit30.KoszulRegularSequences

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

open CategoryTheory
open CategoryTheory.Limits
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

/- The source uses the full Koszul complex from More on Algebra, Chapter 30.
   Its list interface is the established project API; this abbreviation only
   adapts the source's two-element notation to that interface. -/
abbrev koszulH₂ {S : Type u} [CommRing S] (x y : S) :=
  Formalization.Books.MoreAlgebra.Unit30.koszulComplexOnListWithCoefficients
    S S [x, y] |>.homology 2

abbrev IsKoszulRegularPair {S : Type u} [CommRing S] (x y : S) : Prop :=
  Formalization.Books.MoreAlgebra.Unit30.IsKoszulRegular S [x, y]

/-- A common annihilator gives a nonzero degree-two Koszul homology object. -/
theorem koszulH₂_not_isZero_of_common_annihilator
    {S : Type u} [CommRing S] {x y a : S}
    (ha : a ≠ 0) (hxa : x * a = 0) (hya : y * a = 0) :
    ¬ IsZero (koszulH₂ x y) := by
  intro hz
  let K₀ :=
    Formalization.Books.MoreAlgebra.Unit30.koszulComplexOnList S [x, y]
  let K :=
    Formalization.Books.MoreAlgebra.Unit30.koszulComplexOnListWithCoefficients
      S S [x, y]
  have hK : IsZero (K.homology 2) := hz
  have hKexact : K.ExactAt 2 :=
    (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := 2)).2 hK
  have hK₀exact : K₀.ExactAt 2 :=
    hKexact.of_iso (HomologicalComplex.rightUnitor K₀)
  let φ : (Fin 2 → S) →ₗ[S] S :=
    Formalization.Books.MoreAlgebra.Unit29.sequenceLinearMap S 2
      (fun i => [x, y].get i)
  have hK₀d₃ : K₀.d 3 2 = 0 := by
    change ModuleCat.ofHom
      (Formalization.Books.MoreAlgebra.Unit29.koszulDifferential
        S (Fin 2 → S) φ 2) = 0
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext v
    let b := Pi.basisFun S (Fin 2)
    let B := b.exteriorPower 3
    have hEmpty : IsEmpty (Set.powersetCard (Fin 2) 3) := by
      constructor
      intro s
      have hle := Finset.card_le_univ s.1
      have hle' : s.1.card ≤ 2 := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hle
      have hcard' : s.1.card = 3 := Set.powersetCard.card_eq s
      omega
    have hsub : Subsingleton (⋀[S]^3 (Fin 2 → S)) := by
      constructor
      intro p q
      apply B.repr.injective
      ext i
      exact False.elim (hEmpty.false i)
    have hzv : exteriorPower.ιMulti S 3 v = 0 :=
      @Subsingleton.elim (⋀[S]^3 (Fin 2 → S)) hsub _ _
    simp only [LinearMap.compAlternatingMap_apply]
    rw [hzv]
    simp
  let e₀ : Fin 2 → S := ![1, 0]
  let e₁ : Fin 2 → S := ![0, 1]
  let v₂ : Fin 2 → (Fin 2 → S) := ![e₀, e₁]
  let w : K₀.X 2 := a • exteriorPower.ιMulti S 2 v₂
  have hw : K₀.d 2 1 w = 0 := by
    change Formalization.Books.MoreAlgebra.Unit29.koszulDifferential
      S (Fin 2 → S) φ 1 (a • exteriorPower.ιMulti S 2 v₂) = 0
    rw [map_smul,
      Formalization.Books.MoreAlgebra.Unit29.koszulDifferential_apply_ιMulti]
    rw [Fin.sum_univ_two]
    simp [v₂, e₀, e₁, φ,
      Formalization.Books.MoreAlgebra.Unit29.sequenceLinearMap_apply, hxa, hya,
      smul_smul, mul_comm]
  have hsc : (K₀.sc' 3 2 1).Exact :=
    (HomologicalComplex.exactAt_iff' (K := K₀) (i := 3) (j := 2) (k := 1)
      (by simp) (by simp)).1 hK₀exact
  obtain ⟨b, hb⟩ :=
    (ShortComplex.moduleCat_exact_iff (K₀.sc' 3 2 1)).1 hsc w hw
  have hw₀ : w = 0 := by
    change K₀.d 3 2 b = w at hb
    rw [← hb, hK₀d₃]
    rfl
  let b₂ := Pi.basisFun S (Fin 2)
  let e₂ : Fin 2 ↪o Fin 2 := (OrderIso.refl _).toOrderEmbedding
  let s₂ : Set.powersetCard (Fin 2) 2 :=
    Set.powersetCard.ofFinEmbEquiv e₂
  have hv₂ : exteriorPower.ιMulti_family S 2 b₂ s₂ =
      exteriorPower.ιMulti S 2 v₂ := by
    apply congrArg (exteriorPower.ιMulti S 2)
    funext i
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [s₂, e₂, b₂, v₂, e₀, e₁]
  let ω : (Fin 2 → S) [⋀^(Fin 2)]→ₗ[S] S :=
    (exteriorPower.alternatingMapLinearEquiv (R := S) (n := 2)).symm
      (exteriorPower.ιMultiDual S 2 b₂ s₂)
  have hω : ω v₂ = 1 := by
    change exteriorPower.ιMultiDual S 2 b₂ s₂
      (exteriorPower.ιMulti S 2 v₂) = 1
    rw [← hv₂]
    exact exteriorPower.ιMultiDual_apply_diag S 2 b₂ s₂
  have ha0 := congrArg (exteriorPower.alternatingMapLinearEquiv ω) hw₀
  have hAw : (exteriorPower.alternatingMapLinearEquiv ω) w = a := by
    change (exteriorPower.alternatingMapLinearEquiv ω)
      (a • exteriorPower.ιMulti S 2 v₂) = a
    calc
      (exteriorPower.alternatingMapLinearEquiv ω)
          (a • exteriorPower.ιMulti S 2 v₂) =
          a • (exteriorPower.alternatingMapLinearEquiv ω)
            (exteriorPower.ιMulti S 2 v₂) := map_smul _ _ _
      _ = a • ω v₂ := by
        rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      _ = a := by rw [hω]; simp
  apply ha
  exact hAw.symm.trans (ha0.trans (map_zero _))

/-- The regular-sequence predicate used below, reusing Mathlib's list API. -/
abbrev IsRegularSequence (S : Type u) [CommRing S] (rs : List S) : Prop :=
  RingTheory.Sequence.IsRegular S rs

/- The source diagram has named canonical maps, rather than arbitrary maps
   witnessing an existential.  The quotient constructions above determine
   these maps; the remaining well-definedness proofs belong to the proof stage. -/
noncomputable def strangeTopLeftToTopMiddle (k : Type u) [Field k] :
    StrangeTopLeft k →ₗ[PolynomialRing k] StrangeTopMiddle k := by
  let fxy : YLocalization k →ₗ[PolynomialRing k] XYLocalization k :=
    { toFun := yLocalizationToXY k
      map_add' := by intro a b; exact (yLocalizationToXY k).map_add a b
      map_smul' := by
        intro r a
        simp only [Algebra.smul_def, map_mul, yLocalizationToXY,
          IsLocalization.Away.awayToAwayLeft_eq, RingHom.id_apply] }
  let f : StrangeTopLeftNumerator k →ₗ[PolynomialRing k] StrangeTopMiddle k :=
    (yTimesXLocalizationInXY k).mkQ.comp
      (fxy.comp
        (xTimesYLocalization k).subtype)
  exact (strangeTopLeftDenominator k).liftQ f (by
    intro a ha
    change (yTimesXLocalizationInXY k).mkQ
      (yLocalizationToXY k (a : YLocalization k)) = 0
    apply (Submodule.Quotient.mk_eq_zero
      (p := yTimesXLocalizationInXY k)
      (x := yLocalizationToXY k (a : YLocalization k))).2
    change (a : YLocalization k) ∈
      Submodule.span (PolynomialRing k)
        {algebraMap (PolynomialRing k) (YLocalization k)
          (xPolynomial k * yPolynomial k)} at ha
    rcases Submodule.mem_span_singleton.mp ha with ⟨r, hr⟩
    apply Submodule.subset_span
    refine ⟨algebraMap (PolynomialRing k) (XLocalization k)
      (xPolynomial k * r), ?_⟩
    have hmap := congrArg (yLocalizationToXY k) hr
    rw [← hmap]
    simp [Algebra.smul_def, xLocalizationToXY, yLocalizationToXY,
      IsLocalization.Away.awayToAwayLeft_eq,
      IsLocalization.Away.awayToAwayRight_eq, map_mul,
      mul_comm, mul_left_comm])

noncomputable def strangeTopLeftToBottomLeft (k : Type u) [Field k] :
    StrangeTopLeft k →ₗ[PolynomialRing k] StrangeBottomLeft k := by
  let mx : YLocalization k →ₗ[PolynomialRing k] YLocalization k :=
    LinearMap.lsmul (PolynomialRing k) (YLocalization k) (xPolynomial k)
  let mz : YLocalization k →ₗ[PolynomialRing k] YLocalization k :=
    LinearMap.lsmul (PolynomialRing k) (YLocalization k) (zPolynomial k)
  let emx : YLocalization k ≃ₗ[PolynomialRing k] StrangeTopLeftNumerator k :=
    LinearEquiv.ofBijective mx.rangeRestrict (by
      constructor
      · intro a b hab
        have hx : algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) ≠ 0 :=
          IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors
            (S := YLocalization k)
            (powers_le_nonZeroDivisors_of_noZeroDivisors
              (x := yPolynomial k)
              (by simp [yPolynomial, polynomialVariable]))
            (mem_nonZeroDivisors_iff_ne_zero.mpr
              (by simp [xPolynomial, polynomialVariable]))
        have hmul :
            algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) * a =
              algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) * b := by
          have hab' := congrArg (fun q : mx.range => (q : YLocalization k)) hab
          change mx a = mx b at hab'
          simpa only [mx, LinearMap.lsmul_apply, Algebra.smul_def] using
            hab'
        exact mul_left_cancel₀ hx hmul
      · intro a
        rcases a.property with ⟨b, hb⟩
        exact ⟨b, Subtype.ext hb⟩)
  let f : StrangeTopLeftNumerator k →ₗ[PolynomialRing k] YLocalization k :=
    mz.comp emx.symm.toLinearMap
  exact (strangeTopLeftDenominator k).liftQ
    ((yzPolynomialSubmodule k).mkQ.comp f) (by
      intro a ha
      rw [LinearMap.mem_ker]
      change (yzPolynomialSubmodule k).mkQ (mz (emx.symm a)) = 0
      apply (Submodule.Quotient.mk_eq_zero
        (p := yzPolynomialSubmodule k) (x := mz (emx.symm a))).2
      change (a : YLocalization k) ∈
        Submodule.span (PolynomialRing k)
          {algebraMap (PolynomialRing k) (YLocalization k)
            (xPolynomial k * yPolynomial k)} at ha
      rcases Submodule.mem_span_singleton.mp ha with ⟨r, hr⟩
      have hx : algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) ≠ 0 :=
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors
          (S := YLocalization k)
          (powers_le_nonZeroDivisors_of_noZeroDivisors
            (x := yPolynomial k)
            (by simp [yPolynomial, polynomialVariable]))
          (mem_nonZeroDivisors_iff_ne_zero.mpr
            (by simp [xPolynomial, polynomialVariable]))
      have hmx : mx (emx.symm a) = (a : YLocalization k) := by
        have h := congrArg Subtype.val (emx.apply_symm_apply a)
        change mx (emx.symm a) = (a : YLocalization k) at h
        exact h
      have hc : emx.symm a =
          algebraMap (PolynomialRing k) (YLocalization k) (yPolynomial k * r) := by
        apply mul_left_cancel₀ hx
        calc
          algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) *
              emx.symm a = (a : YLocalization k) := by
                simpa [mx, LinearMap.lsmul, Algebra.smul_def] using hmx
          _ = r • algebraMap (PolynomialRing k) (YLocalization k)
                (xPolynomial k * yPolynomial k) := hr.symm
          _ = algebraMap (PolynomialRing k) (YLocalization k) (xPolynomial k) *
                algebraMap (PolynomialRing k) (YLocalization k) (yPolynomial k * r) := by
                simp [Algebra.smul_def, map_mul, mul_comm, mul_left_comm]
      rw [hc]
      have hyz : algebraMap (PolynomialRing k) (YLocalization k)
          (yPolynomial k * zPolynomial k) ∈ yzPolynomialSubmodule k := by
        apply Submodule.subset_span
        rfl
      simpa [mz, LinearMap.lsmul_apply, Algebra.smul_def, map_mul,
        mul_assoc, mul_comm, mul_left_comm] using
        (yzPolynomialSubmodule k).smul_mem r hyz)

noncomputable def strangeTopMiddleToStrangeRight (k : Type u) [Field k] :
    StrangeTopMiddle k →ₗ[PolynomialRing k] StrangeRight k := by
  exact (yTimesXLocalizationInXY k).mapQ (strangeRightDenominator k)
    LinearMap.id le_sup_left

noncomputable def strangeBottomLeftToStrangeRight (k : Type u) [Field k] :
    StrangeBottomLeft k →ₗ[PolynomialRing k] StrangeRight k := by
  let fxy : YLocalization k →ₗ[PolynomialRing k] XYLocalization k :=
    { toFun := yLocalizationToXY k
      map_add' := by intro a b; exact (yLocalizationToXY k).map_add a b
      map_smul' := by
        intro r a
        simp only [Algebra.smul_def, map_mul, yLocalizationToXY,
          IsLocalization.Away.awayToAwayLeft_eq, RingHom.id_apply] }
  let f : YLocalization k →ₗ[PolynomialRing k] StrangeRight k :=
    (strangeRightDenominator k).mkQ.comp fxy
  exact (yzPolynomialSubmodule k).liftQ f (by
    apply (Submodule.span_le).2
    rintro _ ⟨rfl⟩
    change f (algebraMap (PolynomialRing k) (YLocalization k)
      (yPolynomial k * zPolynomial k)) = 0
    change (strangeRightDenominator k).mkQ (fxy
      (algebraMap (PolynomialRing k) (YLocalization k)
        (yPolynomial k * zPolynomial k))) = 0
    apply (Submodule.Quotient.mk_eq_zero
      (p := strangeRightDenominator k) (x := fxy
        (algebraMap (PolynomialRing k) (YLocalization k)
          (yPolynomial k * zPolynomial k)))).2
    apply Submodule.mem_sup_left
    apply Submodule.subset_span
    refine ⟨algebraMap (PolynomialRing k) (XLocalization k)
      (zPolynomial k), ?_⟩
    have hz : xLocalizationToXY k
          (algebraMap (PolynomialRing k) (XLocalization k) (zPolynomial k)) =
        algebraMap (PolynomialRing k) (XYLocalization k) (zPolynomial k) := by
      simp [xLocalizationToXY, IsLocalization.Away.awayToAwayRight_eq]
    change algebraMap (PolynomialRing k) (XYLocalization k) (yPolynomial k) *
        xLocalizationToXY k
          (algebraMap (PolynomialRing k) (XLocalization k) (zPolynomial k)) =
      yLocalizationToXY k
        (algebraMap (PolynomialRing k) (YLocalization k)
          (yPolynomial k * zPolynomial k))
    rw [hz]
    simp [fxy, yLocalizationToXY,
      IsLocalization.Away.awayToAwayLeft_eq,
      IsLocalization.Away.awayToAwayRight_eq, map_mul, mul_comm, mul_left_comm])

noncomputable def strangeTopMiddleToModule (k : Type u) [Field k] :
    StrangeTopMiddle k →ₗ[PolynomialRing k] StrangeModule k := by
  let i : StrangeTopMiddle k →ₗ[PolynomialRing k]
      StrangeTopMiddle k × StrangeBottomLeft k :=
    { toFun := fun a => (a, 0)
      map_add' := by intro a b; simp
      map_smul' := by intro r a; simp }
  exact (strangeRelationSubmodule k).mkQ.comp i

noncomputable def strangeBottomLeftToModule (k : Type u) [Field k] :
    StrangeBottomLeft k →ₗ[PolynomialRing k] StrangeModule k := by
  let i : StrangeBottomLeft k →ₗ[PolynomialRing k]
      StrangeTopMiddle k × StrangeBottomLeft k :=
    { toFun := fun b => (0, b)
      map_add' := by intro a b; simp
      map_smul' := by intro r a; simp }
  exact (strangeRelationSubmodule k).mkQ.comp i

noncomputable def strangeModuleToStrangeRight (k : Type u) [Field k] :
    StrangeModule k →ₗ[PolynomialRing k] StrangeRight k := by
  let f : StrangeTopMiddle k × StrangeBottomLeft k →ₗ[PolynomialRing k]
      StrangeRight k :=
    (strangeTopMiddleToStrangeRight k).comp
        (LinearMap.fst (PolynomialRing k) (StrangeTopMiddle k)
          (StrangeBottomLeft k)) +
      (strangeBottomLeftToStrangeRight k).comp
        (LinearMap.snd (PolynomialRing k) (StrangeTopMiddle k)
          (StrangeBottomLeft k))
  exact (strangeRelationSubmodule k).liftQ f (by sorry)

/-- The four-term diagram in the source, including its two short exact rows
and the push-out universal property. -/
def StrangePushoutDiagram (k : Type u) [Field k] : Prop :=
  Function.Injective (strangeTopLeftToTopMiddle k) ∧
    Function.Exact (strangeTopLeftToTopMiddle k)
      (strangeTopMiddleToStrangeRight k) ∧
    Function.Surjective (strangeTopMiddleToStrangeRight k) ∧
    Function.Injective (strangeBottomLeftToModule k) ∧
    Function.Exact (strangeBottomLeftToModule k)
      (strangeModuleToStrangeRight k) ∧
    Function.Surjective (strangeModuleToStrangeRight k) ∧
    (strangeTopMiddleToModule k).comp (strangeTopLeftToTopMiddle k) =
      (strangeBottomLeftToModule k).comp (strangeTopLeftToBottomLeft k) ∧
    (strangeModuleToStrangeRight k).comp (strangeTopMiddleToModule k) =
      strangeTopMiddleToStrangeRight k ∧
    (strangeModuleToStrangeRight k).comp (strangeBottomLeftToModule k) =
      strangeBottomLeftToStrangeRight k ∧
    (∀ {N : Type u} [AddCommGroup N] [Module (PolynomialRing k) N]
      (u : StrangeTopMiddle k →ₗ[PolynomialRing k] N)
      (v : StrangeBottomLeft k →ₗ[PolynomialRing k] N),
      u.comp (strangeTopLeftToTopMiddle k) =
          v.comp (strangeTopLeftToBottomLeft k) →
        ∃! t : StrangeModule k →ₗ[PolynomialRing k] N,
          t.comp (strangeTopMiddleToModule k) = u ∧
            t.comp (strangeBottomLeftToModule k) = v)

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
This records the consequence of the displayed relation; the source's later
minus sign is inconsistent with that relation. -/
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

instance strangeLocalRing_module (k : Type u) [Field k] :
    Module (StrangeLocalRing k) (StrangeLocalRing k) :=
  (RingHom.id (StrangeLocalRing k)).toModule

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

def baseChangeQuotientMap (k : Type u) [Field k] :
    BaseRing k →+* baseChangeQuotient k :=
  (Ideal.Quotient.mk (baseChangeIdealXY k)).comp (baseChangeMap k)

def baseMaximalExtension (k : Type u) [Field k] : Ideal (baseChangeRing k) :=
  (baseRingMaximalIdeal k).map (baseChangeMap k)

abbrev baseChangeFiber (k : Type u) [Field k] :=
  baseChangeRing k ⧸ baseMaximalExtension k

def baseChangeFiberX (k : Type u) [Field k] : baseChangeFiber k :=
  Ideal.Quotient.mk (baseMaximalExtension k) (baseChangeX k)

def baseChangeFiberY (k : Type u) [Field k] : baseChangeFiber k :=
  Ideal.Quotient.mk (baseMaximalExtension k) (baseChangeY k)

theorem base_ring_prime_isPrime (k : Type u) [Field k] :
    (basePrimeIdeal k).IsPrime := by
  exact basePrimeIdeal_isPrime k

theorem base_change_map_isLocalHom (k : Type u) [Field k] :
    IsLocalHom (baseChangeMap k) := by
  sorry

theorem base_change_quotient_torsion_free (k : Type u) [Field k] :
    letI : Module (BaseRing k) (baseChangeQuotient k) :=
      Module.compHom (baseChangeQuotient k) (baseChangeMap k)
    Module.IsTorsionFree (BaseRing k) (baseChangeQuotient k) := by
  sorry

theorem base_change_quotient_flat (k : Type u) [Field k] :
    RingHom.Flat (baseChangeQuotientMap k) := by
  sorry

theorem base_change_fiber_common_annihilator (k : Type u) [Field k] :
    ∃ δ : baseChangeFiber k,
      δ ≠ 0 ∧ baseChangeFiberX k * δ = 0 ∧ baseChangeFiberY k * δ = 0 := by
  sorry

theorem base_change_fiber_koszul_h₂_not_isZero (k : Type u) [Field k] :
    ¬ IsZero (koszulH₂ (baseChangeFiberX k) (baseChangeFiberY k)) := by
  obtain ⟨δ, hδ, hxδ, hyδ⟩ := base_change_fiber_common_annihilator k
  exact koszulH₂_not_isZero_of_common_annihilator hδ hxδ hyδ

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
    IsRegularSequence (baseChangeRing k)
      [baseChangeX k, baseChangeY k] ∧
    baseChangeX k ∈ strangeLocalMaximalIdeal k ∧
      baseChangeY k ∈ strangeLocalMaximalIdeal k ∧
    RingHom.Flat (baseChangeQuotientMap k) ∧
    ¬ IsRegularSequence (baseChangeFiber k)
      [baseChangeFiberX k, baseChangeFiberY k] ∧
    ¬ IsKoszulRegularPair (baseChangeFiberX k) (baseChangeFiberY k)

theorem base_change_regular_sequence_statement (k : Type u) [Field k] :
    BaseChangeRegularSequenceStatement k := by
  sorry

end Formalization.Books.Examples.Unit15
