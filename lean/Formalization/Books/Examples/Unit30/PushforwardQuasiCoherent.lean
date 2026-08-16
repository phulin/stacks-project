import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Pi

/-!
# Examples, Chapter 30: Pushforward of quasi-coherent modules

This file formalizes the two counterexamples in the chapter. The constructions use
Mathlib's canonical pushforward, gluing, basic-open, and localization APIs; the
counterexample assertions themselves are theorem interfaces for the prove stage.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace Formalization.Books.Examples.Unit30

/-! ### A countable coproduct over an affine scheme -/

/-- The affine target `Y = Spec(R)` in the first example. -/
abbrev firstTarget (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)

/-- The countable coproduct `X = ⨿ₙ Spec(R)`. -/
noncomputable def firstSource (R : Type u) [CommRing R] : Scheme.{u} :=
  ∐ fun _ : ℕ => firstTarget R

/-- The evident map from the countable coproduct to the affine target. -/
noncomputable def firstMap (R : Type u) [CommRing R] :
    firstSource R ⟶ firstTarget R :=
  Sigma.desc fun _ : ℕ => 𝟙 (firstTarget R)

/-- The basic open `D(a)` in the target of the first example. -/
def firstBasicOpen (R : Type u) [CommRing R] (a : R) : (firstTarget R).Opens :=
  PrimeSpectrum.basicOpen (R := CommRingCat.of R) a

/-- The module-theoretic structure sheaf used in the pushforward examples. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The pushforward of the structure sheaf along the first map. -/
abbrev firstPushforward (R : Type u) [CommRing R] : (firstTarget R).Modules :=
  (Scheme.Modules.pushforward (firstMap R)).obj (unitModule (firstSource R))

/-- The product of the localizations `Rₐ` appearing on `D(a)`. -/
abbrev firstProductOfLocalizations (R : Type u) [CommRing R] (a : R) :=
  ∀ _ : ℕ, Localization.Away a

/-- The element `(a,a,a,...)` of the product ring. -/
def firstProductConstant (R : Type u) [CommRing R] (a : R) : ∀ _ : ℕ, R :=
  fun _ => a

/-- The canonical map from the localization of a product to the product of localizations.

This is the map whose failure to be surjective is used in the first example. -/
noncomputable def firstLocalizationComparison (R : Type u) [CommRing R] (a : R) :
    Localization.Away (firstProductConstant R a) →+*
      firstProductOfLocalizations R a :=
  IsLocalization.lift
    (M := Submonoid.powers (firstProductConstant R a))
    (g := RingHom.pi fun n : ℕ =>
      (algebraMap R (Localization.Away a)).comp (Pi.evalRingHom (fun _ : ℕ => R) n))
    (by
      intro y
      obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff y.1 (firstProductConstant R a)).mp y.2
      rw [Pi.isUnit_iff]
      intro n
      change IsUnit ((algebraMap R (Localization.Away a)) (y.1 n))
      simpa using
        (IsLocalization.map_units (Localization.Away a)
          (⟨y.1 n, (Submonoid.mem_powers_iff (y.1 n) a).mpr ⟨m, by
            simpa [firstProductConstant] using congr_fun hm n⟩⟩ :
            Submonoid.powers a)) )

/-- The product of sections on the basic open in the first example. -/
theorem first_pushforward_sections_formula (R : Type u) [CommRing R] (a : R) :
    Nonempty
      (Γ((firstPushforward R), firstBasicOpen R a) ≃+
        firstProductOfLocalizations R a) := by
  sorry

/-- The sequence `(1,1/2,1/4,...)` in `∏ₙ ℤ[1/2]`. -/
def firstZObstruction (n : ℕ) : Localization.Away (2 : ℤ) :=
  Localization.mk 1 ⟨(2 : ℤ) ^ n, n, rfl⟩

/-- The displayed sequence is not induced by one element of the localization of the product. -/
theorem first_z_obstruction_not_in_comparison_range :
    (fun n : ℕ => firstZObstruction n) ∉
      Set.range (firstLocalizationComparison ℤ (2 : ℤ)) := by
  sorry

/-- The first example is not quasi-coherent for the explicit choice `R = ℤ`. -/
theorem first_pushforward_Z_not_quasicoherent :
    ¬ (firstPushforward ℤ).IsQuasicoherent := by
  sorry

/-- The coproduct map in the explicit first example is separated. -/
theorem first_map_Z_is_separated : IsSeparated (firstMap ℤ) := by
  sorry

/-- The coproduct map in the explicit first example is not quasi-compact. -/
theorem first_map_Z_not_quasiCompact : ¬ QuasiCompact (firstMap ℤ) := by
  sorry

/-! ### Two affine charts glued along a non-quasi-compact open -/

/-- The polynomial ring in `t`, `z`, and the countable family `xₙ`. -/
abbrev secondPolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2 ⊕ ℕ) k

/-- The variables `t`, `z`, and `xₙ`. -/
def secondTPolynomial (k : Type u) [CommRing k] : secondPolynomialRing k :=
  MvPolynomial.X (Sum.inl 0)

def secondZPolynomial (k : Type u) [CommRing k] : secondPolynomialRing k :=
  MvPolynomial.X (Sum.inl 1)

def secondXPolynomial (k : Type u) [CommRing k] (n : ℕ) : secondPolynomialRing k :=
  MvPolynomial.X (Sum.inr n)

/-- The relation `tⁿ xₙⁿ z`, with `n = 1,2,...` represented by `n+1`. -/
def secondRelation (k : Type u) [CommRing k] (n : ℕ) : secondPolynomialRing k :=
  secondTPolynomial k ^ (n + 1) * secondXPolynomial k n ^ (n + 1) * secondZPolynomial k

/-- The ideal generated by all the displayed relations. -/
def secondRelationsIdeal (k : Type u) [CommRing k] :
    Ideal (secondPolynomialRing k) :=
  Ideal.span (Set.range (secondRelation k))

/-- The quotient ring `k[t,z,x₁,x₂,…]/(tx₁z,t²x₂²z,t³x₃³z,…)`. -/
abbrev secondRing (k : Type u) [CommRing k] :=
  secondPolynomialRing k ⧸ secondRelationsIdeal k

/-- The class of a polynomial variable in the quotient ring. -/
def secondVariable (k : Type u) [CommRing k] (v : Fin 2 ⊕ ℕ) : secondRing k :=
  Ideal.Quotient.mk (secondRelationsIdeal k) (MvPolynomial.X v)

def secondT (k : Type u) [CommRing k] : secondRing k :=
  secondVariable k (Sum.inl 0)

def secondZ (k : Type u) [CommRing k] : secondRing k :=
  secondVariable k (Sum.inl 1)

def secondX (k : Type u) [CommRing k] (n : ℕ) : secondRing k :=
  secondVariable k (Sum.inr n)

/-- The affine scheme `Y = Spec(A)` in the second example. -/
abbrev secondTarget (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (CommRingCat.of (secondRing k))

/-- The open `V = ⋃ₙ D(xₙ) ⊆ Y`. -/
def secondOpenV (k : Type u) [CommRing k] : (secondTarget k).Opens :=
  ⨆ n : ℕ,
    PrimeSpectrum.basicOpen (R := CommRingCat.of (secondRing k)) (secondX k n)

/-- The inclusion `j : V ↪ Y`. -/
def secondOpenEmbedding (k : Type u) [CommRing k] :
    (secondOpenV k).toScheme ⟶ secondTarget k :=
  (secondOpenV k).ι

/-- The basic open `D(t) ⊆ Y`. -/
def secondBasicOpenT (k : Type u) [CommRing k] : (secondTarget k).Opens :=
  PrimeSpectrum.basicOpen (R := CommRingCat.of (secondRing k)) (secondT k)

private noncomputable def secondPbIdOpenToOpenId {Y V : Scheme.{u}} (j : V ⟶ Y) :
    pullback (𝟙 Y) j ⟶ pullback j (𝟙 Y) :=
  (pullbackSymmetry (𝟙 Y) j).hom

private noncomputable def secondPbOpenIdToOpenOpen {Y V : Scheme.{u}} (j : V ⟶ Y) :
    pullback j (𝟙 Y) ⟶ pullback j j :=
  pullback.lift (pullback.fst j (𝟙 Y)) (pullback.fst j (𝟙 Y)) (by simp)

private noncomputable def secondPbOpenOpenToIdOpen {Y V : Scheme.{u}} (j : V ⟶ Y) :
    pullback j j ⟶ pullback (𝟙 Y) j :=
  pullback.lift (pullback.fst j j ≫ j) (pullback.fst j j) (by simp)

@[reassoc (attr := simp)]
private lemma secondPbIdOpenToOpenId_snd {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbIdOpenToOpenId j ≫ pullback.snd j (𝟙 Y) = pullback.fst (𝟙 Y) j := by
  exact pullbackSymmetry_hom_comp_snd (𝟙 Y) j

@[reassoc (attr := simp)]
private lemma secondPbIdOpenToOpenId_fst {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbIdOpenToOpenId j ≫ pullback.fst j (𝟙 Y) = pullback.snd (𝟙 Y) j := by
  exact pullbackSymmetry_hom_comp_fst (𝟙 Y) j

@[reassoc (attr := simp)]
private lemma secondPbOpenIdToOpenOpen_snd {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbOpenIdToOpenOpen j ≫ pullback.snd j j = pullback.fst j (𝟙 Y) := by
  dsimp [secondPbOpenIdToOpenOpen]
  apply pullback.lift_snd

@[reassoc (attr := simp)]
private lemma secondPbOpenIdToOpenOpen_fst {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbOpenIdToOpenOpen j ≫ pullback.fst j j = pullback.fst j (𝟙 Y) := by
  dsimp [secondPbOpenIdToOpenOpen]
  apply pullback.lift_fst

@[reassoc (attr := simp)]
private lemma secondPbOpenOpenToIdOpen_fst {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbOpenOpenToIdOpen j ≫ pullback.fst (𝟙 Y) j = pullback.fst j j ≫ j := by
  dsimp [secondPbOpenOpenToIdOpen]
  apply pullback.lift_fst

@[reassoc (attr := simp)]
private lemma secondPbOpenOpenToIdOpen_snd {Y V : Scheme.{u}} (j : V ⟶ Y) :
    secondPbOpenOpenToIdOpen j ≫ pullback.snd (𝟙 Y) j = pullback.fst j j := by
  dsimp [secondPbOpenOpenToIdOpen]
  apply pullback.lift_snd

private lemma secondPullbackIdId_fst_eq_snd (Y : Scheme.{u}) :
    pullback.fst (𝟙 Y) (𝟙 Y) = pullback.snd (𝟙 Y) (𝟙 Y) := by
  exact fst_eq_snd_of_mono_eq _

def secondGlueV (k : Type u) [CommRing k] : Bool × Bool → Scheme.{u}
  | (false, false) => secondTarget k
  | (false, true) => (secondOpenV k).toScheme
  | (true, false) => (secondOpenV k).toScheme
  | (true, true) => secondTarget k

def secondGlueF (k : Type u) [CommRing k] (i j : Bool) :
    secondGlueV k (i, j) ⟶ secondTarget k := by
  cases i <;> cases j
  · exact 𝟙 _
  · exact secondOpenEmbedding k
  · exact secondOpenEmbedding k
  · exact 𝟙 _

def secondGlueT (k : Type u) [CommRing k] (i j : Bool) :
    secondGlueV k (i, j) ⟶ secondGlueV k (j, i) := by
  cases i <;> cases j <;> exact 𝟙 _

noncomputable def secondGlueTPrime (k : Type u) [CommRing k] (i j l : Bool) :
    pullback (secondGlueF k i j) (secondGlueF k i l) ⟶
      pullback (secondGlueF k j l) (secondGlueF k j i) := by
  cases i <;> cases j <;> cases l
  · exact 𝟙 _
  · exact secondPbIdOpenToOpenId (secondOpenEmbedding k)
  · exact secondPbOpenIdToOpenOpen (secondOpenEmbedding k)
  · exact secondPbOpenOpenToIdOpen (secondOpenEmbedding k)
  · exact secondPbOpenOpenToIdOpen (secondOpenEmbedding k)
  · exact secondPbOpenIdToOpenOpen (secondOpenEmbedding k)
  · exact secondPbIdOpenToOpenId (secondOpenEmbedding k)
  · exact 𝟙 _

/-!
The scheme gluing API uses the same universe for its index type and for the schemes being
glued. `ULift` records the two-element index in that universe. -/

abbrev secondIndex : Type u := ULift.{u} Bool

def secondGlueV' (k : Type u) [CommRing k] : secondIndex × secondIndex → Scheme.{u} :=
  fun p => secondGlueV k (p.1.down, p.2.down)

def secondGlueF' (k : Type u) [CommRing k] (i j : secondIndex) :
    secondGlueV' k (i, j) ⟶ secondTarget k :=
  secondGlueF k i.down j.down

def secondGlueT' (k : Type u) [CommRing k] (i j : secondIndex) :
    secondGlueV' k (i, j) ⟶ secondGlueV' k (j, i) :=
  secondGlueT k i.down j.down

noncomputable def secondGlueTPrime' (k : Type u) [CommRing k]
    (i j l : secondIndex) :
    pullback (secondGlueF' k i j) (secondGlueF' k i l) ⟶
      pullback (secondGlueF' k j l) (secondGlueF' k j i) :=
  secondGlueTPrime k i.down j.down l.down

set_option backward.isDefEq.respectTransparency.types false in
/-- Glue data for two copies of `Y`, identifying their common open `V`. -/
noncomputable def secondGlueData (k : Type u) [CommRing k] : Scheme.GlueData.{u} where
  J := secondIndex
  U := fun _ => secondTarget k
  V := secondGlueV' k
  f := secondGlueF' k
  f_mono := by
    rintro ⟨i⟩ ⟨j⟩
    cases i <;> cases j <;>
      dsimp [secondGlueF', secondGlueV', secondGlueF, secondGlueV,
        secondOpenEmbedding] <;> infer_instance
  f_id := by
    rintro ⟨i⟩
    cases i <;>
      dsimp [secondGlueF', secondGlueV', secondGlueF, secondGlueV,
        secondOpenEmbedding] <;> infer_instance
  f_hasPullback := by
    rintro ⟨i⟩ ⟨j⟩ ⟨l⟩
    infer_instance
  t := secondGlueT' k
  t_id := by
    rintro ⟨i⟩
    cases i <;> rfl
  t' := secondGlueTPrime' k
  t_fac := by
    rintro ⟨i⟩ ⟨j⟩ ⟨l⟩
    cases i <;> cases j <;> cases l
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [Category.id_comp, Category.comp_id, secondPullbackIdId_fst_eq_snd]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbIdOpenToOpenId_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbOpenIdToOpenOpen_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbOpenOpenToIdOpen_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbOpenOpenToIdOpen_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbOpenIdToOpenOpen_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [secondPbIdOpenToOpenId_snd, Category.comp_id]
    · dsimp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueT', secondGlueT, secondGlueV', secondGlueV]
      rw [Category.id_comp, Category.comp_id, secondPullbackIdId_fst_eq_snd]
  cocycle := by
    rintro ⟨i⟩ ⟨j⟩ ⟨l⟩
    cases i <;> cases j <;> cases l <;>
      apply pullback.hom_ext <;>
      simp [secondGlueTPrime', secondGlueTPrime, secondGlueF', secondGlueF,
        secondGlueV', secondGlueV, secondOpenEmbedding, pullback.condition,
        fst_eq_snd_of_mono_eq,
        secondPbIdOpenToOpenId_fst, secondPbIdOpenToOpenId_snd,
        secondPbOpenIdToOpenOpen_snd,
        secondPbOpenIdToOpenOpen_snd, secondPbOpenOpenToIdOpen_fst,
        secondPbOpenOpenToIdOpen_snd, Category.assoc]
  f_open := by
    rintro ⟨i⟩ ⟨j⟩
    cases i <;> cases j <;>
      dsimp [secondGlueF', secondGlueV', secondGlueF, secondGlueV,
        secondOpenEmbedding] <;> infer_instance

/-- The glued scheme `X` in the second example. -/
noncomputable def secondSource (k : Type u) [CommRing k] : Scheme.{u} :=
  (secondGlueData k).glued

/-- The two chart maps `Y ⟶ X`. -/
noncomputable def secondChart (k : Type u) [CommRing k] (i : secondIndex) :
    secondTarget k ⟶ secondSource k :=
  (secondGlueData k).ι i

private lemma secondGlueData_diagram_condition (k : Type u) [CommRing k]
    (i j : secondIndex) :
    (secondGlueData k).diagram.fst (i, j) ≫ 𝟙 (secondTarget k) =
      (secondGlueData k).diagram.snd (i, j) ≫ 𝟙 (secondTarget k) := by
  change secondGlueF' k i j ≫ 𝟙 (secondTarget k) =
    secondGlueT' k i j ≫ secondGlueF' k j i ≫ 𝟙 (secondTarget k)
  cases i with
  | up i =>
    cases j with
    | up j =>
      cases i <;> cases j <;>
        simp [secondGlueF', secondGlueF, secondGlueT', secondGlueT,
          secondGlueV', secondGlueV, secondOpenEmbedding]

/-- The evident map from the glued scheme to `Y`. -/
noncomputable def secondMap (k : Type u) [CommRing k] :
    secondSource k ⟶ secondTarget k :=
  Multicoequalizer.desc (secondGlueData k).diagram (secondTarget k)
    (fun _ : secondIndex => 𝟙 (secondTarget k)) (by
      rintro ⟨i, j⟩
      exact secondGlueData_diagram_condition k i j)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem second_chart_comp_map (k : Type u) [CommRing k] (i : secondIndex) :
    secondChart k i ≫ secondMap k = 𝟙 (secondTarget k) := by
  change Multicoequalizer.π (secondGlueData k).diagram i ≫
      Multicoequalizer.desc (secondGlueData k).diagram (secondTarget k)
        (fun _ : secondIndex => 𝟙 (secondTarget k)) _ = 𝟙 (secondTarget k)
  exact Multicoequalizer.π_desc _ _ _ _ _

/-! ### The sheaf maps and exact sequence in the second example -/

abbrev secondStructureSheaf (k : Type u) [CommRing k] : (secondTarget k).Modules :=
  unitModule (secondTarget k)

abbrev secondOpenPushforward (k : Type u) [CommRing k] : (secondTarget k).Modules :=
  (Scheme.Modules.pushforward (secondOpenEmbedding k)).obj
    (unitModule (secondOpenV k).toScheme)

abbrev secondPushforward (k : Type u) [CommRing k] : (secondTarget k).Modules :=
  (Scheme.Modules.pushforward (secondMap k)).obj (unitModule (secondSource k))

/-- The canonical map from the target structure sheaf to the second pushforward. -/
noncomputable def secondUnitPushforwardMap (k : Type u) [CommRing k] :
    secondStructureSheaf k ⟶ secondPushforward k :=
  SheafOfModules.unitToPushforwardObjUnit (secondMap k).toRingCatSheafHom

/-- The canonical localization-to-sections map on `D(t)`, transported through the affine
identification of that basic open with `Spec (Aₜ)`. -/
noncomputable def secondAwayToTargetBasicOpenSections (k : Type u) [CommRing k] :
    Localization.Away (secondT k) →+
      Γ(secondTarget k, secondBasicOpenT k) :=
  ((secondBasicOpenT k).topIso.hom.hom.comp
      ((basicOpenIsoSpecAway (R := CommRingCat.of (secondRing k)) (secondT k)).hom.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (secondT k)))).inv.hom)).toAddMonoidHom

/-- The canonical map `Aₜ → Γ(D(t), f_*𝒪_X)`. -/
noncomputable def secondAwayToPushforwardBasicOpenSections (k : Type u) [CommRing k] :
    Localization.Away (secondT k) →+
      Γ(secondPushforward k, secondBasicOpenT k) :=
  ((secondUnitPushforwardMap k).app (secondBasicOpenT k)).hom.comp
    (secondAwayToTargetBasicOpenSections k)

/-- The canonical map `𝒪_Y ⟶ j_*𝒪_V`. -/
noncomputable def secondOpenUnitMap (k : Type u) [CommRing k] :
    secondStructureSheaf k ⟶ secondOpenPushforward k :=
  SheafOfModules.unitToPushforwardObjUnit
    (secondOpenEmbedding k).toRingCatSheafHom

/-- The restriction of `f_*𝒪_X` to either glued chart. -/
noncomputable def secondChartRestrictionMap (k : Type u) [CommRing k] (i : secondIndex) :
    secondPushforward k ⟶ secondStructureSheaf k :=
  (Scheme.Modules.pushforward (secondMap k)).map
      (SheafOfModules.unitToPushforwardObjUnit
        (secondChart k i).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (secondChart k i) (secondMap k)).hom.app
      (unitModule (secondTarget k)) ≫
    (Scheme.Modules.pushforwardCongr (second_chart_comp_map k i)).hom.app
      (unitModule (secondTarget k)) ≫
    (Scheme.Modules.pushforwardId (secondTarget k)).hom.app
      (unitModule (secondTarget k))

/-- The map `f_*𝒪_X ⟶ 𝒪_Y ⊕ 𝒪_Y` given by the two charts. -/
noncomputable def secondRestrictionPairMap (k : Type u) [CommRing k] :
    secondPushforward k ⟶ secondStructureSheaf k ⊞ secondStructureSheaf k :=
  biprod.lift (secondChartRestrictionMap k ⟨false⟩) (secondChartRestrictionMap k ⟨true⟩)

/-- The two chart restrictions agree after restriction to the gluing open. -/
theorem second_restriction_compatibility (k : Type u) [CommRing k] :
    secondChartRestrictionMap k ⟨false⟩ ≫ secondOpenUnitMap k =
      secondChartRestrictionMap k ⟨true⟩ ≫ secondOpenUnitMap k := by
  sorry

/-- The difference map `𝒪_Y ⊕ 𝒪_Y ⟶ j_*𝒪_V`, written `(1,-1)`. -/
noncomputable def secondDifferenceMap (k : Type u) [CommRing k] :
    secondStructureSheaf k ⊞ secondStructureSheaf k ⟶ secondOpenPushforward k :=
  biprod.desc
    (𝟙 (secondStructureSheaf k) ≫ secondOpenUnitMap k)
    (-(𝟙 (secondStructureSheaf k) ≫ secondOpenUnitMap k))

/-- The short complex displayed in the chapter. -/
noncomputable def secondExactComplex (k : Type u) [CommRing k] :
    ShortComplex (secondTarget k).Modules :=
  ShortComplex.mk (secondRestrictionPairMap k) (secondDifferenceMap k) (by
    simp [secondRestrictionPairMap, secondDifferenceMap,
      second_restriction_compatibility])

/-- The displayed sequence `0 → f_*𝒪_X → 𝒪_Y⊕𝒪_Y → j_*𝒪_V` is exact. -/
theorem second_exact_sequence (k : Type u) [Field k] :
    (secondExactComplex k).ShortExact := by
  sorry

/-- The global sections of the second pushforward identify with `A`. -/
theorem second_global_sections_identification (k : Type u) [Field k] :
    Nonempty (Γ(secondPushforward k, ⊤) ≃+ secondRing k) := by
  sorry

/-- The product of the localizations `A_{xₙ}`. -/
abbrev secondLocalizationProduct (k : Type u) [CommRing k] :=
  ∀ n : ℕ, Localization.Away (secondX k n)

/-- The canonical map `A → ∏ₙ A_{xₙ}`. -/
def secondLocalizationProductMap (k : Type u) [CommRing k] :
    secondRing k →+* secondLocalizationProduct k :=
  RingHom.pi fun n : ℕ => algebraMap (secondRing k) (Localization.Away (secondX k n))

/-- The map `A → ∏ₙ A_{xₙ}` is injective in the second example. -/
theorem second_localization_product_map_injective (k : Type u) [Field k] :
    Function.Injective (secondLocalizationProductMap k) := by
  sorry

/-- The localization map `A_t → A_{t xₙ}` induced by `t ↦ t`. -/
noncomputable def secondTToTXLocalization (k : Type u) [CommRing k] (n : ℕ) :
    Localization.Away (secondT k) →+* Localization.Away (secondT k * secondX k n) :=
  IsLocalization.Away.lift (secondT k)
    (IsLocalization.Away.isUnit_of_dvd
      (S := Localization.Away (secondT k * secondX k n))
      (x := secondT k * secondX k n)
      (r := secondT k)
      (dvd_mul_right (secondT k) (secondX k n)))

/-- The map `A_t → ∏ₙ A_{t xₙ}`. -/
def secondTLocalizationProductMap (k : Type u) [CommRing k] :
    Localization.Away (secondT k) →+*
      (∀ n : ℕ, Localization.Away (secondT k * secondX k n)) :=
  RingHom.pi fun n : ℕ => secondTToTXLocalization k n

/-- The image of `z` in `A_t`. -/
def secondLocalizedZ (k : Type u) [CommRing k] : Localization.Away (secondT k) :=
  algebraMap (secondRing k) (Localization.Away (secondT k)) (secondZ k)

/-- The pair `(z, 0)` in the two chart sections over `D(t)`. -/
noncomputable def secondExtraSectionPair (k : Type u) [CommRing k] :
    Γ(secondStructureSheaf k ⊞ secondStructureSheaf k, secondBasicOpenT k) :=
  ((biprod.inl : secondStructureSheaf k ⟶
      secondStructureSheaf k ⊞ secondStructureSheaf k).app (secondBasicOpenT k)).hom
    (secondAwayToTargetBasicOpenSections k (secondLocalizedZ k))

/-- The element `z` is a nonzero kernel witness for `A_t → ∏ₙ A_{t xₙ}`. -/
theorem second_t_localization_kernel_contains_z (k : Type u) [Field k] :
    secondLocalizedZ k ∈ RingHom.ker (secondTLocalizationProductMap k) ∧
      secondLocalizedZ k ≠ 0 := by
  sorry

/-- The section `(z, 0)` is an extra section of the pushforward over `D(t)`. -/
theorem second_basic_open_has_extra_section (k : Type u) [Field k] :
    ∃ s : Γ(secondPushforward k, secondBasicOpenT k),
      s ∉ Set.range (secondAwayToPushforwardBasicOpenSections k) ∧
        ((secondRestrictionPairMap k).app (secondBasicOpenT k)).hom s =
          secondExtraSectionPair k := by
  sorry

/-- The pushforward in the second example is not quasi-coherent. -/
theorem second_pushforward_not_quasicoherent (k : Type u) [Field k] :
    ¬ (secondPushforward k).IsQuasicoherent := by
  sorry

/-- The glued-to-affine map is quasi-compact. -/
theorem second_map_is_quasiCompact (k : Type u) [Field k] :
    QuasiCompact (secondMap k) := by
  sorry

/-- The glued-to-affine map is not quasi-separated. -/
theorem second_map_not_quasiSeparated (k : Type u) [Field k] :
    ¬ QuasiSeparated (secondMap k) := by
  sorry

/-! ### Sharpness of the general implication -/

/-- A source-facing formulation of the sharpness statement in the chapter. -/
theorem pushforward_quasicoherent_requires_quasiseparated_source
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ M : X.Modules, M.IsQuasicoherent →
      ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent) →
      QuasiSeparated f := by
  sorry

end Formalization.Books.Examples.Unit30
