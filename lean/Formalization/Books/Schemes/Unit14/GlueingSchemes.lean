import Formalization.Books.Schemes.Unit03.OpenImmersions
import Formalization.Books.Schemes.Unit09.Schemes
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Schemes, Chapter 14: Glueing schemes

The source chapter's gluing data are represented by Mathlib's canonical
`AlgebraicGeometry.LocallyRingedSpace.GlueData` and `AlgebraicGeometry.Scheme.GlueData`.
Those structures package the open pieces, their intersections, transition maps, pullback
conditions, and cocycle.  The declarations below expose the source-facing glued-space,
mapping-property, scheme, and example interfaces without duplicating Mathlib's constructions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

namespace Formalization.Books.Schemes.Unit14

universe u

abbrev LocallyRingedSpace := Formalization.Books.Schemes.Unit02.LocallyRingedSpace

/-! ## Gluing data and the glued locally ringed space -/

/-- Canonical locally-ringed-space gluing data for the source's collection of pieces. -/
abbrev GlueingData := AlgebraicGeometry.LocallyRingedSpace.GlueData

/-- Canonical scheme gluing data, used when the pieces are schemes. -/
abbrev SchemeGlueingData := AlgebraicGeometry.Scheme.GlueData

/-- The locally ringed space obtained by gluing `D`. -/
abbrev gluedLocallyRingedSpace (D : GlueingData.{u}) : LocallyRingedSpace.{u} :=
  D.toGlueData.glued

/-- The canonical map from the `i`th piece into the glued locally ringed space. -/
abbrev gluedPieceMap (D : GlueingData.{u}) (i : D.J) :
    D.U i ⟶ gluedLocallyRingedSpace D :=
  D.toGlueData.ι i

/-- The intersection cone for two pieces. -/
abbrev gluedIntersectionCone (D : GlueingData.{u}) (i j : D.J) :
    PullbackCone (gluedPieceMap D i) (gluedPieceMap D j) :=
  D.toGlueData.vPullbackCone i j

/-- The pieces glue along the displayed transition maps. -/
theorem gluedPieceMap_glue_condition (D : GlueingData.{u}) (i j : D.J) :
    D.t i j ≫ D.f j i ≫ gluedPieceMap D j = D.f i j ≫ gluedPieceMap D i :=
  D.toGlueData.glue_condition i j

theorem glueingData_diagonal_transition (D : GlueingData.{u}) (i : D.J) :
    D.t i i = 𝟙 _ :=
  D.t_id i

/-- The prescribed intersection really is the pullback of the two chart maps. -/
noncomputable def gluedIntersectionCone_isLimit (D : GlueingData.{u}) (i j : D.J) :
    IsLimit (gluedIntersectionCone D i j) := by
  exact D.vPullbackConeIsLimit i j

/-- The chart maps jointly cover the glued locally ringed space. -/
theorem gluedPieceMap_jointly_surjective (D : GlueingData.{u}) (x : gluedLocallyRingedSpace D) :
    ∃ (i : D.J) (y : D.U i), (gluedPieceMap D i).base y = x := by
  exact D.ι_jointly_surjective x

/-- The image of each chart is an open subspace of the glued locally ringed space. -/
theorem gluedPieceMap_isOpenImmersion (D : GlueingData.{u}) (i : D.J) :
    LocallyRingedSpace.IsOpenImmersion (gluedPieceMap D i) := by
  infer_instance

/-- The open subspace on the image of a chart. -/
abbrev gluedPieceOpenSubspace (D : GlueingData.{u}) (i : D.J) : LocallyRingedSpace.{u} :=
  Formalization.Books.Schemes.Unit03.openSubspaceOfImage (gluedPieceMap D i)

/-- The canonical identification of a chart with its open image. -/
noncomputable def gluedPieceIso (D : GlueingData.{u}) (i : D.J) :
    D.U i ≅ gluedPieceOpenSubspace D i :=
  Formalization.Books.Schemes.Unit03.openImmersion_imageIso (gluedPieceMap D i)

/-! ## The two mapping properties -/

/-- A compatible family of maps out of the pieces. -/
structure GluedMapOut (D : GlueingData.{u}) (Y : LocallyRingedSpace.{u}) where
  map : ∀ i : D.J, D.U i ⟶ Y
  compatible : ∀ i j : D.J,
    D.t i j ≫ D.f j i ≫ map j = D.f i j ≫ map i

/-- Restriction of a map on a locally ringed space to nested open subspaces. -/
noncomputable def openSubspaceMap {X : LocallyRingedSpace.{u}}
    {U V : Opens X} (h : U ≤ V) :
    Formalization.Books.Schemes.Unit03.openSubspace X U ⟶
      Formalization.Books.Schemes.Unit03.openSubspace X V :=
  Formalization.Books.Schemes.Unit03.restrictHom (𝟙 X) U V (by
    intro x hx
    exact h hx)

/-- The compatible family obtained by restricting a map from the glued space. -/
def gluedMapOutOfMorph (D : GlueingData.{u}) {Y : LocallyRingedSpace.{u}}
    (f : gluedLocallyRingedSpace D ⟶ Y) : GluedMapOut D Y where
  map i := gluedPieceMap D i ≫ f
  compatible i j := by
    simpa only [Category.assoc] using congrArg (fun q => q ≫ f)
      (gluedPieceMap_glue_condition D i j)

/-- Maps from the glued space are exactly compatible maps from its pieces. -/
theorem glued_maps_out_equiv_exists (D : GlueingData.{u})
    (Y : LocallyRingedSpace.{u}) :
    Nonempty ((gluedLocallyRingedSpace D ⟶ Y) ≃ GluedMapOut D Y) := by
  sorry

/-- A compatible family of maps into the pieces, with its open cover and overlap lifts. -/
structure GluedMapInto (D : GlueingData.{u}) (Y : LocallyRingedSpace.{u}) where
  V : D.J → Opens Y
  cover : IsOpenCover V
  map : ∀ i : D.J,
    Formalization.Books.Schemes.Unit03.openSubspace Y (V i) ⟶ D.U i
  overlap : ∀ i j : D.J,
    Formalization.Books.Schemes.Unit03.openSubspace Y (V i ⊓ V j) ⟶ D.V (i, j)
  overlap_f : ∀ i j : D.J,
    overlap i j ≫ D.f i j =
      openSubspaceMap (show V i ⊓ V j ≤ V i from inf_le_left) ≫ map i
  overlap_t : ∀ i j : D.J,
    overlap i j ≫ D.t i j ≫ D.f j i =
      openSubspaceMap (show V i ⊓ V j ≤ V j from inf_le_right) ≫ map j

/-- Maps into the glued space are exactly open-cover families of compatible local maps. -/
theorem glued_maps_into_equiv_exists (D : GlueingData.{u})
    (Y : LocallyRingedSpace.{u}) :
    Nonempty ((Y ⟶ gluedLocallyRingedSpace D) ≃ GluedMapInto D Y) := by
  sorry

/-- A chosen out-of-the-gluing mapping equivalence. -/
noncomputable def glued_maps_out_equiv (D : GlueingData.{u})
    (Y : LocallyRingedSpace.{u}) :
    (gluedLocallyRingedSpace D ⟶ Y) ≃ GluedMapOut D Y :=
  Classical.choice (glued_maps_out_equiv_exists D Y)

/-- A chosen into-the-gluing mapping equivalence. -/
noncomputable def glued_maps_into_equiv (D : GlueingData.{u})
    (Y : LocallyRingedSpace.{u}) :
    (Y ⟶ gluedLocallyRingedSpace D) ≃ GluedMapInto D Y :=
  Classical.choice (glued_maps_into_equiv_exists D Y)

/-! ## The scheme gluing lemma -/

/-- A locally ringed space is a scheme when it is locally isomorphic to schemes. -/
abbrev IsSchemeLocallyRingedSpace (X : LocallyRingedSpace.{u}) : Prop :=
  Formalization.Books.Schemes.Unit09.IsSchemeLocallyRingedSpace X

/-- Gluing schemes along open intersections produces a scheme. -/
theorem gluedLocallyRingedSpace_is_scheme (D : GlueingData.{u})
    (hD : ∀ i : D.J, IsSchemeLocallyRingedSpace (D.U i)) :
    IsSchemeLocallyRingedSpace (gluedLocallyRingedSpace D) := by
  sorry

/-! ## The affine-space-with-zero-doubled example -/

/-- The polynomial ring in `n` coordinates over a field. -/
abbrev affineSpaceRing (k : Type u) [Field k] (n : ℕ) := MvPolynomial (Fin n) k

/-- The affine `n`-space. -/
abbrev affineSpace (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (affineSpaceRing k n))

/-- The `i`th coordinate function. -/
def affineSpaceCoordinate (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    affineSpaceRing k n :=
  MvPolynomial.X i

/-- Evaluation at the origin. -/
def affineSpaceOriginEvaluation (k : Type u) [Field k] (n : ℕ) :
    affineSpaceRing k n →+* k :=
  (MvPolynomial.aeval (R := k) (fun _ : Fin n => (0 : k))).toRingHom

/-- The origin of affine `n`-space. -/
def affineSpaceOrigin (k : Type u) [Field k] (n : ℕ) : affineSpace k n :=
  ⟨RingHom.ker (affineSpaceOriginEvaluation k n),
    RingHom.ker_isPrime (affineSpaceOriginEvaluation k n)⟩

/-- The punctured affine space, as the union of the coordinate standard opens. -/
def affineSpacePuncturedOpen (k : Type u) [Field k] (n : ℕ) :
    (affineSpace k n).Opens :=
  ⨆ i : Fin n, PrimeSpectrum.basicOpen (affineSpaceCoordinate k n i)

/-- The punctured affine space as a scheme. -/
abbrev affineSpacePunctured (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  (affineSpacePuncturedOpen k n).toScheme

/-- The common affine overlap used to double the origin. -/
abbrev affineSpaceZeroDoubledOverlap (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  affineSpacePunctured k n

/-- The inclusion of the overlap in either affine chart. -/
abbrev affineSpaceZeroDoubledOverlapInclusion (k : Type u) [Field k] (n : ℕ) :
    affineSpaceZeroDoubledOverlap k n ⟶ affineSpace k n :=
  (affineSpacePuncturedOpen k n).ι

private theorem affineSpaceZeroDoubled_no_three_distinct
    (i j l : ULift.{u} Bool) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  cases i with
  | up i =>
    cases j with
    | up j =>
      cases l with
      | up l => cases i <;> cases j <;> cases l <;> simp_all

/-- The categorical two-chart gluing datum for affine space with its origin doubled. -/
def affineSpaceZeroDoubledGlueDataPrime (k : Type u) [Field k] (n : ℕ) :
    CategoryTheory.GlueData' (Scheme.{u}) := {
    J := ULift.{u} Bool
    U := fun b => affineSpace k n
    V := by
      intro i j h
      exact affineSpaceZeroDoubledOverlap k n
    f := by
      intro i j h
      exact affineSpaceZeroDoubledOverlapInclusion k n
    f_mono := by
      intro i j h
      infer_instance
    f_hasPullback := by
      intro i j l hij hil
      infer_instance
    t := by
      intro i j h
      exact 𝟙 _
    t' := by
      intro i j l hij hil hjl
      exact (affineSpaceZeroDoubled_no_three_distinct i j l hij hil hjl).elim
    t_fac := by
      intro i j l hij hil hjl
      exact (affineSpaceZeroDoubled_no_three_distinct i j l hij hil hjl).elim
    t_inv := by
      intro i j h
      simp
    cocycle := by
      intro i j l hij hil hjl
      exact (affineSpaceZeroDoubled_no_three_distinct i j l hij hil hjl).elim }

theorem affineSpaceZeroDoubledGlueData_f_open (k : Type u) [Field k] (n : ℕ) :
    ∀ i j,
      IsOpenImmersion
        ((CategoryTheory.GlueData.ofGlueData'
          (affineSpaceZeroDoubledGlueDataPrime k n)).f i j) := by
  sorry

/-- The two-chart scheme gluing datum for affine space with its origin doubled. -/
def affineSpaceZeroDoubledGlueData (k : Type u) [Field k] (n : ℕ) :
    SchemeGlueingData.{u} := {
    toGlueData := CategoryTheory.GlueData.ofGlueData'
      (affineSpaceZeroDoubledGlueDataPrime k n)
    f_open := affineSpaceZeroDoubledGlueData_f_open k n }

/-- The affine space with its origin doubled. -/
abbrev affineSpaceZeroDoubled (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  (affineSpaceZeroDoubledGlueData k n).glued

/-- The two affine chart inclusions into the doubled-origin scheme. -/
abbrev affineSpaceZeroDoubledChart (k : Type u) [Field k] (n : ℕ) (b : Bool) :
    affineSpace k n ⟶ affineSpaceZeroDoubled k n :=
  (affineSpaceZeroDoubledGlueData k n).ι (ULift.up b)

theorem affineSpacePuncturedOpen_eq_complement_origin
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    (affineSpacePuncturedOpen k n : Set (affineSpace k n)) =
      ({affineSpaceOrigin k n} : Set (affineSpace k n))ᶜ := by
  sorry

theorem affineSpaceZeroDoubled_chart_isOpenImmersion
    (k : Type u) [Field k] (n : ℕ) (b : Bool) :
    IsOpenImmersion (affineSpaceZeroDoubledChart k n b) := by
  exact Scheme.GlueData.ι_isOpenImmersion
    (affineSpaceZeroDoubledGlueData k n) (ULift.up b)

theorem affineSpaceZeroDoubled_chart_source_is_affine
    (k : Type u) [Field k] (n : ℕ) (b : Bool) :
    IsAffine (affineSpace k n) := by
  sorry

theorem affineSpaceZeroDoubled_origins_ne
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    affineSpaceZeroDoubledChart k n false (affineSpaceOrigin k n) ≠
      affineSpaceZeroDoubledChart k n true (affineSpaceOrigin k n) := by
  sorry

/-- The morphism to affine `n`-space whose two chart restrictions are the identity. -/
theorem affineSpaceZeroDoubled_to_affineSpace_exists
    (k : Type u) [Field k] (n : ℕ) :
    ∃ f : affineSpaceZeroDoubled k n ⟶ affineSpace k n,
      (∀ b : Bool, affineSpaceZeroDoubledChart k n b ≫ f = 𝟙 _) := by
  sorry

noncomputable def affineSpaceZeroDoubled_to_affineSpace
    (k : Type u) [Field k] (n : ℕ) :
    affineSpaceZeroDoubled k n ⟶ affineSpace k n :=
  Classical.choose (affineSpaceZeroDoubled_to_affineSpace_exists k n)

theorem affineSpaceZeroDoubled_to_affineSpace_fac
    (k : Type u) [Field k] (n : ℕ) (b : Bool) :
    affineSpaceZeroDoubledChart k n b ≫
        affineSpaceZeroDoubled_to_affineSpace k n = 𝟙 _ := by
  exact Classical.choose_spec (affineSpaceZeroDoubled_to_affineSpace_exists k n) b

theorem affineSpaceZeroDoubled_origins_have_same_affine_image
    (k : Type u) [Field k] (n : ℕ) :
    (affineSpaceZeroDoubled_to_affineSpace k n).base
        (affineSpaceZeroDoubledChart k n false (affineSpaceOrigin k n)) =
      (affineSpaceZeroDoubled_to_affineSpace k n).base
        (affineSpaceZeroDoubledChart k n true (affineSpaceOrigin k n)) := by
  sorry

theorem affineSpaceZeroDoubled_globalSections
    (k : Type u) [Field k] (n : ℕ) :
    Nonempty (Γ(affineSpaceZeroDoubled k n, ⊤) ≅ CommRingCat.of (affineSpaceRing k n)) := by
  sorry

theorem affineSpaceZeroDoubled_not_affine
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ¬ IsAffine (affineSpaceZeroDoubled k n) := by
  sorry

theorem affineSpaceZeroDoubled_overlap_two_not_affine
    (k : Type u) [Field k] :
    ¬ IsAffine (affineSpaceZeroDoubledOverlap k 2) := by
  sorry

/-- The source's irreducible-closed-subset assertion for the doubled origin. -/
def IsIrreducibleClosedSubsetOfAffineSpaceZeroDoubled
    (k : Type u) [Field k] (n : ℕ)
    (T : Set (affineSpaceZeroDoubled k n)) : Prop :=
  IsClosed T ∧ IsIrreducible T

theorem affineSpaceZeroDoubled_irreducible_closed_subset_origin_membership
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n)
    (T : Set (affineSpaceZeroDoubled k n))
    (hT : IsIrreducibleClosedSubsetOfAffineSpaceZeroDoubled k n T)
    (h₁ : T ≠ {affineSpaceZeroDoubledChart k n false (affineSpaceOrigin k n)})
    (h₂ : T ≠ {affineSpaceZeroDoubledChart k n true (affineSpaceOrigin k n)}) :
    (affineSpaceZeroDoubledChart k n false (affineSpaceOrigin k n) ∈ T ↔
      affineSpaceZeroDoubledChart k n true (affineSpaceOrigin k n) ∈ T) := by
  sorry

theorem affineSpaceZeroDoubled_many_irreducible_closed_subsets
    (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    ∃ T : Set (affineSpaceZeroDoubled k n),
      IsIrreducibleClosedSubsetOfAffineSpaceZeroDoubled k n T ∧
        T ≠ {affineSpaceZeroDoubledChart k n false (affineSpaceOrigin k n)} ∧
        T ≠ {affineSpaceZeroDoubledChart k n true (affineSpaceOrigin k n)} := by
  sorry

/-! ## The projective line example -/

/-- The affine line chart of the projective line. -/
abbrev projectiveLineAffineChart (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The Laurent-polynomial overlap of the two projective-line charts. -/
abbrev projectiveLineOverlap (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial k)))

/-- The standard open `D(x)` in the affine-line chart. -/
abbrev projectiveLineChartOpen (k : Type u) [Field k] :
    (projectiveLineAffineChart k).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)

/-- The standard-open presentation of the Laurent overlap. -/
noncomputable def projectiveLineChartOpenIso (k : Type u) [Field k] :
    (projectiveLineChartOpen k).toScheme ≅ projectiveLineOverlap k :=
  AlgebraicGeometry.basicOpenIsoSpecAway
    (R := CommRingCat.of (Polynomial k)) (Polynomial.X : Polynomial k)

/-- The chart inclusion `D(x) ⟶ Spec(k[x])`, expressed through the overlap iso. -/
noncomputable def projectiveLineAffineChartToOverlap (k : Type u) [Field k] :
    projectiveLineOverlap k ⟶ projectiveLineAffineChart k :=
  (projectiveLineChartOpenIso k).inv ≫ (projectiveLineChartOpen k).ι

theorem projectiveLineAffineChartToOverlap_isOpenImmersion
    (k : Type u) [Field k] :
    IsOpenImmersion (projectiveLineAffineChartToOverlap k) := by
  sorry

theorem projectiveLineAffineChartToOverlap_mono
    (k : Type u) [Field k] :
    Mono (projectiveLineAffineChartToOverlap k) := by
  sorry

/-- The polynomial evaluation map at a scalar. -/
def projectiveLineCoordinateEvaluation (k : Type u) [Field k] (a : k) :
    Polynomial k →+* k :=
  Polynomial.eval₂RingHom (RingHom.id k) a

/-- The point with affine coordinate `a`. -/
def projectiveLineCoordinatePoint (k : Type u) [Field k] (a : k) :
    projectiveLineAffineChart k :=
  ⟨RingHom.ker (projectiveLineCoordinateEvaluation k a),
    RingHom.ker_isPrime (projectiveLineCoordinateEvaluation k a)⟩

/-- The point `0` on the first affine chart. -/
abbrev projectiveLineZero (k : Type u) [Field k] : projectiveLineAffineChart k :=
  projectiveLineCoordinatePoint k 0

/-- The point `∞`, namely the origin of the second affine chart. -/
abbrev projectiveLineInfinityOnChart (k : Type u) [Field k] : projectiveLineAffineChart k :=
  projectiveLineZero k

/-- The polynomial map used to invert the affine coordinate on the overlap. -/
def projectiveLineInversionPolynomialHom (k : Type u) [Field k] :
    Polynomial k →+* Localization.Away (Polynomial.X : Polynomial k) :=
  Polynomial.eval₂RingHom
    (algebraMap k (Localization.Away (Polynomial.X : Polynomial k)))
    (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k))
      (Polynomial.X : Polynomial k))

/-- The Laurent-polynomial involution sending `x` to `x⁻¹`. -/
def projectiveLineInversionRingHom (k : Type u) [Field k] :
    Localization.Away (Polynomial.X : Polynomial k) →+*
      Localization.Away (Polynomial.X : Polynomial k) :=
  Localization.awayLift (projectiveLineInversionPolynomialHom k) Polynomial.X (by
    exact isUnit_iff_exists_inv.mpr ⟨
      algebraMap (Polynomial k)
        (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X, by
        rw [mul_comm]
        simp [projectiveLineInversionPolynomialHom,
          IsLocalization.Away.mul_invSelf]⟩)

/-- The scheme morphism implementing `x ↦ 1/x` on the overlap. -/
def projectiveLineTransition (k : Type u) [Field k] :
    projectiveLineOverlap k ⟶ projectiveLineOverlap k :=
  Spec.map (CommRingCat.ofHom (projectiveLineInversionRingHom k))

/-- The inversion morphism is an involution. -/
theorem projectiveLineTransition_involutive (k : Type u) [Field k] :
    projectiveLineTransition k ≫ projectiveLineTransition k = 𝟙 _ := by
  sorry

private theorem projectiveLine_no_three_distinct
    (i j l : ULift.{u} Bool) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  cases i with
  | up i =>
    cases j with
    | up j =>
      cases l with
      | up l => cases i <;> cases j <;> cases l <;> simp_all

/-- The categorical gluing datum for the two affine charts of `ℙ¹`. -/
def projectiveLineGlueDataPrime (k : Type u) [Field k] :
    CategoryTheory.GlueData' (Scheme.{u}) := {
    J := ULift.{u} Bool
    U := fun _ => projectiveLineAffineChart k
    V := by
      intro i j h
      exact projectiveLineOverlap k
    f := by
      intro i j h
      exact projectiveLineAffineChartToOverlap k
    f_mono := by
      intro i j h
      exact projectiveLineAffineChartToOverlap_mono k
    f_hasPullback := by
      intro i j l hij hil
      infer_instance
    t := by
      intro i j h
      exact projectiveLineTransition k
    t' := by
      intro i j l hij hil hjl
      exact (projectiveLine_no_three_distinct i j l hij hil hjl).elim
    t_fac := by
      intro i j l hij hil hjl
      exact (projectiveLine_no_three_distinct i j l hij hil hjl).elim
    t_inv := by
      intro i j h
      exact projectiveLineTransition_involutive k
    cocycle := by
      intro i j l hij hil hjl
      exact (projectiveLine_no_three_distinct i j l hij hil hjl).elim }

theorem projectiveLineGlueData_f_open (k : Type u) [Field k] :
    ∀ i j,
      IsOpenImmersion
        ((CategoryTheory.GlueData.ofGlueData'
          (projectiveLineGlueDataPrime k)).f i j) := by
  sorry

/-- The scheme gluing datum defining the projective line. -/
def projectiveLineGlueData (k : Type u) [Field k] : SchemeGlueingData.{u} := {
    toGlueData := CategoryTheory.GlueData.ofGlueData'
      (projectiveLineGlueDataPrime k)
    f_open := projectiveLineGlueData_f_open k }

/-- The projective line over `k`. -/
abbrev projectiveLine (k : Type u) [Field k] : Scheme.{u} :=
  (projectiveLineGlueData k).glued

/-- The two affine chart maps into the projective line. -/
abbrev projectiveLineChartMap (k : Type u) [Field k] (b : Bool) :
    projectiveLineAffineChart k ⟶ projectiveLine k :=
  (projectiveLineGlueData k).ι (ULift.up b)

/-- The point `0` on the projective line. -/
def projectiveLineZeroOnGlued (k : Type u) [Field k] : projectiveLine k :=
  projectiveLineChartMap k false (projectiveLineZero k)

/-- The point `∞` on the projective line. -/
def projectiveLineInfinity (k : Type u) [Field k] : projectiveLine k :=
  projectiveLineChartMap k true (projectiveLineInfinityOnChart k)

/-- The point `1`, used to define the affine open in the second part of the example. -/
def projectiveLineOne (k : Type u) [Field k] : projectiveLine k :=
  projectiveLineChartMap k false (projectiveLineCoordinatePoint k 1)

theorem projectiveLine_zero_ne_infinity (k : Type u) [Field k] :
    projectiveLineZeroOnGlued k ≠ projectiveLineInfinity k := by
  sorry

/-- The global sections of the projective line are the constants. -/
theorem projectiveLine_globalSections (k : Type u) [Field k] :
    Nonempty (Γ(projectiveLine k, ⊤) ≅ CommRingCat.of k) := by
  sorry

/-- The projective line is not affine.  This uses the valid point-separation argument,
rather than the source's overstrong claim that it is infinite over every field. -/
theorem projectiveLine_not_affine (k : Type u) [Field k] :
    ¬ IsAffine (projectiveLine k) := by
  sorry

/-! ## The affine open containing `0` and `∞` -/

/-- The first localization used to write `1/(x - 1)`. -/
abbrev projectiveLineFirstAtOneRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X - 1 : Polynomial k)

/-- The second localization used to write `y/(1 - y)`. -/
abbrev projectiveLineSecondAtOneRing (k : Type u) [Field k] :=
  Localization.Away (1 - Polynomial.X : Polynomial k)

/-- The source's two rational expressions for the coordinate on the affine open. -/
def ProjectiveLineAffineOpenSectionFormula (k : Type u) [Field k]
    {U : (projectiveLine k).Opens} (s : Γ(projectiveLine k, U)) : Prop :=
  ∃ (r₁ : Γ(projectiveLine k, U) →+* projectiveLineFirstAtOneRing k)
    (r₂ : Γ(projectiveLine k, U) →+* projectiveLineSecondAtOneRing k),
    r₁ s = IsLocalization.Away.invSelf (S := projectiveLineFirstAtOneRing k)
      (Polynomial.X - 1 : Polynomial k) ∧
    r₂ s = algebraMap (Polynomial k) (projectiveLineSecondAtOneRing k) Polynomial.X *
      IsLocalization.Away.invSelf (S := projectiveLineSecondAtOneRing k)
        (1 - Polynomial.X : Polynomial k)

/-- Data recording the affine open, its coordinate, and the corresponding affine scheme. -/
structure ProjectiveLineAffineOpenData (k : Type u) [Field k] where
  U : (projectiveLine k).Opens
  eq_complement : (U : Set (projectiveLine k)) = ({projectiveLineOne k} : Set _)ᶜ
  contains_zero : projectiveLineZeroOnGlued k ∈ U
  contains_infinity : projectiveLineInfinity k ∈ U
  coordinateSection : Γ(projectiveLine k, U)
  coordinateSection_formula : ProjectiveLineAffineOpenSectionFormula k coordinateSection
  coordinateIso : Γ(projectiveLine k, U) ≅ CommRingCat.of (Polynomial k)
  coordinateIso_section : coordinateIso.hom.hom coordinateSection = Polynomial.X
  schemeIso : U.toScheme ≅ Spec (CommRingCat.of (Polynomial k))

theorem projectiveLine_affineOpen_exists (k : Type u) [Field k] :
    Nonempty (ProjectiveLineAffineOpenData k) := by
  sorry

/-- A chosen affine open obtained by removing the point `1`. -/
noncomputable def projectiveLineAffineOpenData (k : Type u) [Field k] :
    ProjectiveLineAffineOpenData k :=
  Classical.choice (projectiveLine_affineOpen_exists k)

abbrev projectiveLineAffineOpen (k : Type u) [Field k] : (projectiveLine k).Opens :=
  (projectiveLineAffineOpenData k).U

theorem projectiveLineAffineOpen_eq_complement_one (k : Type u) [Field k] :
    (projectiveLineAffineOpen k : Set (projectiveLine k)) =
      ({projectiveLineOne k} : Set _)ᶜ :=
  (projectiveLineAffineOpenData k).eq_complement

theorem projectiveLineAffineOpen_contains_zero (k : Type u) [Field k] :
    projectiveLineZeroOnGlued k ∈ projectiveLineAffineOpen k :=
  (projectiveLineAffineOpenData k).contains_zero

theorem projectiveLineAffineOpen_contains_infinity (k : Type u) [Field k] :
    projectiveLineInfinity k ∈ projectiveLineAffineOpen k :=
  (projectiveLineAffineOpenData k).contains_infinity

abbrev projectiveLineAffineOpenSection (k : Type u) [Field k] :
    Γ(projectiveLine k, projectiveLineAffineOpen k) :=
  (projectiveLineAffineOpenData k).coordinateSection

theorem projectiveLineAffineOpen_section_formula (k : Type u) [Field k] :
    ProjectiveLineAffineOpenSectionFormula k (projectiveLineAffineOpenSection k) :=
  (projectiveLineAffineOpenData k).coordinateSection_formula

noncomputable def projectiveLineAffineOpen_sectionsIso (k : Type u) [Field k] :
    Γ(projectiveLine k, projectiveLineAffineOpen k) ≅ CommRingCat.of (Polynomial k) :=
  (projectiveLineAffineOpenData k).coordinateIso

theorem projectiveLineAffineOpen_section_is_coordinate (k : Type u) [Field k] :
    (projectiveLineAffineOpen_sectionsIso k).hom.hom (projectiveLineAffineOpenSection k) =
      Polynomial.X :=
  (projectiveLineAffineOpenData k).coordinateIso_section

noncomputable def projectiveLineAffineOpen_schemeIso (k : Type u) [Field k] :
    (projectiveLineAffineOpen k).toScheme ≅ Spec (CommRingCat.of (Polynomial k)) :=
  (projectiveLineAffineOpenData k).schemeIso

end Formalization.Books.Schemes.Unit14
