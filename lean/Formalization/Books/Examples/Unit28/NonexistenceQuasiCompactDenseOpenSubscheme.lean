import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.QuasiSeparated

/-!
# Examples, Chapter 28: nonexistence of a quasi-compact dense open subscheme

Mathlib contains the affine-scheme, spectrum, coproduct, and topological
constructions used in the example, but not a category of algebraic spaces.
The `TopCat` model below therefore records the underlying space of an
algebraic space, while the presentation and the geometric properties that are
not available in Mathlib are kept as source-facing propositions.  The ring and
scheme data are concrete; the geometric assertions are theorem interfaces
for the later proof stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Set TopologicalSpace

universe u

namespace Formalization.Books.Examples.Unit28

/-! ## The algebraic-space and open-subscheme interfaces -/

/-- The chapter-local underlying-space model for an algebraic space. -/
abbrev AlgebraicSpace := TopCat.{u}

/-- A topological representability interface for an algebraic space. -/
def IsScheme (X : AlgebraicSpace) : Prop :=
  ∃ S : Scheme, Nonempty (X ≅ (S : TopCat))

/-- The corresponding representability interface for an open subspace. -/
def IsSchemeOpenSubspace (X : AlgebraicSpace) (V : Set X) : Prop :=
  ∃ S : Scheme, Nonempty (TopCat.of V ≅ (S : TopCat))

/-- The topological quasi-compactness predicate used for an algebraic space. -/
def IsQuasiCompactSpace (X : AlgebraicSpace) : Prop :=
  IsCompact (Set.univ : Set X)

/-- Mathlib's canonical quasi-separated-space predicate, exposed here for spaces. -/
def IsQuasiSeparatedAlgebraicSpace (X : AlgebraicSpace) : Prop :=
  QuasiSeparatedSpace X

/-- The topological part of local separatedness available in this interface. -/
def IsLocallySeparatedAlgebraicSpace (X : AlgebraicSpace) : Prop :=
  IsLocallyClosed (Set.diagonal X)

/-- A dense open subspace which is represented by a scheme. -/
def IsDenseOpenSubscheme (X : AlgebraicSpace) (V : Set X) : Prop :=
  IsOpen V ∧ Dense V ∧ IsSchemeOpenSubspace X V

/-- A quasi-compact dense open subspace which is represented by a scheme. -/
def IsQuasiCompactDenseOpenSubscheme (X : AlgebraicSpace) : Prop :=
  ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ Dense V ∧ IsSchemeOpenSubspace X V

/-- The negation of the property in the chapter's main conclusion. -/
def HasNoQuasiCompactDenseOpenSubscheme (X : AlgebraicSpace) : Prop :=
  ¬ IsQuasiCompactDenseOpenSubscheme X

/-- The open subspace obtained as the union of all scheme open subspaces. -/
def schematicLocus (X : AlgebraicSpace) : Set X :=
  {x | ∃ V : Set X, x ∈ V ∧ IsOpen V ∧ IsSchemeOpenSubspace X V}

/-- A source-facing interface for an affine étale map into an algebraic space. -/
structure AffineEtalePointMap (X : AlgebraicSpace) where
  source : Scheme
  map : (source : TopCat) ⟶ X
  isAffine : Prop
  isEtale : Prop

namespace AffineEtalePointMap

/-- Uniform finite-fibre boundedness for the topological point map. -/
def UniversallyBoundedFibers {X : AlgebraicSpace} (f : AffineEtalePointMap X) : Prop :=
  ∃ n : ℕ, ∀ x : X,
    ∃ h : Fintype {y : (f.source : TopCat) // f.map y = x},
      @Fintype.card _ h ≤ n

end AffineEtalePointMap

/-- The bounded-fibre condition called reasonable in the cited earlier result. -/
def IsReasonableAlgebraicSpace (X : AlgebraicSpace) : Prop :=
  ∀ f : AffineEtalePointMap X,
    f.isAffine → f.isEtale → f.UniversallyBoundedFibers

/-- The standard schematic-locus statement for a quasi-compact, quasi-separated space. -/
theorem schematicLocus_is_dense_open_subscheme
    (X : AlgebraicSpace) (hqc : IsQuasiCompactSpace X)
    (hqs : IsQuasiSeparatedAlgebraicSpace X) :
    IsDenseOpenSubscheme X (schematicLocus X) := by
  sorry

/-- The corresponding schematic-locus statement under the earlier reasonable-space
interface. -/
theorem schematicLocus_is_dense_open_subscheme_of_reasonable
    (X : AlgebraicSpace) (hX : IsReasonableAlgebraicSpace X) :
    IsDenseOpenSubscheme X (schematicLocus X) := by
  sorry

/-! ## The affine ring and its distinguished point -/

abbrev CoordinateVariable := Option ℕ

/-- The products generating the ideal `J` in the source ring. -/
def relationGenerators (k : Type u) [Field k] : Set (MvPolynomial CoordinateVariable k) :=
  Set.range (fun i : ℕ ↦ MvPolynomial.X none * MvPolynomial.X (some i)) ∪
    Set.range (fun p : {p : ℕ × ℕ // p.1 ≠ p.2} ↦
      MvPolynomial.X (some p.1.1) * MvPolynomial.X (some p.1.2))

/-- The ideal generated by `xz_i` and by `z_i z_j` for `i ≠ j`. -/
def relationIdeal (k : Type u) [Field k] : Ideal (MvPolynomial CoordinateVariable k) :=
  Ideal.span (relationGenerators k)

/-- The coordinate ring `B = k[x,z₁,z₂,…]/J`. -/
abbrev relationRing (k : Type u) [Field k] :=
  MvPolynomial CoordinateVariable k ⧸ relationIdeal k

/-- The quotient map from the polynomial ring to `B`. -/
def relationRingMk (k : Type u) [Field k] :
    MvPolynomial CoordinateVariable k →+* relationRing k :=
  Ideal.Quotient.mk (relationIdeal k)

/-- The image of `x` in `B`. -/
def xInRelationRing (k : Type u) [Field k] : relationRing k :=
  relationRingMk k (MvPolynomial.X none)

/-- The image of `z_i` in `B`. -/
def zInRelationRing (k : Type u) [Field k] (i : ℕ) : relationRing k :=
  relationRingMk k (MvPolynomial.X (some i))

/-- The affine scheme `U = Spec(B)`. -/
abbrev affineRelationScheme (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of (relationRing k))

/-- The affine line with its origin removed, used for the second component `Γ`. -/
abbrev gammaRing (k : Type u) [Field k] :=
  Localization.Away (Polynomial.X : Polynomial k)

/-- The scheme `Γ ≃ 𝔾ₘ` used in the relation. -/
abbrev gammaScheme (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of (gammaRing k))

/-- The base affine scheme over which the relation is formed. -/
abbrev relationBaseScheme (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of k)

/-- The structure morphism of `U` over `Spec(k)`. -/
noncomputable def relationBaseMap (k : Type u) [Field k] :
    affineRelationScheme k ⟶ relationBaseScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (relationRing k)))

/-- The structure morphism of `Γ` over `Spec(k)`. -/
noncomputable def gammaBaseMap (k : Type u) [Field k] :
    gammaScheme k ⟶ relationBaseScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (gammaRing k)))

/-- The fiber product `U ×ₖ U` appearing in the source. -/
abbrev relationProduct (k : Type u) [Field k] : Scheme :=
  pullback (relationBaseMap k) (relationBaseMap k)

private def gammaCoordinate (k : Type u) [Field k] (sign : Bool) :
    CoordinateVariable → gammaRing k
  | none => if sign then algebraMap (Polynomial k) (gammaRing k) Polynomial.X
      else -algebraMap (Polynomial k) (gammaRing k) Polynomial.X
  | some _ => 0

private def gammaEvaluation (k : Type u) [Field k] (sign : Bool) :
    MvPolynomial CoordinateVariable k →+* gammaRing k :=
  MvPolynomial.eval₂Hom (algebraMap k (gammaRing k)) (gammaCoordinate k sign)

private def gammaEvaluationAlgHom (k : Type u) [Field k] (sign : Bool) :
    MvPolynomial CoordinateVariable k →ₐ[k] gammaRing k :=
  MvPolynomial.eval₂AlgHom k (gammaCoordinate k sign)

private lemma gammaEvaluation_relationGenerator (k : Type u) [Field k] (sign : Bool)
    {r : MvPolynomial CoordinateVariable k} (hr : r ∈ relationGenerators k) :
    gammaEvaluation k sign r = 0 := by
  rcases hr with hr | hr
  · rcases Set.mem_range.mp hr with ⟨i, rfl⟩
    simp [gammaEvaluation, gammaCoordinate]
  · rcases Set.mem_range.mp hr with ⟨p, rfl⟩
    rcases p with ⟨⟨i, j⟩, hij⟩
    simp [gammaEvaluation, gammaCoordinate]

private lemma gammaEvaluation_relationIdeal (k : Type u) [Field k] (sign : Bool)
    (r : MvPolynomial CoordinateVariable k) (hr : r ∈ relationIdeal k) :
    gammaEvaluation k sign r = 0 := by
  have hle : relationIdeal k ≤ RingHom.ker (gammaEvaluation k sign) := by
    refine Ideal.span_le.2 ?_
    intro r hr
    exact (RingHom.mem_ker).2 (gammaEvaluation_relationGenerator k sign hr)
  exact hle hr

/-- Evaluation of `B` on `Γ` with `x` sent to `x` or `-x`, and all `z_i` sent to zero. -/
def gammaRingHom (k : Type u) [Field k] (sign : Bool) :
    relationRing k →ₐ[k] gammaRing k :=
  Ideal.Quotient.liftₐ (relationIdeal k) (gammaEvaluationAlgHom k sign)
    (fun r hr ↦ gammaEvaluation_relationIdeal k sign r hr)

private lemma gammaRingHom_comp_algebraMap (k : Type u) [Field k] (sign : Bool) :
    (gammaRingHom k sign).toRingHom.comp (algebraMap k (relationRing k)) =
      algebraMap k (gammaRing k) := by
  ext r
  exact (gammaRingHom k sign).commutes r

/-- The two maps `Γ ⟶ U` appearing in the graph of `x ↦ -x`. -/
noncomputable def gammaToAffineRelationScheme (k : Type u) [Field k] (sign : Bool) :
    gammaScheme k ⟶ affineRelationScheme k :=
  Spec.map (CommRingCat.ofHom (gammaRingHom k sign))

private lemma gammaToAffineRelationScheme_comp_baseMap (k : Type u) [Field k]
    (sign : Bool) :
    gammaToAffineRelationScheme k sign ≫ relationBaseMap k = gammaBaseMap k := by
  change
    Spec.map (CommRingCat.ofHom (gammaRingHom k sign).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (relationRing k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (gammaRing k)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [gammaRingHom_comp_algebraMap]

private def zeroEvaluation (k : Type u) [Field k] :
    MvPolynomial CoordinateVariable k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ ↦ 0)

private lemma zeroEvaluation_relationGenerator (k : Type u) [Field k]
    {r : MvPolynomial CoordinateVariable k} (hr : r ∈ relationGenerators k) :
    zeroEvaluation k r = 0 := by
  rcases hr with hr | hr
  · rcases Set.mem_range.mp hr with ⟨i, rfl⟩
    simp [zeroEvaluation]
  · rcases Set.mem_range.mp hr with ⟨p, rfl⟩
    rcases p with ⟨⟨i, j⟩, hij⟩
    simp [zeroEvaluation]

private lemma zeroEvaluation_relationIdeal (k : Type u) [Field k]
    (r : MvPolynomial CoordinateVariable k) (hr : r ∈ relationIdeal k) :
    zeroEvaluation k r = 0 := by
  have hle : relationIdeal k ≤ RingHom.ker (zeroEvaluation k) := by
    refine Ideal.span_le.2 ?_
    intro r hr
    exact (RingHom.mem_ker).2 (zeroEvaluation_relationGenerator k hr)
  exact hle hr

/-- The homomorphism sending every coordinate to zero. -/
def zeroRelationRingHom (k : Type u) [Field k] : relationRing k →+* k :=
  Ideal.Quotient.lift (relationIdeal k) (zeroEvaluation k)
    (fun r hr ↦ zeroEvaluation_relationIdeal k r hr)

/-- The closed point of `U` at which all coordinates vanish. -/
def zeroPoint (k : Type u) [Field k] : affineRelationScheme k :=
  ⟨RingHom.ker (zeroRelationRingHom k), RingHom.ker_isPrime _⟩

/-- The chosen point is the common zero of `x` and all `z_i`. -/
theorem zeroPoint_coordinates (k : Type u) [Field k] :
    zeroRelationRingHom k (xInRelationRing k) = 0 ∧
      ∀ i : ℕ, zeroRelationRingHom k (zInRelationRing k i) = 0 := by
  constructor
  · simp [xInRelationRing, relationRingMk, zeroRelationRingHom, zeroEvaluation]
  · intro i
    simp [zInRelationRing, relationRingMk, zeroRelationRingHom, zeroEvaluation]

/-! ## The étale equivalence relation and its quotient -/

/-- The diagonal component `Δ ⟶ U ×ₖ U`. -/
noncomputable def diagonalRelationMap (k : Type u) [Field k] :
    affineRelationScheme k ⟶ relationProduct k :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

/-- The graph of `x ↦ -x`, viewed in `U ×ₖ U`. -/
noncomputable def gammaRelationMap (k : Type u) [Field k] :
    gammaScheme k ⟶ relationProduct k :=
  pullback.lift (gammaToAffineRelationScheme k true) (gammaToAffineRelationScheme k false)
    ((gammaToAffineRelationScheme_comp_baseMap k true).trans
      (gammaToAffineRelationScheme_comp_baseMap k false).symm)

/-- The relation scheme `R = Δ ⊔ Γ`. -/
abbrev relationScheme (k : Type u) [Field k] : Scheme :=
  affineRelationScheme k ⨿ gammaScheme k

/-- The diagonal and graph subsets of the fiber product used by `j`. -/
def relationDiagonalImage (k : Type u) [Field k] : Set (relationProduct k) :=
  Set.range (fun p : affineRelationScheme k ↦ diagonalRelationMap k p)

def relationGammaImage (k : Type u) [Field k] : Set (relationProduct k) :=
  Set.range (fun p : gammaScheme k ↦ gammaRelationMap k p)

/-- The pair `(0, 0)` on the diagonal component. -/
def relationZeroPair (k : Type u) [Field k] : relationProduct k :=
  diagonalRelationMap k (zeroPoint k)

theorem relationZeroPair_mem_diagonalImage (k : Type u) [Field k] :
    relationZeroPair k ∈ relationDiagonalImage k := by
  exact ⟨zeroPoint k, rfl⟩

/-- The graph accumulates at the diagonal origin, the topological reason that `j` is not
an immersion. -/
theorem relationZeroPair_mem_closure_gammaImage (k : Type u) [Field k] :
    relationZeroPair k ∈ closure (relationGammaImage k) := by
  sorry

/-- The relation scheme is quasi-compact, as used for the quotient's separation property. -/
theorem relationScheme_is_quasi_compact (k : Type u) [Field k] :
    IsCompact (Set.univ : Set (relationScheme k)) := by
  sorry

/-- The source map `s : R ⟶ U`. -/
noncomputable def relationSource (k : Type u) [Field k] :
    relationScheme k ⟶ affineRelationScheme k :=
  coprod.desc (𝟙 _) (gammaToAffineRelationScheme k true)

/-- The target map `t : R ⟶ U`. -/
noncomputable def relationTarget (k : Type u) [Field k] :
    relationScheme k ⟶ affineRelationScheme k :=
  coprod.desc (𝟙 _) (gammaToAffineRelationScheme k false)

/-- The relation map `j : R ⟶ U ×ₖ U`. -/
noncomputable def relationMap (k : Type u) [Field k] :
    relationScheme k ⟶ relationProduct k :=
  coprod.desc (diagonalRelationMap k) (gammaRelationMap k)

theorem relationMap_fst (k : Type u) [Field k] :
    relationMap k ≫ pullback.fst (relationBaseMap k) (relationBaseMap k) =
      relationSource k := by
  change
    coprod.desc (diagonalRelationMap k) (gammaRelationMap k) ≫
        pullback.fst (relationBaseMap k) (relationBaseMap k) =
      coprod.desc (𝟙 _) (gammaToAffineRelationScheme k true)
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, diagonalRelationMap,
      pullback.lift_fst, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_desc, gammaRelationMap,
      pullback.lift_fst, coprod.inr_desc]

theorem relationMap_snd (k : Type u) [Field k] :
    relationMap k ≫ pullback.snd (relationBaseMap k) (relationBaseMap k) =
      relationTarget k := by
  change
    coprod.desc (diagonalRelationMap k) (gammaRelationMap k) ≫
        pullback.snd (relationBaseMap k) (relationBaseMap k) =
      coprod.desc (𝟙 _) (gammaToAffineRelationScheme k false)
  apply coprod.hom_ext
  · rw [← Category.assoc, coprod.inl_desc, diagonalRelationMap,
      pullback.lift_snd, coprod.inl_desc]
  · rw [← Category.assoc, coprod.inr_desc, gammaRelationMap,
      pullback.lift_snd, coprod.inr_desc]

theorem relationMap_diagonal (k : Type u) [Field k] :
    coprod.inl ≫ relationMap k = diagonalRelationMap k := by
  change coprod.inl ≫ coprod.desc (diagonalRelationMap k) (gammaRelationMap k) = _
  exact coprod.inl_desc _ _

theorem relationMap_gamma (k : Type u) [Field k] :
    coprod.inr ≫ relationMap k = gammaRelationMap k := by
  change coprod.inr ≫ coprod.desc (diagonalRelationMap k) (gammaRelationMap k) = _
  exact coprod.inr_desc _ _

/-- The point relation induced by the two projections `s` and `t`. -/
def pointRelation (k : Type u) [Field k]
    (p q : affineRelationScheme k) : Prop :=
  ∃ r : relationScheme k, relationSource k r = p ∧ relationTarget k r = q

/-- The source's assertion that `s,t : R ⟶ U` are étale and define an equivalence relation. -/
def IsEtaleEquivalenceRelation (k : Type u) [Field k] : Prop :=
  Equivalence (pointRelation k) ∧ Etale (relationSource k) ∧ Etale (relationTarget k)

theorem pointRelation_is_equivalence (k : Type u) [Field k] :
    Equivalence (pointRelation k) := by
  sorry

theorem relationSource_is_etale (k : Type u) [Field k] :
    Etale (relationSource k) := by
  sorry

theorem relationTarget_is_etale (k : Type u) [Field k] :
    Etale (relationTarget k) := by
  sorry

theorem relation_is_etale_equivalence_relation (k : Type u) [Field k] :
    IsEtaleEquivalenceRelation k := by
  exact ⟨pointRelation_is_equivalence k, relationSource_is_etale k,
    relationTarget_is_etale k⟩

/-- The failure of `j` to be an immersion, expressed by the closure of `Γ` meeting `Δ`
at the origin. -/
theorem relationMap_not_immersion (k : Type u) [Field k] (hchar : (2 : k) ≠ 0) :
    ¬ IsImmersion (relationMap k) := by
  sorry

/-- The setoid of points used to form the underlying quotient space. -/
noncomputable def pointRelationSetoid (k : Type u) [Field k] :
    Setoid (affineRelationScheme k) where
  r := pointRelation k
  iseqv := pointRelation_is_equivalence k

noncomputable instance pointRelationSetoidInstance (k : Type u) [Field k] :
    Setoid (affineRelationScheme k) :=
  pointRelationSetoid k

abbrev quotientCarrier (k : Type u) [Field k] :=
  Quotient (pointRelationSetoid k)

noncomputable instance quotientCarrier.topologicalSpace (k : Type u) [Field k] :
    TopologicalSpace (quotientCarrier k) :=
  TopologicalSpace.coinduced Quotient.mk' inferInstance

/-- The underlying topological space of the quotient algebraic space `X = U/R`. -/
noncomputable def quotientAlgebraicSpace (k : Type u) [Field k] : AlgebraicSpace :=
  TopCat.of (quotientCarrier k)

/-- The quotient map `U ⟶ X` on underlying spaces. -/
noncomputable def quotientMap (k : Type u) [Field k] :
    (affineRelationScheme k : TopCat) ⟶ quotientAlgebraicSpace k :=
  TopCat.ofHom ⟨@Quotient.mk' (affineRelationScheme k) (pointRelationSetoid k),
    @continuous_quotient_mk' (affineRelationScheme k) _ (pointRelationSetoid k)⟩

/-- The image `0_X` of the all-zero point. -/
def quotientZeroPoint (k : Type u) [Field k] : quotientAlgebraicSpace k :=
  quotientMap k (zeroPoint k)

theorem quotient_is_quasi_compact (k : Type u) [Field k] :
    IsQuasiCompactSpace (quotientAlgebraicSpace k) := by
  sorry

theorem quotient_is_quasi_separated (k : Type u) [Field k] :
    IsQuasiSeparatedAlgebraicSpace (quotientAlgebraicSpace k) := by
  sorry

theorem quotient_is_not_a_scheme (k : Type u) [Field k] (hchar : (2 : k) ≠ 0) :
    ¬ IsScheme (quotientAlgebraicSpace k) := by
  sorry

/-! ## The punctured quotient and the nonexistence conclusion -/

/-- The punctured quotient locus `X \\ {0_X}`. -/
def quotientPuncturedLocus (k : Type u) [Field k] : Set (quotientAlgebraicSpace k) :=
  {x | x ≠ quotientZeroPoint k}

/-- The Laurent-polynomial component `k[x²,x⁻²]`, represented by a Laurent polynomial ring. -/
abbrev puncturedLineRing (k : Type u) [Field k] := LaurentPolynomial k

/-- The `z_i`-component ring `k[z₁,z₂,…]/(z_i z_j)_{i ≠ j}`. -/
def puncturedZGenerators (k : Type u) [Field k] : Set (MvPolynomial ℕ k) :=
  Set.range (fun p : {p : ℕ × ℕ // p.1 ≠ p.2} ↦
    MvPolynomial.X p.1.1 * MvPolynomial.X p.1.2)

def puncturedZIdeal (k : Type u) [Field k] : Ideal (MvPolynomial ℕ k) :=
  Ideal.span (puncturedZGenerators k)

abbrev puncturedZRing (k : Type u) [Field k] :=
  MvPolynomial ℕ k ⧸ puncturedZIdeal k

abbrev puncturedZScheme (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of (puncturedZRing k))

private def puncturedZZeroEvaluation (k : Type u) [Field k] :
    MvPolynomial ℕ k →+* k :=
  MvPolynomial.eval₂Hom (RingHom.id k) (fun _ ↦ 0)

private lemma puncturedZZeroEvaluation_mem_ker (k : Type u) [Field k]
    (r : MvPolynomial ℕ k) (hr : r ∈ puncturedZIdeal k) :
    puncturedZZeroEvaluation k r = 0 := by
  have hle : puncturedZIdeal k ≤ RingHom.ker (puncturedZZeroEvaluation k) := by
    refine Ideal.span_le.2 ?_
    intro r hr
    rcases Set.mem_range.mp hr with ⟨p, rfl⟩
    simp [puncturedZZeroEvaluation]
  exact hle hr

def puncturedZZeroRingHom (k : Type u) [Field k] : puncturedZRing k →+* k :=
  Ideal.Quotient.lift (puncturedZIdeal k) (puncturedZZeroEvaluation k)
    (fun r hr ↦ puncturedZZeroEvaluation_mem_ker k r hr)

def puncturedZZeroPoint (k : Type u) [Field k] : puncturedZScheme k :=
  ⟨RingHom.ker (puncturedZZeroRingHom k), RingHom.ker_isPrime _⟩

theorem puncturedZPoint_is_open_complement (k : Type u) [Field k] :
    IsOpen ({p : puncturedZScheme k | p ≠ puncturedZZeroPoint k} : Set (puncturedZScheme k)) := by
  sorry

def puncturedZOpen (k : Type u) [Field k] : (puncturedZScheme k).Opens :=
  ⟨{p | p ≠ puncturedZZeroPoint k}, puncturedZPoint_is_open_complement k⟩

/-- The scheme displayed in the source for the punctured quotient. -/
noncomputable def puncturedQuotientDescription (k : Type u) [Field k] : Scheme :=
  Spec (CommRingCat.of (puncturedLineRing k)) ⨿ (puncturedZOpen k).toScheme

/-- The punctured quotient is the displayed disjoint union, expressed by a topological
isomorphism because the algebraic-space API is not present in Mathlib. -/
theorem quotientPuncturedLocus_is_displayed_scheme
    (k : Type u) [Field k] :
    Nonempty (TopCat.of (quotientPuncturedLocus k) ≅
      (puncturedQuotientDescription k : TopCat)) := by
  sorry

/-- The displayed scheme has no quasi-compact dense open. -/
def HasNoQuasiCompactDenseOpen (X : TopCat) : Prop :=
  ¬ ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ Dense V

theorem puncturedQuotientDescription_has_no_quasi_compact_dense_open
    (k : Type u) [Field k] :
    HasNoQuasiCompactDenseOpen (puncturedQuotientDescription k : TopCat) := by
  sorry

theorem quotient_has_no_quasi_compact_dense_open_subscheme
    (k : Type u) [Field k] :
    HasNoQuasiCompactDenseOpenSubscheme (quotientAlgebraicSpace k) := by
  sorry

/-- Main existence lemma of the source section. -/
theorem exists_quasi_compact_quasi_separated_algebraic_space_without_dense_open
    (k : Type u) [Field k] (_hchar : (2 : k) ≠ 0) :
    ∃ X : AlgebraicSpace.{u},
      IsQuasiCompactSpace X ∧
      IsQuasiSeparatedAlgebraicSpace X ∧
      HasNoQuasiCompactDenseOpenSubscheme X := by
  refine ⟨quotientAlgebraicSpace k, quotient_is_quasi_compact k,
    quotient_is_quasi_separated k, ?_⟩
  exact quotient_has_no_quasi_compact_dense_open_subscheme k

/-- The strengthened final assertion from the source, using the chapter-local
topological local-separation interface. -/
theorem exists_quasi_compact_quasi_separated_locally_separated_algebraic_space_without_dense_open :
    ∃ X : AlgebraicSpace,
      IsQuasiCompactSpace X ∧
      IsQuasiSeparatedAlgebraicSpace X ∧
      IsLocallySeparatedAlgebraicSpace X ∧
      HasNoQuasiCompactDenseOpenSubscheme X := by
  sorry

end Formalization.Books.Examples.Unit28
