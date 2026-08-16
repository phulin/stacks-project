import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.LocallyClosed

/-!
# Examples, Chapter 25: Images of locally closed subsets

This file formalizes the countably generated affine example showing that the
image of a locally closed subset need not be a finite union of locally closed
subsets.  The polynomial extension is Mathlib's canonical presentation of the
extra variable `t`, and the equations and basic opens are indexed by `ℕ` so
that index `n` denotes the textbook's `(n + 1)`-st `x` or `y`.
-/

noncomputable section

universe u

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

namespace Formalization.«Books.Examples».Unit25

/-! ## The affine projection and its coordinates -/

/-- The two countable families of variables in the target affine scheme. -/
abbrev imageExampleVariable := ℕ ⊕ ℕ

/-- The target ring `k[x₁, x₂, …, y₁, y₂, …]`. -/
abbrev imageExampleTargetRing (k : Type u) [Field k] :=
  MvPolynomial imageExampleVariable k

/-- The source ring, obtained from the target by adjoining the variable `t`. -/
abbrev imageExampleSourceRing (k : Type u) [Field k] :=
  Polynomial (imageExampleTargetRing k)

/-- The affine target scheme `Y`. -/
abbrev imageExampleTargetScheme (k : Type u) [Field k] : Scheme :=
  Spec (.of (imageExampleTargetRing k))

/-- The affine source scheme `X`. -/
abbrev imageExampleSourceScheme (k : Type u) [Field k] : Scheme :=
  Spec (.of (imageExampleSourceRing k))

/-- The target variable `xₙ₊₁`. -/
def imageExampleTargetX (k : Type u) [Field k] (n : ℕ) : imageExampleTargetRing k :=
  MvPolynomial.X (.inl n)

/-- The target variable `yₙ₊₁`. -/
def imageExampleTargetY (k : Type u) [Field k] (n : ℕ) : imageExampleTargetRing k :=
  MvPolynomial.X (.inr n)

/-- The copies of the target variables in the source polynomial ring. -/
def imageExampleSourceX (k : Type u) [Field k] (n : ℕ) : imageExampleSourceRing k :=
  Polynomial.C (imageExampleTargetX k n)

def imageExampleSourceY (k : Type u) [Field k] (n : ℕ) : imageExampleSourceRing k :=
  Polynomial.C (imageExampleTargetY k n)

/-- The polynomial ring map underlying the projection `X ⟶ Y`. -/
def imageExampleProjectionRingHom (k : Type u) [Field k] :
    imageExampleTargetRing k →+* imageExampleSourceRing k :=
  algebraMap (imageExampleTargetRing k) (imageExampleSourceRing k)

/-- The projection morphism `Spec(k[t, x₁, …, y₁, …]) ⟶ Spec(k[x₁, …, y₁, …])`. -/
noncomputable def imageExampleProjection (k : Type u) [Field k] :
    imageExampleSourceScheme k ⟶ imageExampleTargetScheme k :=
  Spec.map (CommRingCat.ofHom (imageExampleProjectionRingHom k))

/-- The projection is locally of finite presentation, by the polynomial extension API. -/
instance imageExampleProjection_locallyOfFinitePresentation
    (k : Type u) [Field k] :
    LocallyOfFinitePresentation (imageExampleProjection k) := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (imageExampleProjectionRingHom k)))
  apply (LocallyOfFinitePresentation.SpecMap_iff _).2
  change (algebraMap (imageExampleTargetRing k) (imageExampleSourceRing k)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

/-- The affine projection is quasi-compact. -/
instance imageExampleProjection_quasiCompact (k : Type u) [Field k] :
    QuasiCompact (imageExampleProjection k) := by
  infer_instance

/-- In Mathlib's property language, the displayed projection is of finite presentation. -/
theorem imageExampleProjection_is_finite_presentation (k : Type u) [Field k] :
    LocallyOfFinitePresentation (imageExampleProjection k) ∧
      QuasiCompact (imageExampleProjection k) :=
  ⟨inferInstance, inferInstance⟩

/-! ## The equations and the locally closed source subset -/

/-- The product `(t - 1) … (t - (n + 1))`. -/
def imageExampleRootProduct (k : Type u) [Field k] (n : ℕ) : imageExampleSourceRing k :=
  (Finset.range (n + 1)).prod (fun i ↦
    (Polynomial.X : imageExampleSourceRing k) -
      Polynomial.C ((i + 1 : ℕ) : imageExampleTargetRing k))

/-- The `(n + 1)`-st displayed equation defining `Z`. -/
def imageExampleEquation (k : Type u) [Field k] (n : ℕ) : imageExampleSourceRing k :=
  imageExampleSourceX k n * imageExampleRootProduct k n

/-- The function whose basic open is `Uₙ₊₁`. -/
def imageExampleOpenFunction (k : Type u) [Field k] (n : ℕ) : imageExampleSourceRing k :=
  imageExampleSourceY k n * imageExampleRootProduct k n

/-- The closed subset `Z` cut out by all the displayed equations. -/
def imageExampleZ (k : Type u) [Field k] : Set (imageExampleSourceScheme k) :=
  PrimeSpectrum.zeroLocus (Set.range (imageExampleEquation k))

/-- The basic open `Uₙ₊₁`, where `yₙ₊₁(t - 1)…(t - (n + 1))` is nonzero. -/
def imageExampleUj (k : Type u) [Field k] (n : ℕ) : Set (imageExampleSourceScheme k) :=
  (PrimeSpectrum.basicOpen (imageExampleOpenFunction k n) :
    Set (PrimeSpectrum (imageExampleSourceRing k)))

/-- The open subset `U = ⋃ₙ Uₙ₊₁`. -/
def imageExampleU (k : Type u) [Field k] : Set (imageExampleSourceScheme k) :=
  ⋃ n : ℕ, imageExampleUj k n

/-- The locally closed subset `T = Z ∩ U` whose image is studied. -/
def imageExampleT (k : Type u) [Field k] : Set (imageExampleSourceScheme k) :=
  imageExampleZ k ∩ imageExampleU k

theorem imageExampleZ_isClosed (k : Type u) [Field k] :
    IsClosed (imageExampleZ k) := by
  exact PrimeSpectrum.isClosed_zeroLocus _

theorem imageExampleUj_isOpen (k : Type u) [Field k] (n : ℕ) :
    IsOpen (imageExampleUj k n) := by
  exact PrimeSpectrum.isOpen_basicOpen

theorem imageExampleU_isOpen (k : Type u) [Field k] :
    IsOpen (imageExampleU k) := by
  exact isOpen_iUnion fun n => imageExampleUj_isOpen k n

theorem imageExampleT_isLocallyClosed (k : Type u) [Field k] :
    IsLocallyClosed (imageExampleT k) := by
  exact (imageExampleZ_isClosed k).isLocallyClosed.inter
    (imageExampleU_isOpen k).isLocallyClosed

/-! ## The image formula and the set `B` -/

/-
The comparison statement recalled at the start of the source section is
Mathlib's existing `Scheme.Hom.isConstructible_image`; it is reused directly
when applicable and is not redeclared here.
-/

/-- The target points where `x₁, …, xₙ₊₁` vanish and `yₙ₊₁` does not vanish. -/
def imageExampleTargetCondition (k : Type u) [Field k] (n : ℕ) :
    Set (imageExampleTargetScheme k) :=
  {p | (∀ i ∈ Finset.range (n + 1), imageExampleTargetX k i ∈ p.asIdeal) ∧
    imageExampleTargetY k n ∉ p.asIdeal}

/-- The image of `Z ∩ Uₙ₊₁` is the displayed target condition. -/
theorem imageExampleProjection_image_Z_inter_Uj
    (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    imageExampleProjection k '' (imageExampleZ k ∩ imageExampleUj k n) =
      imageExampleTargetCondition k n := by
  sorry

/-- The image `B = f(T)`. -/
def imageExampleB (k : Type u) [Field k] [CharZero k] :
    Set (imageExampleTargetScheme k) :=
  imageExampleProjection k '' imageExampleT k

/-- The image `B` is the union of the target conditions from the source. -/
theorem imageExampleB_eq_iUnion (k : Type u) [Field k] [CharZero k] :
    imageExampleB k = ⋃ n : ℕ, imageExampleTargetCondition k n := by
  sorry

/-- The set `B` is nonempty, as used for the base case of the source induction. -/
theorem imageExampleB_nonempty (k : Type u) [Field k] [CharZero k] :
    (imageExampleB k).Nonempty := by
  sorry

/-- The target zero locus of a single target coordinate. -/
def imageExampleTargetVanishing (k : Type u) [Field k]
    (r : imageExampleTargetRing k) : Set (imageExampleTargetScheme k) :=
  PrimeSpectrum.zeroLocus {r}

/-- The closure of `B` is the hyperplane `(x₁ = 0)`. -/
theorem imageExampleB_closure (k : Type u) [Field k] [CharZero k] :
    closure (imageExampleB k) =
      imageExampleTargetVanishing k (imageExampleTargetX k 0) := by
  sorry

/-- On `B`, the condition `y₁ = 0` forces `x₂ = 0`. -/
theorem imageExampleB_inter_y₁_vanishing_subset_x₂_vanishing
    (k : Type u) [Field k] [CharZero k] :
    imageExampleB k ∩ imageExampleTargetVanishing k (imageExampleTargetY k 0) ⊆
      imageExampleTargetVanishing k (imageExampleTargetX k 1) := by
  sorry

/-- A point of `B` with `y₁ = 0` has no neighborhood in `B` relative to
the hyperplane `(x₁ = 0)`. -/
theorem imageExampleB_not_mem_nhdsWithin_x₁_vanishing_of_y₁_vanishing
    (k : Type u) [Field k] [CharZero k]
    (p : imageExampleTargetScheme k)
    (hp : p ∈ imageExampleB k ∩
      imageExampleTargetVanishing k (imageExampleTargetY k 0)) :
    imageExampleB k ∉
      nhdsWithin p (imageExampleTargetVanishing k (imageExampleTargetX k 0)) := by
  sorry

/-! ## The shift used in the non-constructibility argument -/

/-- The variable map which inserts a zero first coordinate in both families. -/
def imageExampleRightShiftVariable (k : Type u) [Field k] :
    imageExampleVariable → imageExampleTargetRing k
  | .inl 0 => 0
  | .inl (Nat.succ n) => MvPolynomial.X (.inl n)
  | .inr 0 => 0
  | .inr (Nat.succ n) => MvPolynomial.X (.inr n)

/-- The polynomial-ring map underlying the right shift on points. -/
def imageExampleRightShiftRingHom (k : Type u) [Field k] :
    imageExampleTargetRing k →+* imageExampleTargetRing k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* imageExampleTargetRing k)
    (imageExampleRightShiftVariable k)

/-- The affine scheme map induced by the right shift. -/
noncomputable def imageExampleRightShiftMap (k : Type u) [Field k] :
    imageExampleTargetScheme k ⟶ imageExampleTargetScheme k :=
  Spec.map (CommRingCat.ofHom (imageExampleRightShiftRingHom k))

/-- The right shift identifies `B` with `B ∩ (y₁ = 0)`. -/
theorem imageExampleRightShift_bijOn_B
    (k : Type u) [Field k] [CharZero k] :
    Set.BijOn (imageExampleRightShiftMap k) (imageExampleB k)
      (imageExampleB k ∩ imageExampleTargetVanishing k (imageExampleTargetY k 0)) := by
  sorry

/-! ## The finite-union claim -/

/-- A set is a finite union of locally closed subsets. -/
def IsFiniteUnionLocallyClosed {α : Type*} [TopologicalSpace α] (s : Set α) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Set α,
    (∀ i, IsLocallyClosed (A i)) ∧ s = ⋃ i, A i

/-- The induction in the source shows that every finite locally closed cover of `B`
would have arbitrarily many members. -/
theorem imageExample_finite_cover_lower_bound
    (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (A : Fin m → Set (imageExampleTargetScheme k))
    (hA : ∀ i, IsLocallyClosed (A i))
    (hcover : imageExampleB k ⊆ ⋃ i, A i) :
    ∀ n : ℕ, m ≥ n := by
  sorry

/-- The set `B` is not a finite union of locally closed subsets of `Y`. -/
theorem imageExampleB_not_finite_union_locallyClosed
    (k : Type u) [Field k] [CharZero k] :
    ¬ IsFiniteUnionLocallyClosed (imageExampleB k) := by
  sorry

/-! ## The chapter lemma -/

/-- For every characteristic-zero field, the displayed construction has all
the properties asserted in the source lemma. -/
theorem imageExample_counterexample (k : Type u) [Field k] [CharZero k] :
    IsAffine (imageExampleSourceScheme k) ∧
      IsAffine (imageExampleTargetScheme k) ∧
        LocallyOfFinitePresentation (imageExampleProjection k) ∧
          QuasiCompact (imageExampleProjection k) ∧
            IsLocallyClosed (imageExampleT k) ∧
              ¬ IsFiniteUnionLocallyClosed
                (imageExampleProjection k '' imageExampleT k) := by
  sorry

/-- There is a finite-presentation morphism between affine schemes and a locally
 closed subset whose image is not a finite union of locally closed subsets. -/
theorem imageExample_no_chevalley (k : Type u) [Field k] [CharZero k] :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (T : Set X),
      IsAffine X ∧ IsAffine Y ∧
        LocallyOfFinitePresentation f ∧ QuasiCompact f ∧
          IsLocallyClosed T ∧ ¬ IsFiniteUnionLocallyClosed (f '' T) := by
  refine ⟨imageExampleSourceScheme k, imageExampleTargetScheme k,
    imageExampleProjection k, imageExampleT k, ?_⟩
  exact imageExample_counterexample k

end Formalization.«Books.Examples».Unit25
