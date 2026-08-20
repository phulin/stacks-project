import Formalization.Books.Dpa.Unit05.DividedPowerPolynomialAlgebras
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps

/-!
# Divided Power Algebra, Chapter 6: Tate resolutions

This file records the graded divided-power and differential graded algebra
interfaces used in the source section.  The graded algebra itself is the
canonical Mathlib `GradedAlgebra`; the chapter-specific fields below only
record strict graded commutativity and the divided-power identities that are
not bundled together by Mathlib.
-/

namespace Formalization.Books.Dpa.Unit06

open scoped BigOperators TensorProduct
open BigOperators

universe u v

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Graded algebras and their even and odd parts -/

/-- A strictly graded-commutative `R`-algebra, graded by the nonnegative
integers.  The decomposition and multiplicative grading are Mathlib's
`GradedAlgebra`; the two displayed source conditions are recorded explicitly.
-/
structure GradedCommAlgebra (R A : Type u) [CommRing R] [Ring A]
    [Algebra R A] where
  component : ℕ → Submodule R A
  graded : GradedAlgebra component
  graded_commutative : ∀ {i j : ℕ} {x y : A},
    x ∈ component i → y ∈ component j →
      x * y = (-1 : A) ^ (i * j) * (y * x)
  odd_square_zero : ∀ {i : ℕ} {x : A}, Odd i → x ∈ component i → x * x = 0

namespace GradedCommAlgebra

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

/-- The homogeneous projection onto degree `n`. -/
def proj (G : GradedCommAlgebra R A) (n : ℕ) (x : A) : A :=
  letI := G.graded
  GradedAlgebra.proj G.component n x

/-- An element supported in even degrees. -/
def IsEven (G : GradedCommAlgebra R A) (x : A) : Prop :=
  ∀ n : ℕ, Odd n → G.proj n x = 0

/-- An element supported in positive even degrees. -/
def IsPositiveEven (G : GradedCommAlgebra R A) (x : A) : Prop :=
  G.IsEven x ∧ G.proj 0 x = 0

/-- An element supported in odd degrees. -/
def IsOdd (G : GradedCommAlgebra R A) (x : A) : Prop :=
  ∀ n : ℕ, Even n → G.proj n x = 0

/-- A homogeneous element in an odd degree. -/
def IsHomogeneousOdd (G : GradedCommAlgebra R A) (x : A) : Prop :=
  ∃ n : ℕ, x ∈ G.component (2 * n + 1)

end GradedCommAlgebra

/-! ## Divided powers on a graded algebra -/

/-- The seven source conditions for divided powers on the positive even part.

The operation is zero outside the positive even part, as in Mathlib's
zero-extended `DividedPowers.dpow`; this makes the source's convention
`gamma₀(x) = 1` on the ideal precise without introducing a second operation.
-/
structure GradedDividedPowers {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (G : GradedCommAlgebra R A) where
  dpow : ℕ → A → A
  dpow_null : ∀ {n : ℕ} {x : A}, ¬G.IsPositiveEven x → dpow n x = 0
  dpow_mem : ∀ {n : ℕ} {x : A}, n ≠ 0 → G.IsPositiveEven x →
    G.IsPositiveEven (dpow n x)
  dpow_zero : ∀ {x : A}, G.IsPositiveEven x → dpow 0 x = 1
  dpow_one : ∀ {x : A}, G.IsPositiveEven x → dpow 1 x = x
  dpow_mul : ∀ {n m : ℕ} {x : A}, G.IsPositiveEven x →
    dpow n x * dpow m x = (Nat.choose (n + m) n : A) * dpow (n + m) x
  dpow_mul_left : ∀ {n : ℕ} {x y : A}, G.IsEven x →
    G.IsPositiveEven y → dpow n (x * y) = x ^ n * dpow n y
  dpow_odd_mul : ∀ {n : ℕ} {x y : A}, G.IsHomogeneousOdd x →
    G.IsHomogeneousOdd y → 1 < n → dpow n (x * y) = 0
  dpow_add : ∀ {n : ℕ} {x y : A}, G.IsPositiveEven x →
    G.IsPositiveEven y →
      dpow n (x + y) = (Finset.range (n + 1)).sum
        (fun i => dpow i x * dpow (n - i) y)
  dpow_comp : ∀ {n m : ℕ} {x : A}, n ≠ 0 → m ≠ 0 →
    G.IsPositiveEven x →
      dpow n (dpow m x) = (Nat.uniformBell n m : A) * dpow (n * m) x

namespace GradedDividedPowers

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {G : GradedCommAlgebra R A}

/-- The factorial identity attached to a graded divided-power structure. -/
theorem factorial_mul_dpow_eq_pow (γ : GradedDividedPowers G)
    {n : ℕ} {x : A} (hx : G.IsPositiveEven x) :
    (Nat.factorial n : A) * γ.dpow n x = x ^ n := by
  sorry

/-- Conditions (2), (3), (4), (6), and (7) give the ordinary divided-power
structure on the positive even ideal; condition (1) is the grading condition.
-/
def IsOrdinaryDividedPowerStructure (γ : GradedDividedPowers G) : Prop :=
  ∀ {n : ℕ} {x : A}, G.IsPositiveEven x →
    (Nat.factorial n : A) * γ.dpow n x = x ^ n

end GradedDividedPowers

/-- The odd-product warning in the source, expressed as the displayed
divided-power identity. -/
def OddProductSumIdentity {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (G : GradedCommAlgebra R A)
    (γ : GradedDividedPowers G) (z₁ z₂ z₃ z₄ : A) : Prop :=
  G.IsHomogeneousOdd z₁ ∧ G.IsHomogeneousOdd z₂ ∧
    G.IsHomogeneousOdd z₃ ∧ G.IsHomogeneousOdd z₄ ∧
      γ.dpow 2 (z₁ * z₂ + z₃ * z₄) = z₁ * z₂ * z₃ * z₄

/-- It is possible for the odd-product sum in the preceding identity to have
nonzero second divided power. -/
def HasNonzeroOddProductSum {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (G : GradedCommAlgebra R A)
    (γ : GradedDividedPowers G) : Prop :=
  ∃ z₁ z₂ z₃ z₄ : A, OddProductSumIdentity G γ z₁ z₂ z₃ z₄ ∧
    γ.dpow 2 (z₁ * z₂ + z₃ * z₄) ≠ 0

/-! ## The adjoining-variable examples -/

/-- The square-zero extension used for adjoining one odd generator. -/
abbrev OddAdjoin (A : Type u) [Ring A] := TrivSqZeroExt A A

/-- The element `x + yT` in the odd adjoining construction. -/
def oddAdjoinElement {A : Type u} [Ring A] (x y : A) : OddAdjoin A :=
  (x, y)

/-- The divided-power polynomial algebra used for adjoining one even generator.
-/
abbrev EvenAdjoin (A : Type u) [CommRing A] := DividedPowerAlgebra A (Unit →₀ A)

/-- The element `T^(i)` in the even adjoining construction. -/
def evenAdjoinVariable {A : Type u} [CommRing A] (i : ℕ) : EvenAdjoin A :=
  DividedPowerAlgebra.dp A i (Finsupp.single () 1)

/-- A finite formal sum `∑ xᵢ T^(i)` in the even adjoining construction. -/
def evenAdjoinPolynomial {A : Type u} [CommRing A] (x : ℕ →₀ A) : EvenAdjoin A :=
  algebraMap A (EvenAdjoin A) (x 0) +
    (x.support.erase 0).sum (fun i =>
      algebraMap A (EvenAdjoin A) (x i) * evenAdjoinVariable i)

/-- The finite expansion of the divided power of a polynomial with zero
constant term.  The bounded exponent functions make the source's finite sum
over all tuples `(e_i)` explicit. -/
def evenAdjoinPositiveExpansion {A : Type u} [CommRing A]
    (x : ℕ →₀ A) (n : ℕ) : EvenAdjoin A :=
  let I := x.support.erase 0
  (Finset.univ.filter (fun e : I → Fin (n + 1) =>
      (Finset.univ.sum (fun i : I => (e i : ℕ))) = n)).sum (fun e =>
    (Finset.univ.prod (fun i : I =>
      algebraMap A (EvenAdjoin A) ((x i) ^ (e i : ℕ)))) *
      evenAdjoinVariable
        (Finset.univ.sum (fun i : I => (i : ℕ) * (e i : ℕ))))

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)

/-- The source formula characterizing divided powers after adjoining an odd
variable. -/
def IsOddAdjoinDividedPowerExtension
    (E : GradedCommAlgebra R (OddAdjoin A))
    (δ : GradedDividedPowers E) : Prop :=
  ∀ {n : ℕ} {x y : A}, n ≠ 0 → G.IsPositiveEven x →
    G.IsOdd y →
      δ.dpow n (oddAdjoinElement x y) =
        oddAdjoinElement (γ.dpow n x) (γ.dpow (n - 1) x * y)

/-- The odd adjoining construction has the unique compatible divided-power
structure described in the source. -/
theorem exists_unique_odd_adjoin_dividedPowers
    (E : GradedCommAlgebra R (OddAdjoin A)) :
    ∃! δ : GradedDividedPowers E,
      IsOddAdjoinDividedPowerExtension G γ E δ := by
  sorry

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)

/-- The source formula characterizing divided powers after adjoining an even
variable. -/
def IsEvenAdjoinDividedPowerExtension
    (E : GradedCommAlgebra R (EvenAdjoin A))
    (δ : GradedDividedPowers E) : Prop :=
  (∀ {n : ℕ} {x : A}, G.IsPositiveEven x →
    δ.dpow n (algebraMap A (EvenAdjoin A) x) =
      algebraMap A (EvenAdjoin A) (γ.dpow n x)) ∧
    (∀ n i : ℕ, δ.dpow n (evenAdjoinVariable i) =
      evenAdjoinVariable (n * i)) ∧
    (∀ {n : ℕ} {x : ℕ →₀ A},
      (∀ i, G.IsEven (x i)) → G.IsPositiveEven (x 0) →
        δ.dpow n (evenAdjoinPolynomial x) =
          (Finset.range (n + 1)).sum (fun a =>
            algebraMap A (EvenAdjoin A) (γ.dpow a (x 0)) *
              evenAdjoinPositiveExpansion x (n - a)))

/-- The even adjoining construction has the unique compatible divided-power
structure described in the source. -/
theorem exists_unique_even_adjoin_dividedPowers
    (E : GradedCommAlgebra R (EvenAdjoin A)) :
    ∃! δ : GradedDividedPowers E,
      IsEvenAdjoinDividedPowerExtension G γ E δ := by
  sorry

/-! The same constructions for a set of variables. -/

/-- The exterior algebra on a set of odd variables. -/
abbrev OddAdjoinVariables (A : Type u) [CommRing A] (J : Type u) :=
  ExteriorAlgebra A (J →₀ A)

/-- The divided-power algebra on a set of even variables. -/
abbrev EvenAdjoinVariables (A : Type u) [CommRing A] (J : Type u) :=
  DividedPowerAlgebra A (J →₀ A)

/-- Compatibility with the coefficient algebra for a set of exterior
generators. -/
def IsOddAdjoinSetDividedPowerExtension
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)
    {J : Type u} (E : GradedCommAlgebra R (OddAdjoinVariables A J))
    (δ : GradedDividedPowers E) : Prop :=
  ∀ {n : ℕ} {x : A}, G.IsPositiveEven x →
    δ.dpow n (algebraMap A (OddAdjoinVariables A J) x) =
      algebraMap A (OddAdjoinVariables A J) (γ.dpow n x)

/-- Adjoining any set of exterior generators has a unique compatible
divided-power structure. -/
theorem unique_odd_dividedPowers_on_adjoin_set
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)
    {J : Type u} (E : GradedCommAlgebra R (OddAdjoinVariables A J)) :
    ∃! δ : GradedDividedPowers E,
      IsOddAdjoinSetDividedPowerExtension G γ E δ := by
  sorry

/- The canonical divided-power algebra has a distinguished divided-power
   variable for every member of the indexing set. -/
def evenAdjoinSetVariable {A : Type u} [CommRing A] {J : Type u}
    (i : ℕ) (j : J) : EvenAdjoinVariables A J :=
  DividedPowerAlgebra.dp A i (Finsupp.single j 1)

/-- Compatibility with the coefficient algebra and all the variables in a
set-adjoining construction. -/
def IsEvenAdjoinSetDividedPowerExtension
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)
    {J : Type u} (E : GradedCommAlgebra R (EvenAdjoinVariables A J))
    (δ : GradedDividedPowers E) : Prop :=
  (∀ {n : ℕ} {x : A}, G.IsPositiveEven x →
    δ.dpow n (algebraMap A (EvenAdjoinVariables A J) x) =
      algebraMap A (EvenAdjoinVariables A J) (γ.dpow n x)) ∧
    (∀ n i : ℕ, ∀ j : J,
      δ.dpow n (evenAdjoinSetVariable i j) =
        evenAdjoinSetVariable (n * i) j)

/-- A fixed directed-colimit model of adjoining a set of variables has a
unique compatible divided-power structure. -/
theorem unique_dividedPowers_on_adjoin_set
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : GradedCommAlgebra R A) (γ : GradedDividedPowers G)
    {J : Type u} (E : GradedCommAlgebra R (EvenAdjoinVariables A J)) :
    ∃! δ : GradedDividedPowers E,
      IsEvenAdjoinSetDividedPowerExtension G γ E δ := by
  sorry

/-! ## Differential graded algebras -/

/-- A differential of homological degree `-1` on a graded algebra. -/
structure GradedDifferential {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (G : GradedCommAlgebra R A) where
  d : A →ₗ[R] A
  d_zero : ∀ {x : A}, x ∈ G.component 0 → d x = 0
  d_mem : ∀ {n : ℕ} {x : A}, 0 < n → x ∈ G.component n →
    d x ∈ G.component (n - 1)
  d_squared : d.comp d = 0
  leibniz : ∀ {i j : ℕ} {x y : A}, x ∈ G.component i → y ∈ G.component j →
    d (x * y) = d x * y + (-1 : A) ^ i * x * d y

/-- Compatibility of divided powers with a differential, as in the source. -/
def DifferentialCompatible {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] {G : GradedCommAlgebra R A}
    (γ : GradedDividedPowers G) (differential : GradedDifferential G) : Prop :=
  ∀ {n : ℕ} {x : A}, n ≠ 0 → G.IsPositiveEven x →
    differential.d (γ.dpow n x) = differential.d x * γ.dpow (n - 1) x

/-- A strictly graded-commutative differential graded algebra with divided
powers. -/
structure DividedPowerDGA (R A : Type u) [CommRing R] [Ring A]
    [Algebra R A] where
  gradedAlgebra : GradedCommAlgebra R A
  dividedPowers : GradedDividedPowers gradedAlgebra
  differential : GradedDifferential gradedAlgebra
  differential_compatible : DifferentialCompatible dividedPowers differential

namespace DividedPowerDGA

variable {R A B : Type u} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]

/-- A morphism of divided-power differential graded algebras. -/
structure Hom (D : DividedPowerDGA R A) (E : DividedPowerDGA R B) where
  toAlgHom : A →ₐ[R] B
  map_graded : ∀ {n : ℕ} {x : A},
    x ∈ D.gradedAlgebra.component n →
      toAlgHom x ∈ E.gradedAlgebra.component n
  map_differential : ∀ x : A,
    toAlgHom (D.differential.d x) = E.differential.d (toAlgHom x)
  map_divided_powers : ∀ {n : ℕ} {x : A},
    D.gradedAlgebra.IsPositiveEven x →
      toAlgHom (D.dividedPowers.dpow n x) =
        E.dividedPowers.dpow n (toAlgHom x)

end DividedPowerDGA

/-! ## Homology quotients -/

namespace DividedPowerDGA

variable {R A B : Type u} [CommRing R] [Ring A] [Ring B]
  [Algebra R A]

/-- The cycles in homological degree `n`. -/
def cycles (D : DividedPowerDGA R A) (n : ℕ) : Submodule R A :=
  { carrier := {x | x ∈ D.gradedAlgebra.component n ∧ D.differential.d x = 0}
    zero_mem' := by
      exact ⟨D.gradedAlgebra.component n |>.zero_mem, by simp⟩
    add_mem' := by
      intro x y hx hy
      exact ⟨D.gradedAlgebra.component n |>.add_mem hx.1 hy.1, by
        simp [map_add, hx.2, hy.2]⟩
    smul_mem' := by
      intro r x hx
      exact ⟨D.gradedAlgebra.component n |>.smul_mem r hx.1, by
        simp [map_smul, hx.2]⟩ }

/-- Boundaries, regarded as a submodule of the cycles. -/
def boundariesInCycles (D : DividedPowerDGA R A) (n : ℕ) :
    Submodule R (cycles D n) :=
  { carrier := {x | ∃ y : A, y ∈ D.gradedAlgebra.component (n + 1) ∧
      D.differential.d y = x.1}
    zero_mem' := by
      exact ⟨0, D.gradedAlgebra.component (n + 1) |>.zero_mem, by simp⟩
    add_mem' := by
      intro x y hx hy
      rcases hx with ⟨x', hx', hxeq⟩
      rcases hy with ⟨y', hy', hyeq⟩
      refine ⟨x' + y', D.gradedAlgebra.component (n + 1) |>.add_mem hx' hy', ?_⟩
      simp [map_add, hxeq, hyeq]
    smul_mem' := by
      intro r x hx
      rcases hx with ⟨y, hy, hdy⟩
      refine ⟨r • y, D.gradedAlgebra.component (n + 1) |>.smul_mem r hy, ?_⟩
      simp [map_smul, hdy] }

/-- The homology module in degree `n`, as cycles modulo boundaries. -/
abbrev homologyComponent (D : DividedPowerDGA R A) (n : ℕ) : Type u :=
  cycles D n ⧸ boundariesInCycles D n

/-- The homology target for a ring with zero differential. -/
def zeroHomologyComponent (S : Type u) [AddCommMonoid S] (n : ℕ) : Type u :=
  if n = 0 then S else PUnit

/-- An explicit quotient-level formulation of a quasi-isomorphism to a ring
concentrated in degree zero. -/
def IsQuasiIsomorphism (D : DividedPowerDGA R A) (f : A →+* B) : Prop :=
  ∃ g : ∀ n : ℕ, homologyComponent D n → zeroHomologyComponent B n,
    (∀ n, Function.Bijective (g n)) ∧
      (∀ x : cycles D 0, g 0 (Submodule.Quotient.mk x) = f x.1)

end DividedPowerDGA

/-! ## Tate resolutions -/

/-- The set of coefficient and positive-degree generators of a graded algebra.
-/
def gradedPolynomialGeneratorSet {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (G : GradedCommAlgebra R A)
    (J : ℕ → Type v) (g : ∀ n, J n → A) : Set A :=
  {x | x ∈ G.component 0} ∪ ⋃ n : ℕ, Set.range (g n)

/-- A concrete presentation condition for a graded divided-power polynomial
algebra: the coefficient degree-zero part and the chosen variables generate
the whole algebra as an `R`-subalgebra. -/
def IsGradedDividedPowerPolynomial {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (D : DividedPowerDGA R A) : Prop :=
  ∃ (J : ℕ → Type u) (g : ∀ n, J n → A),
    (∀ n j, g n j ∈ D.gradedAlgebra.component (n + 1)) ∧
      Algebra.adjoin R (gradedPolynomialGeneratorSet D.gradedAlgebra J g) = ⊤

/-- Finite generation in each degree for a Tate resolution. -/
def IsFiniteInEachDegree {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (D : DividedPowerDGA R A) : Prop :=
  ∃ (J : ℕ → Type u) (g : ∀ n, J n → A),
    (∀ n, Finite (J n)) ∧
      (∀ n j, g n j ∈ D.gradedAlgebra.component (n + 1)) ∧
        Algebra.adjoin R (gradedPolynomialGeneratorSet D.gradedAlgebra J g) = ⊤

/-- The degree-zero polynomial presentation required in Tate's construction. -/
def IsDegreeZeroPolynomialSurjection {R S A : Type u} [CommRing R] [CommRing S]
    [Ring A] [Algebra R A]
    (G : GradedCommAlgebra R A) (augmentation : A →+* S) : Prop :=
  ∃ (J : Type u) (φ : MvPolynomial J R →ₐ[R] A),
    Function.Surjective (augmentation.comp φ.toRingHom) ∧
      ∀ x, φ x ∈ G.component 0

/-- A Tate resolution of a ring map, with quasi-isomorphism expressed on the
concrete homology quotients. -/
structure TateResolution (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S) where
  A : Type u
  ringA : Ring A
  algebraA : Algebra R A
  dga : @DividedPowerDGA R A _ ringA algebraA
  augmentation : A →+* S
  augmentation_restricts : ∀ r : R,
    augmentation (algebraMap R A r) = f r
  degree_zero_polynomial_surjective :
    IsDegreeZeroPolynomialSurjection dga.gradedAlgebra augmentation
  quasi_isomorphism : @DividedPowerDGA.IsQuasiIsomorphism R A S _ ringA _
    algebraA dga augmentation
  graded_divided_power_polynomial : IsGradedDividedPowerPolynomial dga

/-- Tate's existence theorem, including the basic factorization. -/
theorem exists_tateResolution {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    Nonempty (TateResolution R S f) := by
  sorry

theorem exists_tateResolution_finite {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing R]
    (hfinite : RingHom.FiniteType f) :
    ∃ T : TateResolution R S f,
      @IsFiniteInEachDegree R T.A _ T.ringA T.algebraA T.dga := by
  sorry

/-! The pseudo-coherent refinement of Tate's construction. -/

/-- A compact ring-map interface for the pseudo-coherent hypothesis used by
the source refinement. -/
abbrev IsPseudoCoherentRingMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  Formalization.Books.MoreAlgebra.Unit83.IsPseudoCoherentRingMap f

theorem exists_tateResolution_pseudoCoherent {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (hpseudo : IsPseudoCoherentRingMap f) :
    ∃ T : TateResolution R S f,
      @IsFiniteInEachDegree R T.A _ T.ringA T.algebraA T.dga := by
  sorry

/-! ## Uniqueness and Tor -/

namespace DividedPowerDGA

variable {R A B : Type u} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]

/-- The map induced on degree-zero homology by a DGA map, written directly on
representatives. -/
def homologyZeroMap (D : DividedPowerDGA R A) (E : DividedPowerDGA R B)
    (F : Hom D E) (x : cycles D 0) : homologyComponent E 0 :=
  Submodule.Quotient.mk
    ⟨F.toAlgHom x.1,
      ⟨F.map_graded x.2.1, by
        rw [← F.map_differential, x.2.2, map_zero]⟩⟩

/-- A degree-zero homology map is lifted by `F`. -/
def LiftsHomologyZeroMap (D : DividedPowerDGA R A)
    (E : DividedPowerDGA R B) (F : Hom D E)
    (φ : homologyComponent D 0 →ₗ[R] homologyComponent E 0) : Prop :=
  ∀ x : cycles D 0,
    φ (Submodule.Quotient.mk x) = homologyZeroMap D E F x

/-- A ring model for degree-zero homology, used to state the source's
algebra-map lifting theorem before a multiplication on the quotient is
chosen explicitly. -/
structure HomologyZeroAlgebraModel (D : DividedPowerDGA R A) where
  H0 : Type u
  ringH0 : Ring H0
  algebraH0 : Algebra R H0
  equivalence : Nonempty (H0 ≃ₗ[R] homologyComponent D 0)

/-- Transport an algebra map between degree-zero homology models to the
explicit cycle quotient. -/
noncomputable def homologyZeroLinearMapOfModels
    (D : DividedPowerDGA R A) (E : DividedPowerDGA R B)
    (HD : HomologyZeroAlgebraModel D) (HE : HomologyZeroAlgebraModel E)
    (φ : @AlgHom R HD.H0 HE.H0 _ HD.ringH0.toSemiring HE.ringH0.toSemiring
      HD.algebraH0 HE.algebraH0) :
    homologyComponent D 0 →ₗ[R] homologyComponent E 0 :=
  letI := HD.ringH0
  letI := HE.ringH0
  letI := HD.algebraH0
  letI := HE.algebraH0
  let eD := Classical.choice HD.equivalence
  let eE := Classical.choice HE.equivalence
  eE.toLinearMap.comp (φ.toLinearMap.comp eD.symm.toLinearMap)

/-- The source's uniqueness theorem for maps out of a graded divided-power
polynomial algebra. -/
theorem exists_dgaHom_lifting_homologyZeroMap
    (D : DividedPowerDGA R A) (E : DividedPowerDGA R B)
    (HD : HomologyZeroAlgebraModel D) (HE : HomologyZeroAlgebraModel E)
    (φ : @AlgHom R HD.H0 HE.H0 _ HD.ringH0.toSemiring HE.ringH0.toSemiring
      HD.algebraH0 HE.algebraH0)
    (hpoly : IsGradedDividedPowerPolynomial D)
    (hacyclic : ∀ k : ℕ, 0 < k → Subsingleton (homologyComponent E k)) :
    ∃ F : Hom D E,
      LiftsHomologyZeroMap D E F (homologyZeroLinearMapOfModels D E HD HE φ) := by
  sorry

/-- A graded algebra model for the Tor groups of two commutative
`R`-algebras. -/
abbrev torComponent (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (n : ℕ) : Type u :=
  (Formalization.Books.Algebra.Unit75.Tor (ModuleCat.of R S) (ModuleCat.of R T) n : Type u)

/-- A graded algebra model for the Tor groups of two commutative
`R`-algebras. -/
structure TorAlgebraModel (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] where
  A : Type u
  ringA : Ring A
  algebraA : Algebra R A
  gradedA : @GradedCommAlgebra R A _ ringA algebraA
  component : ℕ → Type u
  component_addCommGroup : ∀ n, AddCommGroup (component n)
  component_equiv : ∀ n,
    Nonempty ((gradedA.component n : Type u) ≃ torComponent R S T n)

/-- An algebra equivalence preserves two graded divided-power structures. -/
def PreservesGradedDividedPowers {R A B : Type u} [CommRing R] [Ring A]
    [Ring B] [Algebra R A] [Algebra R B]
    {GA : GradedCommAlgebra R A} {GB : GradedCommAlgebra R B}
    (γ : GradedDividedPowers GA) (γ' : GradedDividedPowers GB)
    (e : A ≃ₐ[R] B) : Prop :=
  ∀ n x, e (γ.dpow n x) = γ'.dpow n (e x)

/-- The canonical strict graded-commutative divided-power structure on Tor. -/
theorem exists_dividedPowers_on_tor {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : TorAlgebraModel R S T) :
    Nonempty (@GradedDividedPowers R M.A _ M.ringA M.algebraA M.gradedA) := by
  sorry

/-- The structure on Tor is independent of the chosen Tate resolution. -/
theorem tor_dividedPowers_independent {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M M' : TorAlgebraModel R S T)
    (γ : @GradedDividedPowers R M.A _ M.ringA M.algebraA M.gradedA)
    (γ' : @GradedDividedPowers R M'.A _ M'.ringA M'.algebraA M'.gradedA) :
    ∃ e : @AlgEquiv R M.A M'.A _ M.ringA.toSemiring M'.ringA.toSemiring
        M.algebraA M'.algebraA,
    @PreservesGradedDividedPowers R M.A M'.A _ M.ringA M'.ringA
        M.algebraA M'.algebraA M.gradedA M'.gradedA γ γ' e := by
  sorry

/-! ## Homology and the good DGA lemma -/

/-- A graded algebra model for the homology algebra of a DGA. -/
structure HomologyAlgebraModel {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (D : DividedPowerDGA R A) where
  H : Type u
  ringH : Ring H
  algebraH : Algebra R H
  gradedH : @GradedCommAlgebra R H _ ringH algebraH
  component_equiv : ∀ n : ℕ,
    Nonempty ((gradedH.component n : Type u) ≃ₗ[R] homologyComponent D n)

/-- The property that a chosen homology algebra model carries divided powers.
The source warning is that this property is not automatic for an arbitrary
DGA; the good-DGA lemma below supplies it under additional hypotheses. -/
def HasDividedPowersOnHomology {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] {D : DividedPowerDGA R A} (H : HomologyAlgebraModel D) : Prop :=
  Nonempty (@GradedDividedPowers R H.H _ H.ringH H.algebraH H.gradedH)

/-- The source's good-DGA lemma: under positive acyclicity and surjectivity,
the divided powers descend to the homology algebra of the target. -/
theorem dividedPowers_induce_on_homology
    {R A B : Type u} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B]
    (D : DividedPowerDGA R A) (E : DividedPowerDGA R B)
    (F : Hom D E) (hacyclic : ∀ k : ℕ, 0 < k →
      Subsingleton (homologyComponent D k))
    (hsurjective : Function.Surjective F.toAlgHom)
    (H : HomologyAlgebraModel E) :
    HasDividedPowersOnHomology H := by
  sorry

/-- Base change preserves the differential graded divided-power structure. -/
theorem baseChange_dividedPowerDGA
    {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (D : DividedPowerDGA R A) (R' : Type u) [CommRing R'] [Algebra R R'] :
    Nonempty (DividedPowerDGA R' (A ⊗[R] R')) := by
  sorry

end DividedPowerDGA

/-! ## Extending a differential over one generator -/

namespace DividedPowerDGA

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

/-- The source's conditions on a differential over an adjoined variable. -/
def IsDifferentialExtension {B : Type u} [Ring B] [Algebra R B]
    (D : DividedPowerDGA R A) (E : GradedCommAlgebra R B)
    (δ : GradedDividedPowers E) (f : A) (differential : A →ₗ[R] A)
    (d' : B →ₗ[R] B) (ι : A →ₐ[R] B) (T : B) : Prop :=
  (∀ x : A, d' (ι x) = ι (differential x)) ∧
    d' T = ι f ∧
    ∃ extensionDifferential : GradedDifferential E,
      extensionDifferential.d = d' ∧
        DifferentialCompatible δ extensionDifferential

/-- Adjoining an odd variable extends the differential uniquely. -/
theorem exists_unique_differential_odd_adjoin
    (D : DividedPowerDGA R A) (E : GradedCommAlgebra R (OddAdjoin A))
    (δ : GradedDividedPowers E) (d : ℕ) (f : A)
    (hf : f ∈ D.gradedAlgebra.component (d - 1))
    (hclosed : D.differential.d f = 0)
    (ι : A →ₐ[R] OddAdjoin A) (T : OddAdjoin A)
    (hT : T ∈ E.component d) :
    ∃! d' : OddAdjoin A →ₗ[R] OddAdjoin A,
      IsDifferentialExtension D E δ f D.differential.d d' ι T := by
  sorry

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Adjoining an even variable extends the differential uniquely. -/
theorem exists_unique_differential_even_adjoin
    (D : DividedPowerDGA R A) (E : GradedCommAlgebra R (EvenAdjoin A))
    (δ : GradedDividedPowers E) (d : ℕ) (f : A)
    (hf : f ∈ D.gradedAlgebra.component (d - 1))
    (hclosed : D.differential.d f = 0)
    (ι : A →ₐ[R] EvenAdjoin A) (T : EvenAdjoin A)
    (hT : T ∈ E.component d) :
    ∃! d' : EvenAdjoin A →ₗ[R] EvenAdjoin A,
      IsDifferentialExtension D E δ f D.differential.d d' ι T := by
  sorry

end DividedPowerDGA

end

end Formalization.Books.Dpa.Unit06
