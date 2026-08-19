import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit68.RegularSequences
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial

/-!
# Commutative Algebra, Chapter 69: Quasi-regular sequences

The associated graded pieces are written as nested submodule quotients.  For an ideal `I`,
the denominator in degree `n` is `I • ⊤` inside `I ^ n • ⊤`; this is the canonical Mathlib
presentation of `I ^ n M / I ^ (n + 1) M`.
-/

namespace Formalization.Books.Algebra.Unit69

open scoped DirectSum TensorProduct

noncomputable section

universe u v

/-! ## The canonical graded map -/

/-- The total degree of a finitely supported multi-index. -/
def quasiRegularDegree {n : ℕ} (d : Fin n →₀ ℕ) : ℕ :=
  d.sum fun _ e => e

/-- The coefficient in `R` attached to a multi-index and a finite sequence. -/
def quasiRegularMonomialCoefficient
    {R : Type u} [CommRing R] (f : List R) (d : Fin f.length →₀ ℕ) : R :=
  d.prod fun i e => f.get i ^ e

/-- Each monomial coefficient belongs to the corresponding power of the generated ideal. -/
theorem quasiRegularMonomialCoefficient_mem
    {R : Type u} [CommRing R] (f : List R) (d : Fin f.length →₀ ℕ) :
    quasiRegularMonomialCoefficient f d ∈
      (Ideal.ofList f) ^ quasiRegularDegree d := by
  sorry

/-- The `n`-th associated graded piece of a module for an ideal. -/
abbrev quasiRegularPiece
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :=
  (↥(I ^ n • (⊤ : Submodule R M))) ⧸
    (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))

/-- The direct sum of the associated graded pieces. -/
abbrev quasiRegularTarget
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :=
  ⨁ n, quasiRegularPiece R M I n

/-- The source of the canonical graded map in the textbook. -/
abbrev quasiRegularSource
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :=
  (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList f]
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f)

/-- The raw map sending a module element to the corresponding monomial in one graded piece. -/
def quasiRegularMonomialMapRaw
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    M →ₗ[R] quasiRegularPiece R M (Ideal.ofList f) (quasiRegularDegree d) := by
  let I := Ideal.ofList f
  let n := quasiRegularDegree d
  let P := I ^ n • (⊤ : Submodule R M)
  let Q := I • (⊤ : Submodule R ↥P)
  let a := quasiRegularMonomialCoefficient f d
  let ha : a ∈ I ^ n := quasiRegularMonomialCoefficient_mem f d
  let φ : M →ₗ[R] ↥P :=
    (LinearMap.lsmul R M a).codRestrict P (fun m =>
      Submodule.smul_mem_smul ha (Submodule.mem_top : m ∈ (⊤ : Submodule R M)))
  exact Q.mkQ.comp φ

/-- Multiplication by an element of the generated ideal kills the raw monomial map. -/
theorem quasiRegularMonomialMapRaw_ker
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    Ideal.ofList f • (⊤ : Submodule R M) ≤
      LinearMap.ker (quasiRegularMonomialMapRaw R M f d) := by
  sorry

/-- The raw map is semilinear for the quotient map on scalars. -/
theorem quasiRegularMonomialMapRaw_map_smul_quotient
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (r : R) (m : M) :
    quasiRegularMonomialMapRaw R M f d (r • m) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularMonomialMapRaw R M f d m := by
  sorry

/- The quotient of a semilinear map by `I` is linear over `R ⧸ I`. -/
theorem quotientSemilinearMap_smul
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R)
    (hN : Module.IsTorsionBySet R N I)
    (g : letI := hN.module
      (M ⧸ (I • (⊤ : Submodule R M))) →ₛₗ[Ideal.Quotient.mk I] N)
    (s : R ⧸ I) (x : M ⧸ (I • (⊤ : Submodule R M))) :
    let := hN.module
    g (s • x) = s • g x := by
  sorry

/-- Turn the semilinear quotient map into its canonical quotient-ring linear map. -/
def quotientSemilinearMapToLinear
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R)
    (hN : Module.IsTorsionBySet R N I)
    (g : letI := hN.module
      (M ⧸ (I • (⊤ : Submodule R M))) →ₛₗ[Ideal.Quotient.mk I] N) :
    letI := hN.module
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] N :=
  letI := hN.module
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun s x => quotientSemilinearMap_smul I hN g s x }

/-- The monomial map after passing to `M / IM`. -/
def quasiRegularMonomialMapQuotient
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularPiece R M (Ideal.ofList f) (quasiRegularDegree d) := by
  let I := Ideal.ofList f
  let hN := Module.isTorsionBySet_quotient_ideal_smul
    (M := ↥(I ^ quasiRegularDegree d • (⊤ : Submodule R M))) (I := I)
  letI : Module (R ⧸ I)
      (quasiRegularPiece R M I (quasiRegularDegree d)) := hN.module
  let g : M →ₛₗ[Ideal.Quotient.mk I]
      quasiRegularPiece R M I (quasiRegularDegree d) :=
    { toFun := quasiRegularMonomialMapRaw R M f d
      map_add' := (quasiRegularMonomialMapRaw R M f d).map_add
      map_smul' := fun r m => quasiRegularMonomialMapRaw_map_smul_quotient R M f d r m }
  let gq := (I • (⊤ : Submodule R M)).liftQ g
    (quasiRegularMonomialMapRaw_ker R M f d)
  exact quotientSemilinearMapToLinear I hN gq

/-- Coefficients from the arbitrary module act on every associated-graded piece through `R / I`. -/
theorem quasiRegularMonomialMapQuotient_coeff_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (r : R) (m : M) :
    quasiRegularMonomialMapQuotient R M f d
        (Submodule.Quotient.mk (r • m)) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m) := by
  sorry

/-- The polynomial-linear map obtained by summing the monomial components. -/
def quasiRegularPolynomialMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (m : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  (Finsupp.lsum (R ⧸ Ideal.ofList f) (fun d =>
      LinearMap.toSpanSingleton (R ⧸ Ideal.ofList f)
        (quasiRegularTarget R M (Ideal.ofList f))
        (DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
          (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
          (quasiRegularDegree d)
          (quasiRegularMonomialMapQuotient R M f d m)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R ⧸ Ideal.ofList f)).toLinearMap

theorem quasiRegularPolynomialMap_add
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (m₁ m₂ : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularPolynomialMap R M f (m₁ + m₂) =
      quasiRegularPolynomialMap R M f m₁ + quasiRegularPolynomialMap R M f m₂ := by
  sorry

theorem quasiRegularPolynomialMap_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (c : R ⧸ Ideal.ofList f)
    (m : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularPolynomialMap R M f (c • m) =
      c • quasiRegularPolynomialMap R M f m := by
  sorry

/-- The bilinear map underlying the canonical tensor-product map. -/
def quasiRegularBilinearMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) →ₗ[R ⧸ Ideal.ofList f]
      MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) →ₗ[R ⧸ Ideal.ofList f]
        quasiRegularTarget R M (Ideal.ofList f) :=
  LinearMap.mk₂ (R ⧸ Ideal.ofList f)
    (fun m p => quasiRegularPolynomialMap R M f m p)
    (fun m₁ m₂ p => by
      simpa using congrArg (fun q => q p) (quasiRegularPolynomialMap_add R M f m₁ m₂))
    (fun c m p => by
      simpa using congrArg (fun q => q p) (quasiRegularPolynomialMap_smul R M f c m))
    (fun m p₁ p₂ => (quasiRegularPolynomialMap R M f m).map_add p₁ p₂)
    (fun c m p => (quasiRegularPolynomialMap R M f m).map_smul c p)

/-- The canonical graded map from the textbook. -/
def quasiRegularCanonicalMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    quasiRegularSource R M f →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  TensorProduct.lift (quasiRegularBilinearMap R M f)

theorem quasiRegularCanonicalMap_monomial
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (m : M) (d : Fin f.length →₀ ℕ) :
    quasiRegularCanonicalMap R M f
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList f]
          MvPolynomial.monomial d 1) =
      DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
        (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
        (quasiRegularDegree d)
        (quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m)) := by
  sorry

theorem quasiRegularCanonicalMap_coeff_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (r : R) (m : M) (d : Fin f.length →₀ ℕ) :
    quasiRegularCanonicalMap R M f
        (Submodule.Quotient.mk (r • m) ⊗ₜ[R ⧸ Ideal.ofList f]
          MvPolynomial.monomial d 1) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularCanonicalMap R M f
          (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList f]
            MvPolynomial.monomial d 1) := by
  sorry

/-- The canonical graded map is always surjective. -/
theorem quasiRegularCanonicalMap_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    Function.Surjective (quasiRegularCanonicalMap R M f) := by
  sorry

/-! ## Definition and basic properties -/

/-- A sequence is `M`-quasi-regular when the canonical graded map is an isomorphism. -/
def IsMQuasiRegular
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : Prop :=
  Function.Bijective (quasiRegularCanonicalMap R M f)

/-- A sequence is quasi-regular when it is `R`-quasi-regular on the regular module. -/
def IsQuasiRegular
    (R : Type u) [CommRing R] (f : List R) : Prop :=
  IsMQuasiRegular R R f

/-- The isomorphism represented by an `M`-quasi-regular sequence. -/
noncomputable def quasiRegularCanonicalEquiv
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : IsMQuasiRegular R M f) :
    quasiRegularSource R M f ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  LinearEquiv.ofBijective (quasiRegularCanonicalMap R M f) hf

/- The definition is independent of the ordering of the sequence. -/
theorem isMQuasiRegular_iff_of_perm
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : List R} (hfg : f.Perm g) :
    IsMQuasiRegular R M f ↔ IsMQuasiRegular R M g := by
  sorry

/- The regular-sequence comparison from Lemma 69.3. -/
theorem isMQuasiRegular_of_isRegular
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (hf : RingTheory.Sequence.IsRegular M f) :
    IsMQuasiRegular R M f := by
  sorry

theorem isQuasiRegular_of_isRegular
    {R : Type u} [CommRing R] {f : List R}
    (hf : RingTheory.Sequence.IsRegular R f) : IsQuasiRegular R f := by
  exact isMQuasiRegular_of_isRegular hf

/-- In the ring case, quasi-regularity identifies the polynomial ring over the quotient
with the associated graded object. -/
noncomputable def quasiRegular_graded_ring_identification
    {R : Type u} [CommRing R] (f : List R)
    (hf : IsQuasiRegular R f) :
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R R (Ideal.ofList f) := by
  let I := Ideal.ofList f
  let hI : (I • (⊤ : Submodule R R)) = (I : Submodule R R) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let eQ : (R ⧸ (I • (⊤ : Submodule R R))) ≃ₗ[R ⧸ I] (R ⧸ I) := by
    let eR : (R ⧸ (I • (⊤ : Submodule R R))) ≃ₗ[R] (R ⧸ I) :=
      Submodule.quotEquivOfEq _ _ hI
    exact
      { eR with
        map_smul' := by
          intro c x
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
          induction x using Submodule.Quotient.induction_on with
          | _ x => rfl }
  let eSource : quasiRegularSource R R f ≃ₗ[R ⧸ I]
      MvPolynomial (Fin f.length) (R ⧸ I) :=
    eQ.rTensor (MvPolynomial (Fin f.length) (R ⧸ I)) ≪≫ₗ
      TensorProduct.lid (R ⧸ I) (MvPolynomial (Fin f.length) (R ⧸ I))
  exact eSource.symm ≪≫ₗ quasiRegularCanonicalEquiv R R f hf

/-! ## Base change, localization, and truncation -/

theorem isMQuasiRegular_of_flat_baseChange
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) (f : List R)
    (hf : IsMQuasiRegular R M f) :
    IsMQuasiRegular S (S ⊗[R] M) (f.map (algebraMap R S)) := by
  sorry

theorem isMQuasiRegular_in_neighborhood
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (f : List R)
    (hp : IsMQuasiRegular (Localization.AtPrime p)
      (LocalizedModule.AtPrime p M)
      (f.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsMQuasiRegular (Localization (Submonoid.powers g))
        (LocalizedModule (Submonoid.powers g) M)
        (f.map (algebraMap R (Localization (Submonoid.powers g)))) := by
  sorry

theorem isMQuasiRegular_tail
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (hf : IsMQuasiRegular R M f) (i : ℕ) :
    IsMQuasiRegular (R ⧸ Ideal.ofList (f.take i))
      (M ⧸ (Ideal.ofList (f.take i) • (⊤ : Submodule R M)))
      ((f.drop i).map (Ideal.Quotient.mk (Ideal.ofList (f.take i)))) := by
  sorry

theorem isMRegular_of_isMQuasiRegular_of_isLocal
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Nontrivial M) (f : List R)
    (hf : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal R)
    (hq : IsMQuasiRegular R M f) :
    RingTheory.Sequence.IsRegular M f := by
  sorry

/-!
The next source remark defines Koszul-regular and `H₁`-regular sequences using the Koszul
complex and explicitly defers their detailed construction and examples to More on Algebra,
Section 29.  That later chapter is intentionally not imported here: this chapter records the
comparison warning, while its canonical complex and homology API belong to the deferred chapter.
-/

/-! ## The join counterexample -/

inductive joinExampleVariable
  | x
  | y
  | w
  | z (n : ℕ)
deriving DecidableEq

def joinExampleX (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .x

def joinExampleY (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .y

def joinExampleW (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .w

def joinExampleZ (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial joinExampleVariable k := MvPolynomial.X (.z n)

def joinExampleRelations (k : Type u) [CommRing k] :
    Set (MvPolynomial joinExampleVariable k) :=
  {joinExampleY k ^ 2 * joinExampleZ k 0 - joinExampleW k * joinExampleX k} ∪
    Set.range (fun n : ℕ => joinExampleZ k n - joinExampleY k * joinExampleZ k (n + 1))

def joinExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial joinExampleVariable k) := Ideal.span (joinExampleRelations k)

abbrev joinExampleRing (k : Type u) [Field k] :=
  MvPolynomial joinExampleVariable k ⧸ joinExampleIdeal k

def joinExampleXbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleX k)

def joinExampleYbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleY k)

def joinExampleWbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleW k)

def joinExampleZbar (k : Type u) [Field k] (n : ℕ) : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleZ k n)

theorem join_example_defining_relation (k : Type u) [Field k] :
    joinExampleYbar k ^ 2 * joinExampleZbar k 0 =
      joinExampleWbar k * joinExampleXbar k := by
  sorry

theorem join_example_z_relation (k : Type u) [Field k] (n : ℕ) :
    joinExampleZbar k n = joinExampleYbar k * joinExampleZbar k (n + 1) := by
  sorry

theorem join_example_x_is_non_zero_divisor (k : Type u) [Field k] :
    IsSMulRegular (joinExampleRing k) (joinExampleXbar k) := by
  sorry

theorem join_example_ybar_is_quasiRegular (k : Type u) [Field k] :
    IsQuasiRegular (joinExampleRing k ⧸ Ideal.span {joinExampleXbar k})
      [Ideal.Quotient.mk (Ideal.span {joinExampleXbar k}) (joinExampleYbar k)] := by
  sorry

theorem join_example_pair_is_not_quasiRegular (k : Type u) [Field k] :
    ¬ IsQuasiRegular (joinExampleRing k) [joinExampleXbar k, joinExampleYbar k] := by
  sorry

theorem join_example_wbar_mul_xbar_mod_xy_zero (k : Type u) [Field k] :
    Ideal.Quotient.mk (Ideal.span {joinExampleXbar k, joinExampleYbar k})
        (joinExampleWbar k * joinExampleXbar k) = 0 := by
  sorry

theorem join_example_wbar_mod_xy_is_nonzero (k : Type u) [Field k] :
    Ideal.Quotient.mk (Ideal.span {joinExampleXbar k, joinExampleYbar k})
        (joinExampleWbar k) ≠ 0 := by
  sorry

/-! ## Quotienting by the separated part -/

abbrev quasiRegularSeparatedRing
    {R : Type u} [CommRing R] (I : Ideal R) :=
  R ⧸ Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I

abbrev quasiRegularSeparatedModule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :=
  M ⧸ Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule (M := M) I

theorem quasiRegularSeparatedModule_is_torsion
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Module.IsTorsionBySet R (quasiRegularSeparatedModule (M := M) I)
      (Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I) := by
  sorry

@[instance_reducible]
noncomputable def quasiRegularSeparatedModuleModule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Module (quasiRegularSeparatedRing I) (quasiRegularSeparatedModule (M := M) I) :=
  (quasiRegularSeparatedModule_is_torsion I).module

theorem isMQuasiRegular_iff_separated
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    let I := Ideal.ofList f
    letI := quasiRegularSeparatedModuleModule (M := M) I
    IsMQuasiRegular R M f ↔
      IsMQuasiRegular (quasiRegularSeparatedRing I)
        (quasiRegularSeparatedModule (M := M) I)
        (f.map (Ideal.Quotient.mk
          (Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I))) := by
  sorry

end

end Formalization.Books.Algebra.Unit69
