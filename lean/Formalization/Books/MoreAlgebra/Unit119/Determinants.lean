import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Algebra.Unit55.KGroups
import Formalization.Books.MoreAlgebra.Unit118.PicardGroups

set_option genSizeOf false

/-!
# More on Algebra, Chapter 119: Determinants

The determinant line is represented by the canonical annihilator submodule in
the exterior algebra.  This is the source's intrinsic description, and avoids
making a product decomposition of the ring part of the definition.  The
decomposition and rank-one assertions, determinant maps, exact-sequence
compatibilities, and the induced map to the Picard group are recorded below.
-/

namespace Formalization.Books.MoreAlgebra.Unit119

open CategoryTheory
open Formalization.Books.Algebra.Unit13
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Rank decomposition and the determinant line -/

/-- Equality of the rank-at-prime functions of two modules. -/
def SameRankAtPrimes
    (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Prop :=
  Module.rankAtStalk (R := R) M = Module.rankAtStalk (R := R) N

/-- A linear equivalence identifies the rank-at-prime functions. -/
theorem sameRankAtPrimes_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    SameRankAtPrimes R M N := by
  simpa [SameRankAtPrimes] using Module.rankAtStalk_eq_of_equiv e

@[simp]
theorem sameRankAtPrimes_refl
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    SameRankAtPrimes R M M :=
  rfl

abbrev componentProductRing
    (S : Fin n → CommRingCat.{u}) := ∀ i, (S i : Type u)

abbrev componentProductModule
    (S : Fin n → CommRingCat.{u})
    (P : ∀ i, ModuleCat.{v} (S i)) := ∀ i, (P i : Type v)

/-- The product decomposition used in the source's first construction.

The module equivalence is interpreted with the scalar action transported
along `ringEquiv`; each component has the indicated finite locally free rank.
-/
structure RankProductDecomposition
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] where
  t : ℕ
  componentRing : Fin (t + 1) → CommRingCat.{u}
  ringEquiv : R ≃+* componentProductRing componentRing
  componentModule : ∀ i, ModuleCat.{v} (componentRing i)
  componentRank : ∀ i,
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank
      (componentRing i) (componentModule i) i
  moduleEquiv :
    letI : Module R (componentProductModule componentRing componentModule) :=
      Module.compHom _ ringEquiv.toRingHom
    Nonempty
      (M ≃ₗ[R] componentProductModule componentRing componentModule)

/-- The product of the top exterior powers in a rank decomposition. -/
abbrev rankProductDeterminant
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (D : RankProductDecomposition R M) : Type max u v :=
  ∀ i, exteriorPower (D.componentRing i) (D.componentModule i) i

/-- Every finite projective module admits the source's rank-product decomposition. -/
theorem exists_rankProductDecomposition
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Nonempty (RankProductDecomposition R M) := by
  /-
  Shepherd roadmap:
  * Work in universes `R : Type u`, `M : Type v`.  From
    `Module.isLocallyConstant_rankAtStalk` in
    `Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean` (the required finite-presentation and flat
    instances follow from finite projectivity) and `IsLocallyConstant.range_finite` in
    `Mathlib/Topology/LocallyConstant/Basic.lean`, choose `t` bounding the finite image of
    `Module.rankAtStalk (R := R) M`.
  * For each `i : Fin (t + 1)`, take the clopen fibre where the rank is `i`.  Convert these fibres
    to idempotents with `PrimeSpectrum.isIdempotentElemEquivClopens` from
    `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`; prove that they form
    `CompleteOrthogonalIdempotents`.  Empty fibres are represented by the zero idempotent.
  * Put `componentRing i := CommRingCat.of (R ⧸ Ideal.span {1 - e i})`.  The map
    `RingHom.pi (fun i => Ideal.Quotient.mk (Ideal.span {1 - e i}))` is bijective by
    `CompleteOrthogonalIdempotents.bijective_pi` in `Mathlib/RingTheory/Idempotents.lean`; turn it
    into `ringEquiv` with `RingEquiv.ofBijective`.
  * Put the `i`th component module equal to scalar extension of `M` to that quotient.  The usual
    complete-idempotent map `m \mapsto (1 \otimes m)` and its sum-of-components inverse give the
    required `moduleEquiv` over `R` (with the target action explicitly
    `Module.compHom _ ringEquiv.toRingHom`).
  * Finally unfold `FiniteLocallyFreeOfRank` from
    `Formalization/Books/Algebra/Unit78/FiniteProjectiveModules.lean`.  On the `i`th clopen fibre,
    `Module.rankAtStalk_isBaseChange` and the defining fibre equality give constant rank `i`; use
    the finite-projective characterization/local freeness API in that file to build
    `componentRank i`.  Assemble the structure and wrap it in `Nonempty.intro`.
  -/
  sorry

/-- The determinant module as the annihilator of the positive-degree
generators in the exterior algebra.  It is the intrinsic form of the
product of the top exterior powers in the source's decomposition. -/
def determinantModule
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule R (exteriorAlgebra R M) where
  carrier := {x | ∀ m : M, ExteriorAlgebra.ι R m * x = 0}
  zero_mem' := by
    intro m
    simp
  add_mem' := by
    intro x y hx hy m
    rw [mul_add, hx m, hy m, add_zero]
  smul_mem' := by
    intro r x hx m
    calc
      ExteriorAlgebra.ι R m * (r • x) =
          (algebraMap R (exteriorAlgebra R M) r) *
            (ExteriorAlgebra.ι R m * x) := by
        rw [Algebra.smul_def, ← mul_assoc,
          ← Algebra.commutes r (ExteriorAlgebra.ι R m), mul_assoc]
      _ = 0 := by rw [hx m, mul_zero]

@[simp]
theorem mem_determinantModule_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : exteriorAlgebra R M) :
    x ∈ determinantModule R M ↔
      ∀ m : M, ExteriorAlgebra.ι R m * x = 0 :=
  Iff.rfl

/-- The intrinsic determinant line agrees with the product construction in a
rank decomposition. -/
theorem determinantModule_equiv_rankProduct
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (D : RankProductDecomposition R M) :
    letI : Module R (rankProductDeterminant D) :=
      Module.compHom _ D.ringEquiv.toRingHom
    Nonempty
      (determinantModule R M ≃ₗ[R] rankProductDeterminant D) := by
  /-
  Shepherd roadmap:
  * First prove a private fixed-rank helper over a ring `A`: if `P` is finite locally free of rank
    `n`, the inclusion `exteriorPower A P n \hookrightarrow exteriorAlgebra A P` has image exactly
    `determinantModule A P`.  Check this after the basic-open cover in
    `FiniteLocallyFreeOfRank`; use `(algebra_localization_iso S).2.1` from
    `Formalization/Books/Algebra/Unit13/TensorAlgebra.lean` to commute exterior algebra with
    localization.
  * In the localized free calculation choose the `Fin n` basis, expand with
    `Module.Basis.ExteriorAlgebra` / `finite_free_exterior_algebra_basis` and use
    `ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint` plus
    `ExteriorAlgebra.ιMulti_span` (`Mathlib/LinearAlgebra/ExteriorAlgebra/{Basic,Grading}.lean`).
    The simultaneous annihilator of every degree-one basis vector is precisely the coefficient of
    the full `Finset.univ`, i.e. `exteriorPower A P n`.
  * Apply that helper to every `D.componentModule i`, using `D.componentRank i`, and take the finite
    product of the resulting equivalences.  Separately transport `determinantModule R M` along
    `D.moduleEquiv.some` and `D.ringEquiv`; extensionality and
    `ExteriorAlgebra.map_apply_ι` show that the annihilator condition is preserved componentwise.
  * Compose those two equivalences.  State the intermediate product module with the explicit action
    `Module.compHom _ D.ringEquiv.toRingHom`; this avoids asking definitional equality to identify
    the transported scalar actions.  Return the composite inside `Nonempty`.
  -/
  sorry

/-- The determinant line is finite locally free of rank one. -/
theorem determinantModule_finiteLocallyFree_rank_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank
      R (determinantModule R M) 1 := by
  /-
  Shepherd roadmap:
  * Choose `D` from `exists_rankProductDecomposition (R := R) (M := M)` and choose the equivalence
    from `determinantModule_equiv_rankProduct D`.
  * Prove componentwise that `exteriorPower (D.componentRing i) (D.componentModule i) i` is finite
    locally free of rank one.  On each basic open from `D.componentRank i`, transport the standard
    basis through `Module.Basis.exteriorPower` in
    `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`; `Set.powersetCard (Fin i) i` is a singleton,
    so use `Finsupp.uniqueLinearEquiv` to identify the top exterior power with one copy of the
    localized ring.
  * Combine these component covers through `D.ringEquiv` to obtain the defining basic-open cover of
    `rankProductDeterminant D` of rank `1`.  Then transport that cover back along the chosen linear
    equivalence.  Keep the transported `Module R (rankProductDeterminant D)` instance named
    explicitly as in `determinantModule_equiv_rankProduct`.
  * Finish by folding `Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank`; no rank-product
    decomposition should be unfolded during the local basis calculation.
  -/
  sorry

/-- The determinant line is an invertible module. -/
theorem determinantModule_invertible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.Invertible R (determinantModule R M) := by
  /-
  Shepherd roadmap:
  * Obtain `hdet : FiniteLocallyFreeOfRank R (determinantModule R M) 1` from
    `determinantModule_finiteLocallyFree_rank_one` with explicit `(R := R) (M := M)`.
  * Apply the forward implication of
    `finiteLocallyFreeOfRank_one_iff_invertible` from
    `Formalization/Books/MoreAlgebra/Unit118/PicardGroups.lean` to `hdet`.
  * This is a direct interface conversion; do not unfold either `determinantModule` or
    `Module.Invertible` here.
  -/
  sorry

/-! ## Determinant maps -/

/-- The exterior-algebra map induced by a same-rank map restricts to the
determinant modules. -/
theorem determinantMap_mem
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (h : SameRankAtPrimes R M N)
    (x : determinantModule R M) :
    exteriorAlgebraMap f x ∈ determinantModule R N := by
  /-
  Shepherd roadmap:
  * Prove a private functoriality helper using rank-product decompositions for `M` and `N`, refined
    to the same clopen rank partition via `h : Module.rankAtStalk M = Module.rankAtStalk N`.
    Under `determinantModule_equiv_rankProduct`, the map is the product of
    `exteriorPower.map i f_i`; hence it carries each top exterior power to the top exterior power.
  * For the component calculation use `exteriorPower.map_apply_ιMulti` and
    `ExteriorAlgebra.map_apply_ι` from
    `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean` and
    `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.  Do not try to lift an arbitrary `n : N`
    through `f`: `f` is not assumed surjective, and that approach cannot prove the membership goal.
  * Transport the componentwise result back through the ring/module product equivalences.  Then
    unfold only `mem_determinantModule_iff` to state the result as
    `∀ n, ExteriorAlgebra.ι R n * exteriorAlgebraMap f x = 0` and close it with the transported
    top-degree calculation.
  * Keep `h` as an equality of full rank functions (rather than proving pointwise equalities
    repeatedly); use `congrFun h p` at each component prime.
  -/
  sorry

/-- The determinant map attached to a map between finite projectives of the
same rank at every prime. -/
def determinantMap
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (h : SameRankAtPrimes R M N) :
    determinantModule R M →ₗ[R] determinantModule R N :=
  LinearMap.codRestrict (determinantModule R N)
    ((exteriorAlgebraMap f).toLinearMap.comp
      (determinantModule R M).subtype)
    (fun x => determinantMap_mem f h x)

@[simp]
theorem determinantMap_coe
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (h : SameRankAtPrimes R M N)
    (x : determinantModule R M) :
    (determinantMap f h x : exteriorAlgebra R N) =
      exteriorAlgebraMap f x :=
  rfl

/-- The determinant map of an identity map is the identity. -/
theorem determinantMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (h : SameRankAtPrimes R M M) :
    determinantMap (LinearMap.id : M →ₗ[R] M) h = LinearMap.id := by
  /-
  Shepherd roadmap:
  * Apply `LinearMap.ext` and then `Subtype.ext` to an arbitrary
    `x : determinantModule R M`.
  * Rewrite the coerced left side with `determinantMap_coe`; rewrite the exterior-algebra map with
    `exteriorAlgebraMap_id` from
    `Formalization/Books/Algebra/Unit13/TensorAlgebra.lean`, then use `AlgHom.id_apply`.
  * The proof argument `h` disappears after coercion, so no proof-irrelevance rewrite is needed.
  -/
  sorry

/-- Determinant maps compose. -/
theorem determinantMap_comp
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R P] [Module.Projective R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : SameRankAtPrimes R M N) (hg : SameRankAtPrimes R N P)
    (hcomp : SameRankAtPrimes R M P) :
    determinantMap (g.comp f) hcomp =
      (determinantMap g hg).comp (determinantMap f hf) := by
  /-
  Shepherd roadmap:
  * Apply `LinearMap.ext`, introduce `x : determinantModule R M`, and apply `Subtype.ext` in
    `determinantModule R P`.
  * Use `determinantMap_coe` on the outer map and on both component maps.  The remaining equality in
    `exteriorAlgebra R P` is exactly `congrArg (fun k => k x)` of
    `exteriorAlgebraMap_comp f g` from
    `Formalization/Books/Algebra/Unit13/TensorAlgebra.lean`.
  * Normalize only `LinearMap.comp_apply` and `AlgHom.comp_apply`.  The three rank proofs are erased
    by the subtype coercions, so avoid unfolding `determinantMap`.
  -/
  sorry

/-- An isomorphism of finite projectives induces an isomorphism of determinant
lines. -/
theorem determinantMap_bijective_of_linearEquiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) :
    Function.Bijective
      (determinantMap e.toLinearMap
        (sameRankAtPrimes_of_linearEquiv e)) := by
  /-
  Shepherd roadmap:
  * Use `determinantMap e.symm.toLinearMap (sameRankAtPrimes_of_linearEquiv e.symm)` as a two-sided
    inverse candidate.
  * Apply `determinantMap_comp` to `e.toLinearMap,e.symm.toLinearMap` in both orders; rewrite the
    underlying composites with `LinearEquiv.symm_comp` and `LinearEquiv.comp_symm` from
    `Mathlib/Algebra/Module/Equiv/Defs.lean`, and finish each side with `determinantMap_id`.
  * If the rank-proof arguments do not match syntactically, use `Subsingleton.elim` for the proofs of
    `SameRankAtPrimes`; do not unfold that proposition inside the map equality.
  * Feed the resulting left- and right-inverse identities to
    `Function.bijective_iff_has_inverse.mpr`.  All module universes remain the original independent
    `Type*` levels; no `ULift` is needed.
  -/
  sorry

noncomputable def determinantEquiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) :
    determinantModule R M ≃ₗ[R] determinantModule R N :=
  LinearEquiv.ofBijective
    (determinantMap e.toLinearMap (sameRankAtPrimes_of_linearEquiv e))
    (determinantMap_bijective_of_linearEquiv e)

/-- For an invertible module, the endomorphism ring is canonically the base
ring. -/
noncomputable def determinantEndScalarEquiv
    {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
    [Module.Invertible R L] : Module.End R L ≃+* R :=
  (RingEquiv.ofBijective (Module.toModuleEnd R (S := R) L)
    (Module.Invertible.toModuleEnd_bijective R L)).symm

/-- The scalar by which an endomorphism acts on the determinant line. -/
noncomputable def determinant
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (φ : Module.End R M) : R :=
  letI : Module.Invertible R (determinantModule R M) :=
    determinantModule_invertible (R := R) (M := M)
  determinantEndScalarEquiv
    (determinantMap φ (sameRankAtPrimes_refl (R := R) (M := M)))

/-- The determinant of the identity endomorphism is one. -/
theorem determinant_map_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    determinant (M := M) (LinearMap.id : Module.End R M) = 1 := by
  /-
  Shepherd roadmap:
  * Install the named local instance
    `letI : Module.Invertible R (determinantModule R M) :=
      determinantModule_invertible (R := R) (M := M)` used by `determinant`.
  * Rewrite `determinantMap (LinearMap.id) sameRankAtPrimes_refl` with `determinantMap_id`.
    Proof irrelevance identifies its rank proof with the one accepted by that theorem.
  * Now use `map_one` for the ring equivalence
    `determinantEndScalarEquiv (R := R) (L := determinantModule R M)`.  Its inverse definition means
    the scalar-action endomorphism `LinearMap.id` is sent to `1`; finish with `simpa [determinant]`.
  -/
  sorry

/-- The determinant is multiplicative under composition. -/
theorem determinant_map_mul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (φ ψ : Module.End R M) :
    determinant (φ * ψ) = determinant φ * determinant ψ := by
  /-
  Shepherd roadmap:
  * Name the invertible determinant-line instance exactly as in `determinant_map_one`, and set
    `E := determinantEndScalarEquiv (R := R) (L := determinantModule R M)`.
  * Rewrite multiplication with `Module.End.mul_eq_comp`: `φ * ψ = φ.comp ψ`.  Apply
    `determinantMap_comp ψ φ` with all three rank proofs instantiated by
    `sameRankAtPrimes_refl`; after proof irrelevance this gives
    `determinantMap (φ * ψ) _ = determinantMap φ _ * determinantMap ψ _` in the determinant-line
    endomorphism ring.
  * Rewrite by that equality and apply `E.map_mul`.  Finish with `simpa [determinant, E]`; avoid
    unfolding `determinantEndScalarEquiv`, whose ring-equivalence laws already provide the result.
  -/
  sorry

/-- The multiplicative determinant homomorphism of a finite projective module. -/
noncomputable def determinantMonoidHom
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.End R M →* R where
  toFun := determinant
  map_one' := determinant_map_one
  map_mul' := determinant_map_mul

/-! ## Determinants of exact sequences -/

/-- The defining wedge property of the determinant isomorphism of a short
exact sequence.  It characterizes the canonical map used below: lift the
second factor to the middle exterior algebra, wedge it with the image of the
first factor, and use the quotient map to show independence of the lift. -/
def determinantShortExactIsoSpec
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (γ : determinantModule R M' ⊗[R] determinantModule R M''
      ≃ₗ[R] determinantModule R M) : Prop :=
  ∀ (x' : determinantModule R M') (x'' : determinantModule R M'')
    (y : exteriorAlgebra R M),
    exteriorAlgebraMap g y = (x'' : exteriorAlgebra R M'') →
      ((γ (x' ⊗ₜ[R] x'') : determinantModule R M) : exteriorAlgebra R M) =
        exteriorAlgebraMap f (x' : exteriorAlgebra R M') * y

/-- The ModuleCat short complex associated to a linear exact sequence. -/
def determinantShortExactComplex
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk f g hfg.linearMap_comp_eq_zero

/-- Exactness, injectivity, and surjectivity make the canonical ModuleCat
short complex short exact. -/
theorem determinantShortExactComplex_shortExact
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    (determinantShortExactComplex f g hfg).ShortExact := by
  /-
  Shepherd roadmap:
  * Apply `ModuleCat.shortComplex_shortExact` from
    `Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean` to
    `S := determinantShortExactComplex f g hfg`.
  * Supply `hfg`, `hf`, and `hg`; the `@[simps]` equations for `ShortComplex.moduleCatMk` identify
    `S.f` and `S.g` with the original linear maps.
  * If coercions remain, fill the three structure fields directly using
    `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
    `ModuleCat.mono_iff_injective`, and `ModuleCat.epi_iff_surjective` from the same file.
  -/
  sorry

/-- The determinant isomorphism attached to a short exact sequence of finite
projective modules.  Its construction is the exterior-algebra wedge map from
the source; the declaration exposes the canonical isomorphism as an
interface for later compatibilities. -/
theorem exists_determinantShortExactIso
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Nonempty
      {γ : determinantModule R M' ⊗[R] determinantModule R M''
          ≃ₗ[R] determinantModule R M //
        determinantShortExactIsoSpec f g γ} := by
  /-
  Shepherd roadmap (the specification was audited and is well-formed):
  * Since `M''` is projective and `g` is surjective, choose a linear section
    `s : M'' →ₗ[R] M` from `LinearMap.exists_rightInverse_of_surjective` in
    `Mathlib/Algebra/Module/Projective.lean`, using `LinearMap.range_eq_top_of_surjective g hg`.
    Feed `⟨s, hs⟩` to `hfg.splitSurjectiveEquiv hf` from
    `Mathlib/Algebra/Exact/Basic.lean` to obtain `e : M ≃ₗ[R] M' × M''` with its two compatibility
    equations.
  * Before this theorem, add a small private `determinantModule_prodEquiv` helper.  Define its
    forward map on pure tensors by
    `x' ⊗ₜ x'' \mapsto exteriorAlgebraMap (LinearMap.inl R M' M'') x' *
      exteriorAlgebraMap (LinearMap.inr R M' M'') x''` using `TensorProduct.lift`.
    Prove it is an equivalence by the fixed-rank/product calculation already isolated for
    `determinantModule_equiv_rankProduct`; use `TensorProduct.ext'` for equality on pure tensors.
  * Compose that product equivalence with `determinantEquiv e.symm` (or orient `e` so the composite
    lands in `determinantModule R M`).  This gives the candidate `γ`.
  * Prove the spec first for the chosen lift `exteriorAlgebraMap s x''`, using
    `ExteriorAlgebra.map_comp_map`, the two equations attached to the split equivalence, and
    `ExteriorAlgebra.map_surjective_iff` for the quotient map.
  * Isolate the needed kernel statement as a private helper: for a surjective `g`,
    `RingHom.ker (exteriorAlgebraMap g).toRingHom` is the ideal generated by
    `ExteriorAlgebra.ι R '' LinearMap.ker g`.  Prove it from the universal property
    `ExteriorAlgebra.lift`, using `ExteriorAlgebra.map_surjective_iff`; in the present split case it
    can equivalently be checked after transporting by `e` to the projection `M' × M'' → M''`.
  * For an arbitrary `y` with `exteriorAlgebraMap g y = x''`, the difference
    `y - exteriorAlgebraMap s x''` is in that kernel.  Rewrite `LinearMap.ker g` as
    `LinearMap.range f` using `hfg.linearMap_ker_eq`, then show left multiplication by
    `exteriorAlgebraMap f x'` kills the generated ideal.  Use the fixed-rank/top-power helper from
    `determinantModule_equiv_rankProduct` to expand `x'` into top wedges; commute a range generator
    to the left with repeated `ExteriorAlgebra.ι_add_mul_swap`, where it vanishes by
    `mem_determinantModule_iff`.  Extend this generator calculation to the ideal closure with
    `ExteriorAlgebra.induction` and associativity.
    Thus the candidate satisfies the quantified lift-independence equation.  Return `⟨γ, hγ⟩`
    inside `Nonempty`.
  -/
  sorry

/-- The canonical determinant isomorphism of a short exact sequence. -/
noncomputable def determinantShortExactIso
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    determinantModule R M' ⊗[R] determinantModule R M''
      ≃ₗ[R] determinantModule R M :=
  (Classical.choice (exists_determinantShortExactIso f g hfg hf hg)).1

theorem determinantShortExactIso_spec
    {R : Type u} {M' M M'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    determinantShortExactIsoSpec f g
      (determinantShortExactIso f g hfg hf hg) :=
  (Classical.choice (exists_determinantShortExactIso f g hfg hf hg)).2

/-- Naturality of the determinant isomorphism for a commutative diagram of
short exact sequences with vertical isomorphisms. -/
theorem determinantShortExactIso_natural
    {R : Type u}
    {M' M M'' K' K K'' : Type v} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    [AddCommGroup K'] [Module R K'] [Module.Finite R K'] [Module.Projective R K']
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K]
    [AddCommGroup K''] [Module R K''] [Module.Finite R K'']
    [Module.Projective R K'']
    (f₁ : M' →ₗ[R] M) (g₁ : M →ₗ[R] M'')
    (f₂ : K' →ₗ[R] K) (g₂ : K →ₗ[R] K'')
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂)
    (hf₁ : Function.Injective f₁) (hg₁ : Function.Surjective g₁)
    (hf₂ : Function.Injective f₂) (hg₂ : Function.Surjective g₂)
    (comm₁ : v.toLinearMap.comp f₁ = f₂.comp u.toLinearMap)
    (comm₂ : w.toLinearMap.comp g₁ = g₂.comp v.toLinearMap) :
    determinantShortExactIso f₁ g₁ h₁ hf₁ hg₁ ≪≫ₗ determinantEquiv v =
      (TensorProduct.congr (determinantEquiv u) (determinantEquiv w)) ≪≫ₗ
        determinantShortExactIso f₂ g₂ h₂ hf₂ hg₂ := by
  /-
  Shepherd roadmap:
  * Prove a private uniqueness lemma immediately before this theorem: two linear maps
    `γ₁ γ₂ : det M' ⊗ det M'' →ₗ[R] det M` satisfying `determinantShortExactIsoSpec f g` are equal.
    Use `TensorProduct.ext'`; for `x' ⊗ₜ x''`, choose a lift `y` with
    `exteriorAlgebraMap g y = x''` using `(ExteriorAlgebra.map_surjective_iff).2 hg`, and compare the
    two specification equations.  Apply `Subtype.ext` after comparison in the exterior algebra.
  * Regard both sides of the desired equality as linear maps and invoke that uniqueness lemma for
    the lower sequence `(f₂,g₂)`.  The right side satisfies its spec directly from
    `determinantShortExactIso_spec f₂ g₂ ...`.
  * For the left side, start with `x' : det M'`, `x'' : det M''` and a lower lift `z` of
    `determinantEquiv w x''`.  Pull it back through the algebra equivalence induced by `v`; the
    equation `comm₂` and `exteriorAlgebraMap_comp` show that this is a lift of `x''` for `g₁`.
  * Apply the upper specification, then push the wedge expression through `v`.  Use `comm₁`,
    `exteriorAlgebraMap_comp`, `map_mul`, `determinantMap_coe`, and
    `TensorProduct.congr_tmul` to obtain exactly the lower specification.  Any mismatch between
    rank proofs is resolved with `Subsingleton.elim`.
  * Finish with `LinearEquiv.toLinearMap_injective` (or `LinearEquiv.ext`) after uniqueness.  The
    three module universes all remain `Type v`, matching `TensorProduct.congr` without lifts.
  -/
  sorry

/-! ## Filtrations -/

/-- The copy of `K` regarded as a submodule of `L`. -/
def filtrationSubmoduleInL
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) : Submodule R L :=
  K.comap L.subtype

/-- The inclusion of `K` into `L`. -/
def filtrationKToL
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L) : K →ₗ[R] L :=
  LinearMap.codRestrict L K.subtype (fun x => hKL x.property)

/-- The quotient map in the exact sequence `0 → K → L → L/K → 0`. -/
def filtrationLToQuotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) :
    L →ₗ[R] (L ⧸ filtrationSubmoduleInL K L) :=
  (filtrationSubmoduleInL K L).mkQ

/-- The map `L/K → M/K` induced by the inclusion `L ⊂ M`. -/
def filtrationQuotientInclusion
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) :
    (L ⧸ filtrationSubmoduleInL K L) →ₗ[R] (M ⧸ K) :=
  (filtrationSubmoduleInL K L).mapQ K L.subtype (by
    intro x hx
    exact hx)

/-- The quotient map `M/K → M/L` induced by `K ⊂ L`. -/
def filtrationQuotientProjection
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L) :
    (M ⧸ K) →ₗ[R] (M ⧸ L) :=
  K.mapQ L LinearMap.id (by
    intro x hx
    exact hKL hx)

/-- The determinant square for the filtration `K ⊂ L ⊂ M`.

The two paths are respectively the determinant isomorphisms for
`K ⊂ L ⊂ M` and for `K ⊂ M` together with the induced sequence
`0 → L/K → M/K → M/L → 0`; tensor associativity is made explicit. -/
theorem determinant_filtration
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R K] [Module.Projective R K]
    [Module.Finite R (L ⧸ filtrationSubmoduleInL K L)]
    [Module.Projective R (L ⧸ filtrationSubmoduleInL K L)]
    [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)] :
    ∃ (γKL : determinantModule R K ⊗[R]
          determinantModule R (L ⧸ filtrationSubmoduleInL K L)
            ≃ₗ[R] determinantModule R L)
      (γLM : determinantModule R L ⊗[R] determinantModule R (M ⧸ L)
            ≃ₗ[R] determinantModule R M)
      (γKM : determinantModule R K ⊗[R] determinantModule R (M ⧸ K)
            ≃ₗ[R] determinantModule R M)
      (γquot : determinantModule R (L ⧸ filtrationSubmoduleInL K L) ⊗[R]
          determinantModule R (M ⧸ L) ≃ₗ[R] determinantModule R (M ⧸ K)),
      determinantShortExactIsoSpec
          (filtrationKToL K L hKL) (filtrationLToQuotient K L) γKL ∧
      determinantShortExactIsoSpec L.subtype L.mkQ γLM ∧
      determinantShortExactIsoSpec K.subtype K.mkQ γKM ∧
      determinantShortExactIsoSpec
          (filtrationQuotientInclusion K L)
          (filtrationQuotientProjection K L hKL) γquot ∧
      (TensorProduct.congr γKL
          (LinearEquiv.refl R (determinantModule R (M ⧸ L))) ≪≫ₗ γLM) =
        (TensorProduct.assoc R (determinantModule R K)
          (determinantModule R (L ⧸ filtrationSubmoduleInL K L))
          (determinantModule R (M ⧸ L)) ≪≫ₗ
        TensorProduct.congr
          (LinearEquiv.refl R (determinantModule R K)) γquot ≪≫ₗ γKM) := by
  /-
  Shepherd roadmap:
  * Establish the four concrete short exact sequences first.  For subtype/quotient pairs use
    `LinearMap.exact_subtype_mkQ`, `Submodule.injective_subtype`, and
    `Submodule.mkQ_surjective` from
    `Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean` and
    `Mathlib/LinearAlgebra/Quotient/{Basic,Defs}.lean`.  For the quotient sequence, prove on quotient
    representatives that `filtrationQuotientInclusion` is injective, that
    `filtrationQuotientProjection` is surjective, and that its kernel is the range of the inclusion;
    use `Submodule.ker_mkQ` and `Submodule.Quotient.induction_on`.
  * Install the missing finite/projective instances in dependency order.  Split
    `0 → K → L → L/K → 0` with `Function.Exact.splitSurjectiveEquiv` and projectivity of `L/K` to
    identify `L` with `K × L/K`; then do the same for `M` and for `M/K`.  Transport finiteness and
    projectivity through those equivalences using `Module.Finite.equiv` and
    `Module.Projective.of_equiv'`; use the local `moduleProjective_prod` argument (moved to a private
    helper before this theorem if necessary) for products.
  * Define `γKL`, `γLM`, `γKM`, and `γquot` with `determinantShortExactIso` for the four sequences.
    Their first four conjuncts are exactly `determinantShortExactIso_spec`.
  * For the final equality, apply `TensorProduct.ext_threefold` from
    `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.  On
    `(xK ⊗ₜ xLK) ⊗ₜ xML`, choose compatible exterior-algebra lifts successively and apply the four
    specs.  Both sides coerce to the same triple wedge
    `exteriorAlgebraMap K.subtype xK * yLK * yML`; use `mul_assoc`,
    `TensorProduct.assoc_tmul`, and `Subtype.ext`.
  * This triple-wedge comparison is the associativity coherence not supplied by
    `determinantShortExactIso_natural`; trying to finish only with naturality leaves the parenthesized
    tensor products unrelated.
  -/
  sorry

/-! ## Direct sums and the switch sign -/

/-- A finite product of projective modules is projective. -/
theorem moduleProjective_prod
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N] :
    Module.Projective R (M × N) := by
  /-
  Shepherd roadmap:
  * Model the binary product as a finite direct sum.  Let
    `P : Fin 2 → Type* := Fin.cases M (fun _ => N)` and install the induced additive/module and
    projective instances componentwise.
  * `Module.Projective.directSum` in `Mathlib/Algebra/Module/Projective.lean` gives projectivity of
    `⨁ i, P i`.  Compose `DFinsupp.linearEquivFunOnFintype` with
    `LinearEquiv.piFinTwo` from `Mathlib/LinearAlgebra/Pi.lean` to get a linear equivalence from that
    direct sum to `M × N`.
  * Transport projectivity along its inverse with `Module.Projective.of_equiv'`.  This route handles
    the universe parameters directly and avoids invoking `Projective.of_lifting_property`, whose
    `Small` side condition can otherwise force unnecessary `ULift` bookkeeping.
  -/
  sorry

/-- The determinant isomorphism for the canonical direct-sum exact sequence.
A binary product is the additive direct-sum model used by Mathlib. -/
noncomputable def determinantDirectSumIso
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M''] :
    determinantModule R M' ⊗[R] determinantModule R M''
      ≃ₗ[R] determinantModule R (M' × M'') :=
  letI : Module.Projective R (M' × M'') :=
    moduleProjective_prod (R := R) (M := M') (N := M'')
  determinantShortExactIso
    (LinearMap.inl R M' M'') (LinearMap.snd R M' M'')
    Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective

/-- The canonical direct-sum determinant isomorphism exists. -/
theorem exists_determinantDirectSumIso
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M''] :
    Nonempty
      (determinantModule R M' ⊗[R] determinantModule R M''
        ≃ₗ[R] determinantModule R (M' × M'')) :=
  ⟨determinantDirectSumIso (R := R) (M' := M') (M'' := M'')⟩

/-- The determinant of minus the identity on a tensor product is a unit. -/
theorem determinant_neg_identity_isUnit
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    :
    IsUnit
      (determinant (M := M ⊗[R] N)
        (-(LinearMap.id : Module.End R (M ⊗[R] N)))) := by
  /-
  Shepherd roadmap:
  * Let `φ : Module.End R (M ⊗[R] N) := -LinearMap.id`.  Its underlying function is bijective, with
    itself as inverse; prove the two identities pointwise with `neg_neg`.
  * Convert this to `IsUnit φ` using `Module.End.isUnit_iff` from
    `Mathlib/Algebra/Module/Equiv/Basic.lean`.
  * Apply `IsUnit.map` to `determinantMonoidHom (R := R) (M := M ⊗[R] N)`.  The tensor-product
    finite and projective instances are `Module.Finite.tensorProduct` and
    `Module.Projective.tensorProduct` from
    `Mathlib/RingTheory/TensorProduct/Finite.lean` and
    `Mathlib/Algebra/Module/Projective.lean`.
  * The mapped element is definitionally `determinant φ`; finish with `simpa [φ,
    determinantMonoidHom]` without computing the sign exponent.
  -/
  sorry

/-- The sign unit appearing when the two direct-sum factors are switched. -/
noncomputable def determinantSwitchSign
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    : Rˣ :=
  (determinant_neg_identity_isUnit (R := R) (M := M) (N := N)).unit

/-- The sign-twisted tensor switch on determinant lines. -/
noncomputable def determinantSwitchTensorEquiv
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    determinantModule R M ⊗[R] determinantModule R N
      ≃ₗ[R] determinantModule R N ⊗[R] determinantModule R M :=
  determinantSwitchSign (R := R) (M := M) (N := N) •
    TensorProduct.comm R (determinantModule R M) (determinantModule R N)

/-- The determinant equivalence induced by switching two product factors. -/
noncomputable def determinantProductCommEquiv
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    determinantModule R (M × N) ≃ₗ[R] determinantModule R (N × M) := by
  letI : Module.Projective R (M × N) :=
    moduleProjective_prod (R := R) (M := M) (N := N)
  letI : Module.Projective R (N × M) :=
    moduleProjective_prod (R := R) (M := N) (N := M)
  exact determinantEquiv (LinearEquiv.prodComm R M N)

/-- Switching two direct-sum factors gives the sign-twisted tensor switch. -/
theorem determinant_directSum_switch
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    :
    determinantDirectSumIso (R := R) (M' := M') (M'' := M'') ≪≫ₗ
        determinantProductCommEquiv (R := R) (M := M') (N := M'') =
      determinantSwitchTensorEquiv (R := R) (M := M') (N := M'') ≪≫ₗ
        determinantDirectSumIso (R := R) (M' := M'') (M'' := M') := by
  /-
  Shepherd roadmap:
  * Coerce both sides to linear maps and apply `TensorProduct.ext'`; fix pure determinant tensors
    `x' ⊗ₜ x''`.  Expand the two `determinantDirectSumIso` values with
    `determinantShortExactIso_spec` for `LinearMap.inl`/`LinearMap.snd`, choosing the evident lift
    through `LinearMap.inr`.
  * After `determinantMap_coe` for `LinearEquiv.prodComm`, both sides become the two wedge orders
    `map inl x' * map inr x''` and `map inl x'' * map inr x'` in the exterior algebra of
    `M'' × M'`.
  * Prove a private sign helper on each constant-rank component:
    `x' ∧ x'' = determinantSwitchSign • (x'' ∧ x')`.  Expand local basis wedges with
    `ExteriorAlgebra.ιMulti_mul_ιMulti` and `AlternatingMap.map_perm`; the block permutation has sign
    `(-1)^(rank M' * rank M'')`.
  * Identify that scalar with `determinantSwitchSign` by applying
    `determinantModule_equiv_rankProduct` to `M' ⊗[R] M''`: on a component of ranks `r,s`,
    `Module.rankAtStalk` of the tensor product is `r*s`, and `-LinearMap.id` acts on its top exterior
    power by `(-1)^(r*s)`.  Use `determinantMap_coe` and the definition of
    `determinantEndScalarEquiv` to read off the scalar.
  * Rewrite `determinantSwitchTensorEquiv` on a pure tensor with `TensorProduct.comm_tmul` and the
    scalar-action simp lemma, apply the sign helper, and conclude by `Subtype.ext` and
    `LinearEquiv.toLinearMap_injective`.
  -/
  sorry

/-! ## The switch identity -/

/-- The determinant switch identity `det(1 + ab) = det(1 + ba)`. -/
theorem determinant_switch
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    determinant (M := N)
        ((LinearMap.id : N →ₗ[R] N) + a.comp b) =
      determinant (M := M)
        ((LinearMap.id : M →ₗ[R] M) + b.comp a) := by
  /-
  Shepherd roadmap:
  * First derive a block-diagonal compatibility lemma from
    `determinantShortExactIso_natural` for the direct-sum exact sequence: for endomorphisms `p` of
    `M` and `q` of `N`, determinant of `LinearMap.prodMap p q` is
    `determinant p * determinant q`.  Compare scalar actions on the invertible determinant line via
    `determinantDirectSumIso`; use `determinantEndScalarEquiv` and
    `Module.Invertible.toModuleEnd_bijective` to extract equality of scalars.
  * More generally derive a block-triangular compatibility lemma from the same naturality square:
    the determinant of a triangular block map with diagonal maps `p,q` is
    `determinant p * determinant q`; the off-diagonal block does not enter the induced submodule and
    quotient maps.  Its unit-triangular specialization has determinant `1` by
    `determinant_map_one`.
  * Define the block map `T(m,n) = (m + b n, -a m + n)`.  Verify by `LinearMap.ext` the two right
    eliminations (remembering `Module.End.mul_eq_comp`): composing `T` with
    `U_a(m,n) = (m, a m + n)` gives the upper-triangular map
    `(m,n) \mapsto ((id + b.comp a) m + b n, n)`, while composing it with
    `U_{-b}(m,n) = (m - b n,n)` gives the lower-triangular map
    `(m,n) \mapsto (m, -a m + (id + a.comp b) n)`.
  * Apply `determinant_map_mul` to both identities.  Both `U_a` and `U_{-b}` have determinant `1`,
    and the block-triangular lemma reduces the two results to the two sides of this theorem.
  * If the factor order changes the chosen `M × N` versus `N × M` convention, use
    `determinant_directSum_switch` to conjugate by `LinearEquiv.prodComm`; its sign unit occurs on both
    sides and can be cancelled with `IsUnit.mul_left_cancel` using
    `determinant_neg_identity_isUnit`.  This is the projective-module analogue of
    `Matrix.det_one_add_mul_comm` in
    `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`; that matrix theorem cannot be applied
    directly because neither module is assumed free.
  -/
  sorry

/-! ## The determinant map on K₀ -/

/-- The Picard class represented by the determinant of a finite projective
presentation. -/
noncomputable def determinantClassOfPresentation
    {R : Type u} [CommRing R]
    (P : Formalization.Books.Algebra.Unit55.FiniteProjectivePresentation R) :
    Additive (CommRing.Pic R) :=
  letI : Module.Invertible R
      (determinantModule R P.presentation.module) :=
    determinantModule_invertible (R := R) (M := P.presentation.module)
  Additive.ofMul (CommRing.Pic.mk R (determinantModule R P.presentation.module))

/-- The determinant map on the free abelian group of projective generators. -/
def determinantKZeroFree
    {R : Type u} [CommRing R] :
    Formalization.Books.Algebra.Unit55.KZeroFree R →+
      Additive (CommRing.Pic R) :=
  FreeAbelianGroup.lift (fun P => determinantClassOfPresentation P)

/-- Exact-sequence relations are respected by the determinant classes. -/
theorem determinantKZeroFree_respects_relations
    {R : Type u} [CommRing R] :
    Formalization.Books.Algebra.Unit55.kZeroCon R ≤
      AddCon.ker (determinantKZeroFree (R := R)) := by
  /-
  Shepherd roadmap (the additive/Picard interface was audited and needs no statement change):
  * Follow `kZeroFreeToKPrime_respects_relations` in
    `Formalization/Books/Algebra/Unit55/KGroups.lean`: start with
    `refine AddCon.addConGen_le.2 ?_` and
    `rintro x y ⟨S, rfl, rfl⟩`, where
    `S : FiniteProjectiveShortExact R`.
  * Simplify `FreeAbelianGroup.lift` on the three generators.  After unfolding only
    `determinantClassOfPresentation`, change the additive target equality to the multiplicative
    Picard equality
    `Pic.mk R (det middle) = Pic.mk R (det left) * Pic.mk R (det right)`; `Additive.ofMul`
    definitionally turns `+` into `*`.
  * Obtain `γ` from `exists_determinantShortExactIso S.leftToMiddle S.middleToRight
    S.exact S.left_injective S.middle_surjective`.  The corresponding finite/projective instances
    are supplied by `FiniteProjectivePresentation.finite` and `.isProjective` in `Unit55/KGroups`.
  * Use `CommRing.Pic.mk_eq_mk_iff` from `Mathlib/RingTheory/PicardGroup.lean` with `γ.symm` to replace
    the middle determinant class by the class of the tensor product.  Finish with
    `picard_class_tensor` from
    `Formalization/Books/MoreAlgebra/Unit118/PicardGroups.lean`.
  * The subtype proof that `γ` satisfies the wedge spec is not needed for this relation; only its
    linear equivalence field is used.
  -/
  sorry

/-- The determinant homomorphism from K₀ to the additive form of the Picard
group. -/
noncomputable def determinantKZero
    {R : Type u} [CommRing R] :
    Formalization.Books.Algebra.Unit55.KZero R →+
      Additive (CommRing.Pic R) :=
  (Formalization.Books.Algebra.Unit55.kZeroCon R).lift
    (determinantKZeroFree (R := R))
    (determinantKZeroFree_respects_relations (R := R))

@[simp]
theorem determinantKZero_apply_presentation
    {R : Type u} [CommRing R]
    (P : Formalization.Books.Algebra.Unit55.FiniteProjectivePresentation R) :
    determinantKZero (R := R)
        (Formalization.Books.Algebra.Unit55.kZeroClassOfPresentation P) =
      determinantClassOfPresentation P := by
  /-
  Shepherd roadmap:
  * Copy the quotient computation pattern of `kZeroToKPrime_apply_class` in
    `Formalization/Books/Algebra/Unit55/KGroups.lean`.
  * Change the left side to
    `determinantKZeroFree (R := R)
      (Formalization.Books.Algebra.Unit55.kZeroGenerator P)` using the defining reduction rule for
    `AddCon.lift` on `(kZeroCon R).mk'`.
  * Unfold `determinantKZeroFree` and `kZeroGenerator`; close with
    `FreeAbelianGroup.lift_apply_of` from `Mathlib/GroupTheory/FreeAbelianGroup.lean`.  The result is definitionally
    `determinantClassOfPresentation P`, so a focused
    `simp [determinantKZero, determinantKZeroFree,
      Formalization.Books.Algebra.Unit55.kZeroClassOfPresentation,
      Formalization.Books.Algebra.Unit55.kZeroGenerator]` should suffice.
  -/
  sorry

/-- On the class of a finite projective module, the K₀ determinant map is the
class of its determinant line. -/
theorem determinantKZero_apply_module
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    determinantKZero (R := R)
        (Formalization.Books.Algebra.Unit55.kZeroClass (R := R) (M := M)) =
      (letI : Module.Invertible R (determinantModule R M) :=
        determinantModule_invertible (R := R) (M := M)
       Additive.ofMul (CommRing.Pic.mk R (determinantModule R M))) := by
  /-
  Shepherd roadmap:
  * Unfold `Formalization.Books.Algebra.Unit55.kZeroClass` just enough to name
    `P := Classical.choose (exists_finite_projective_presentation (R := R) (M := M))` and
    `e := (Classical.choose_spec ...).some : P.presentation.module ≃ₗ[R] M`.
  * Rewrite the K₀ value with `determinantKZero_apply_presentation P`; the left side is now
    `determinantClassOfPresentation P`.
  * Unfold `determinantClassOfPresentation` and change the equality of `Additive` values to
    `CommRing.Pic.mk R (determinantModule R P.presentation.module) =
      CommRing.Pic.mk R (determinantModule R M)`.
  * Apply `CommRing.Pic.mk_eq_mk_iff.mpr` from
    `Mathlib/RingTheory/PicardGroup.lean` with the equivalence `determinantEquiv e`.  The source
    finite/projective instances are the presentation instances from `Unit55/KGroups.lean`; the
    target instances are the theorem hypotheses.
  * Local `Module.Invertible` instances built by `determinantModule_invertible` may contain different
    proof terms, but they are propositions; use `Subsingleton.elim` only if elaboration does not
    identify them after the `change`.
  -/
  sorry

end

end Formalization.Books.MoreAlgebra.Unit119
