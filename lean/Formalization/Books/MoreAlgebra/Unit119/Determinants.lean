import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Formalization.Books.Algebra.Unit55.KGroups
import Formalization.Books.MoreAlgebra.Unit118.PicardGroups

set_option genSizeOf false
set_option linter.all false

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
    (P : ∀ i, ModuleCat.{u} (S i)) := ∀ i, (P i : Type u)

/-- The product decomposition used in the source's first construction.

The module equivalence is interpreted with the scalar action transported
along `ringEquiv`; each component has the indicated finite locally free rank.
-/
structure RankProductDecomposition
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] where
  t : ℕ
  componentRing : Fin (t + 1) → CommRingCat.{u}
  ringEquiv : R ≃+* componentProductRing componentRing
  componentModule : ∀ i, ModuleCat.{u} (componentRing i)
  componentRank : ∀ i,
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank
      (componentRing i) (componentModule i) i
  moduleEquiv :
    letI : Module R (componentProductModule componentRing componentModule) :=
      Module.compHom _ ringEquiv.toRingHom
    Nonempty
      (M ≃ₗ[R] componentProductModule componentRing componentModule)

/-- Every finite projective module admits the source's rank-product decomposition. -/
theorem exists_rankProductDecomposition
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Nonempty (RankProductDecomposition R M) := by
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

/-- The determinant line is finite locally free of rank one. -/
theorem determinantModule_finiteLocallyFree_rank_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank
      R (determinantModule R M) 1 := by
  sorry

/-- The determinant line is an invertible module. -/
theorem determinantModule_invertible
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.Invertible R (determinantModule R M) := by
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
    ExteriorAlgebra.map f x ∈ determinantModule R N := by
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
    ((ExteriorAlgebra.map f).toLinearMap.comp
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
      ExteriorAlgebra.map f x :=
  rfl

/-- The determinant map of an identity map is the identity. -/
theorem determinantMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (h : SameRankAtPrimes R M M) :
    determinantMap (LinearMap.id : M →ₗ[R] M) h = LinearMap.id := by
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
  sorry

/-- The determinant is multiplicative under composition. -/
theorem determinant_map_mul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (φ ψ : Module.End R M) :
    determinant (φ * ψ) = determinant φ * determinant ψ := by
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
      (determinantModule R M' ⊗[R] determinantModule R M''
        ≃ₗ[R] determinantModule R M) := by
  sorry

/-- A chosen representative of the canonical determinant isomorphism of a
short exact sequence. -/
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
  Classical.choice (exists_determinantShortExactIso f g hfg hf hg)

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
    [Module.Finite R M] [Module.Projective R M]
    (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R K] [Module.Projective R K]
    [Module.Finite R L] [Module.Projective R L]
    [Module.Finite R (L ⧸ filtrationSubmoduleInL K L)]
    [Module.Projective R (L ⧸ filtrationSubmoduleInL K L)]
    [Module.Finite R (M ⧸ K)] [Module.Projective R (M ⧸ K)]
    [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)]
    (hKL_exact :
      Function.Exact (filtrationKToL K L hKL) (filtrationLToQuotient K L))
    (hKL_injective : Function.Injective (filtrationKToL K L hKL))
    (hKL_surjective : Function.Surjective (filtrationLToQuotient K L))
    (hLM_exact : Function.Exact L.subtype L.mkQ)
    (hLM_injective : Function.Injective L.subtype)
    (hLM_surjective : Function.Surjective L.mkQ)
    (hKM_exact : Function.Exact K.subtype K.mkQ)
    (hKM_injective : Function.Injective K.subtype)
    (hKM_surjective : Function.Surjective K.mkQ)
    (hquot_exact :
      Function.Exact (filtrationQuotientInclusion K L)
        (filtrationQuotientProjection K L hKL))
    (hquot_injective : Function.Injective (filtrationQuotientInclusion K L))
    (hquot_surjective : Function.Surjective (filtrationQuotientProjection K L hKL)) :
    let γKL := determinantShortExactIso
      (filtrationKToL K L hKL) (filtrationLToQuotient K L)
      hKL_exact hKL_injective hKL_surjective
    let γLM := determinantShortExactIso L.subtype L.mkQ
      hLM_exact hLM_injective hLM_surjective
    let γKM := determinantShortExactIso K.subtype K.mkQ
      hKM_exact hKM_injective hKM_surjective
    let γquot := determinantShortExactIso
      (filtrationQuotientInclusion K L)
      (filtrationQuotientProjection K L hKL)
      hquot_exact hquot_injective hquot_surjective
    (TensorProduct.congr γKL
        (LinearEquiv.refl R (determinantModule R (M ⧸ L))) ≪≫ₗ γLM) =
      (TensorProduct.assoc R (determinantModule R K)
        (determinantModule R (L ⧸ filtrationSubmoduleInL K L))
        (determinantModule R (M ⧸ L)) ≪≫ₗ
      TensorProduct.congr
        (LinearEquiv.refl R (determinantModule R K)) γquot ≪≫ₗ γKM) := by
  sorry

/-! ## Direct sums and the switch sign -/

/-- The determinant isomorphism for the canonical direct-sum exact sequence.
A binary product is the additive direct-sum model used by Mathlib. -/
theorem exists_determinantDirectSumIso
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M''] :
    Nonempty
      (determinantModule R M' ⊗[R] determinantModule R M''
        ≃ₗ[R] determinantModule R (M' × M'')) := by
  sorry

noncomputable def determinantDirectSumIso
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M''] :
    determinantModule R M' ⊗[R] determinantModule R M''
      ≃ₗ[R] determinantModule R (M' × M'') :=
  Classical.choice (exists_determinantDirectSumIso (R := R) (M' := M') (M'' := M''))

/-- The determinant of minus the identity on a tensor product is a unit. -/
theorem determinant_neg_identity_isUnit
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R (M ⊗[R] N)] [Module.Projective R (M ⊗[R] N)] :
    IsUnit
      (determinant (M := M ⊗[R] N)
        (-(LinearMap.id : Module.End R (M ⊗[R] N)))) := by
  sorry

/-- The sign unit appearing when the two direct-sum factors are switched. -/
noncomputable def determinantSwitchSign
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R (M ⊗[R] N)] [Module.Projective R (M ⊗[R] N)] : Rˣ :=
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

/-- Switching two direct-sum factors gives the sign-twisted tensor switch. -/
theorem determinant_directSum_switch
    {R M' M'' : Type u} [CommRing R]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    [Module.Projective R M'']
    [Module.Finite R (M' × M'')] [Module.Projective R (M' × M'')]
    [Module.Finite R (M'' × M')] [Module.Projective R (M'' × M')]
    [Module.Finite R (M' ⊗[R] M'')] [Module.Projective R (M' ⊗[R] M'')] :
    determinantDirectSumIso (R := R) (M' := M') (M'' := M'') ≪≫ₗ
        determinantEquiv (LinearEquiv.prodComm R M' M'') =
      determinantSwitchTensorEquiv (R := R) (M := M') (N := M'') ≪≫ₗ
        determinantDirectSumIso (R := R) (M' := M'') (M'' := M') := by
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
  sorry

end

end Formalization.Books.MoreAlgebra.Unit119
