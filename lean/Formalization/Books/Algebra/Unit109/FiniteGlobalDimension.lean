import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit85.ProjectiveModulesLocalRing
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Commutative Algebra, Chapter 109: Rings of finite global dimension

The source's projective dimensions are represented by Mathlib's canonical
CategoryTheory.HasProjectiveDimensionLE interface. Infinite projective
resolutions are represented by CategoryTheory.ProjectiveResolution; a
projective syzygy at the end of a resolution is the source-facing encoding of
a finite projective resolution.
-/

namespace Formalization.Books.Algebra.Unit109

open CategoryTheory
open CategoryTheory.Limits
open Module
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Algebra.Unit09

universe u v

noncomputable section

/-! ## Schanuel's lemma -/

/- The source displays maps on products of modules. This is the canonical
   product-module map associated to two linear maps. -/

/-- The product of two linear maps. -/
def productLinearMap {R M M' N N' : Type u} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') : M × N →ₗ[R] M' × N' :=
  { toFun := fun x => (f x.1, g x.2)
    map_add' := by
      intro x y
      ext <;> simp
    map_smul' := by
      intro r x
      ext <;> simp }

/- The map from a product into a common codomain, as used by the two maps
   `(p₁, 0)` and `(0, p₂)` in Schanuel's diagram. -/

/-- Add two linear maps after projecting from a product. -/
def productToCommonLinearMap {R M N P : Type u} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] P) (g : N →ₗ[R] P) : M × N →ₗ[R] P :=
  { toFun := fun x => f x.1 + g x.2
    map_add' := by
      intro x y
      simp [add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro r x
      simp }

/-- The unbundled-module form of a short exact sequence
0 → K → P → M → 0. -/
def IsShortExactLinearSequence {R K P M : Type u} [Semiring R]
    [AddCommMonoid K] [AddCommMonoid P] [AddCommMonoid M]
    [Module R K] [Module R P] [Module R M]
    (c : K →ₗ[R] P) (p : P →ₗ[R] M) : Prop :=
  Function.Exact c p ∧ Function.Injective c ∧ Function.Surjective p

/-- The commutative diagram in the precise form of Schanuel's lemma.

The two displayed vertical arrows are bundled as linear equivalences, and the
two square-commutativity conditions use the product maps into products and the
maps from products into the common codomain. -/
def SchanuelDiagram {R K L P₁ P₂ M : Type u} [Semiring R]
    [AddCommMonoid K] [AddCommMonoid L] [AddCommMonoid P₁] [AddCommMonoid P₂]
    [AddCommMonoid M] [Module R K] [Module R L] [Module R P₁] [Module R P₂]
    [Module R M] (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M) : Prop :=
  ∃ e₁ : (K × P₂) ≃ₗ[R] (P₁ × L),
    ∃ e₂ : (P₁ × P₂) ≃ₗ[R] (P₁ × P₂),
      e₂.toLinearMap.comp (productLinearMap c₁ (LinearMap.id : P₂ →ₗ[R] P₂)) =
          (productLinearMap (LinearMap.id : P₁ →ₗ[R] P₁) c₂).comp e₁.toLinearMap ∧
        productToCommonLinearMap p₁ (0 : P₂ →ₗ[R] M) =
          (productToCommonLinearMap (0 : P₁ →ₗ[R] M) p₂).comp e₂.toLinearMap

/-- Schanuel's lemma, including the commutative diagram with isomorphic
vertical arrows displayed in the source. -/
theorem schanuel_lemma {R K L P₁ P₂ M : Type u} [Ring R]
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup P₁] [AddCommGroup P₂]
    [AddCommGroup M] [Module R K] [Module R L] [Module R P₁] [Module R P₂]
    [Module R M] [Module.Projective R P₁] [Module.Projective R P₂]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (h₁ : IsShortExactLinearSequence c₁ p₁)
    (h₂ : IsShortExactLinearSequence c₂ p₂) :
    Nonempty ((K × P₂) ≃ₗ[R] (L × P₁)) ∧
    SchanuelDiagram c₁ p₁ c₂ p₂ := by
  sorry
/-! ## Finite projective dimension and resolutions -/

/- resolutionSyzygy P n is ker(P₀ → M) for n = 0, and
   ker(Pₙ → Pₙ₋₁) for positive n. -/

/-- The nth syzygy of a projective resolution, with the degree-zero
syzygy taken at the augmentation. -/
noncomputable def resolutionSyzygy {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (n : ℕ) : ModuleCat.{u} R :=
  if n = 0 then
    kernel (P.π.f 0)
  else
    kernel (P.complex.d n (n - 1))

/-- A finite projective resolution of length at most d, represented by a
canonical projective resolution whose terminal syzygy is projective. -/
def HasFiniteProjectiveResolutionLE {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  if d = 0 then
    Module.Projective R M
  else
    ∃ P : ProjectiveResolution M,
      Module.Projective R (resolutionSyzygy P (d - 1))

/-- The source's finite-projective-dimension predicate. -/
def HasFiniteProjectiveDimension {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) : Prop :=
  ∃ d : ℕ, HasFiniteProjectiveResolutionLE M d

private noncomputable def resolutionSyzygyShortComplex {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  if h : n = 0 then
      ShortComplex.mk (kernel.ι (P.complex.d 1 0))
      (kernel.lift (P.π.f 0) (P.complex.d 1 0) P.complex_d_comp_π_f_zero) (by
        apply (cancel_mono (kernel.ι (P.π.f 0))).1
        simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])
  else
      ShortComplex.mk (kernel.ι (P.complex.d (n + 1) n))
      (kernel.lift (P.complex.d n (n - 1)) (P.complex.d (n + 1) n) (by simp)) (by
        apply (cancel_mono (kernel.ι (P.complex.d n (n - 1)))).1
        simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])

private theorem resolutionSyzygyShortComplex_exact {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (n : ℕ) :
    (resolutionSyzygyShortComplex P n).ShortExact := by
  classical
  dsimp [resolutionSyzygyShortComplex]
  split_ifs with hn
  · subst n
    have hEpi : Epi (kernel.lift (P.π.f 0) (P.complex.d 1 0)
        P.complex_d_comp_π_f_zero) := P.exact₀.epi_kernelLift
    refine { exact := ?_, mono_f := by infer_instance, epi_g := hEpi }
    apply ShortComplex.exact_of_f_is_kernel
    have hzero : kernel.ι (P.complex.d 1 0) ≫
        kernel.lift (P.π.f 0) (P.complex.d 1 0) P.complex_d_comp_π_f_zero = 0 := by
      apply (cancel_mono (kernel.ι (P.π.f 0))).1
      simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
    exact KernelFork.IsLimit.ofι' (kernel.ι (P.complex.d 1 0)) hzero (by
      intro A f hf
      refine ⟨kernel.lift (P.complex.d 1 0) f ?_, ?_⟩
      · rw [← kernel.lift_ι (P.π.f 0) (P.complex.d 1 0)
          P.complex_d_comp_π_f_zero, ← Category.assoc, hf, zero_comp]
      · simp)
  · have hEpi : Epi (kernel.lift (P.complex.d n (n - 1))
        (P.complex.d (n + 1) n) (by simp)) := by
      have hn1 : n - 1 + 1 = n := by omega
      have hn2 : n - 1 + 2 = n + 1 := by omega
      convert (P.exact_succ (n - 1)).epi_kernelLift using 1 <;> rw [hn1, hn2]
    refine { exact := ?_, mono_f := by infer_instance, epi_g := hEpi }
    apply ShortComplex.exact_of_f_is_kernel
    have hzero : kernel.ι (P.complex.d (n + 1) n) ≫
        kernel.lift (P.complex.d n (n - 1)) (P.complex.d (n + 1) n) (by simp) = 0 := by
      apply (cancel_mono (kernel.ι (P.complex.d n (n - 1)))).1
      simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
    exact KernelFork.IsLimit.ofι' (kernel.ι (P.complex.d (n + 1) n)) hzero (by
      intro A f hf
      refine ⟨kernel.lift (P.complex.d (n + 1) n) f ?_, ?_⟩
      · rw [← kernel.lift_ι (P.complex.d n (n - 1))
          (P.complex.d (n + 1) n) (by simp), ← Category.assoc, hf, zero_comp]
      · simp)

private theorem hasProjectiveDimensionLT_of_ge_explicit {C : Type u}
    [Category C] [Abelian C] (X : C) (n m : ℕ) (h : n ≤ m)
    (hbase : CategoryTheory.HasProjectiveDimensionLT X n) :
    CategoryTheory.HasProjectiveDimensionLT X m := by
  exact @CategoryTheory.hasProjectiveDimensionLT_of_ge C _ _ X n m h hbase

private theorem resolutionSyzygy_bound_down {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    ∀ (n q : ℕ),
      CategoryTheory.HasProjectiveDimensionLT (resolutionSyzygy P n) q →
        CategoryTheory.HasProjectiveDimensionLT (resolutionSyzygy P 0) (q + n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simpa using hq
  | succ n ih =>
      intro q hq
      let S := resolutionSyzygyShortComplex P n
      have hS := resolutionSyzygyShortComplex_exact P n
      have hproj₂ : CategoryTheory.Projective S.X₂ := by
        dsimp [S, resolutionSyzygyShortComplex]
        split_ifs with hn
        · exact P.projective 1
        · exact P.projective (n + 1)
      have hbase : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
      have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ (q + 1) := by
        exact hasProjectiveDimensionLT_of_ge_explicit
          S.X₂ 1 (q + 1) (by omega) hbase
      have hq' : CategoryTheory.HasProjectiveDimensionLT S.X₁ q := by
        by_cases hn : n = 0
        · subst n
          simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy] using hq
        · simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy, hn] using hq
      have htarget : CategoryTheory.HasProjectiveDimensionLT S.X₃ (q + 1) :=
        hS.hasProjectiveDimensionLT_X₃ q hq' hmid
      have hdown_input : CategoryTheory.HasProjectiveDimensionLT
          (resolutionSyzygy P n) (q + 1) := by
        by_cases hn : n = 0
        · subst n
          simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy] using htarget
        · simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy, hn] using htarget
      have hdown := ih (q + 1) hdown_input
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdown

private theorem resolutionSyzygy_bound_up {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (d n : ℕ)
    (hn : n < d)
    (hbound : CategoryTheory.HasProjectiveDimensionLT M (d + 1)) :
    CategoryTheory.HasProjectiveDimensionLT (resolutionSyzygy P n) (d - n) := by
  induction n with
  | zero =>
      let S := ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0)
        (kernel.condition (P.π.f 0))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_kernel (P.π.f 0)
          mono_f := by infer_instance
          epi_g := by infer_instance }
      have hproj₂ : CategoryTheory.Projective S.X₂ := by
        dsimp [S]
        exact P.projective 0
      have hbase : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
      have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ d := by
        exact hasProjectiveDimensionLT_of_ge_explicit S.X₂ 1 d (by omega) hbase
      have h := hS.hasProjectiveDimensionLT_X₁ d hmid hbound
      simpa [S, resolutionSyzygy, CategoryTheory.HasProjectiveDimensionLE] using h
  | succ n ih =>
      have hn' : n < d := by omega
      have hprev := ih hn'
      let S := resolutionSyzygyShortComplex P n
      have hS := resolutionSyzygyShortComplex_exact P n
      have hproj₂ : CategoryTheory.Projective S.X₂ := by
        dsimp [S, resolutionSyzygyShortComplex]
        split_ifs with hn
        · exact P.projective 1
        · exact P.projective (n + 1)
      have hbase : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
      have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ (d - (n + 1)) := by
        exact hasProjectiveDimensionLT_of_ge_explicit
          S.X₂ 1 (d - (n + 1)) (by omega) hbase
      have hprev' : CategoryTheory.HasProjectiveDimensionLT S.X₃
          ((d - (n + 1)) + 1) := by
        have hdeg : d - (n + 1) + 1 = d - n := by omega
        by_cases hn : n = 0
        · subst n
          simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy, hdeg] using hprev
        · simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy, hn, hdeg] using hprev
      have h := hS.hasProjectiveDimensionLT_X₁ (d - (n + 1)) hmid hprev'
      by_cases hn : n = 0
      · subst n
        simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy] using h
      · simpa [S, resolutionSyzygyShortComplex, resolutionSyzygy, hn] using h

private theorem resolutionSyzygy_projective_succ {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (n : ℕ)
    (hproj : Module.Projective R (resolutionSyzygy P n)) :
    Module.Projective R (resolutionSyzygy P (n + 1)) := by
  let S := resolutionSyzygyShortComplex P n
  have hS := resolutionSyzygyShortComplex_exact P n
  have hproj₂ : CategoryTheory.Projective S.X₂ := by
    dsimp [S, resolutionSyzygyShortComplex]
    split_ifs with hn
    · exact P.projective 1
    · exact P.projective (n + 1)
  have hproj₃ : CategoryTheory.Projective S.X₃ := by
    dsimp [S, resolutionSyzygyShortComplex, resolutionSyzygy]
    split_ifs with hn
    · subst n
      exact (IsProjective.iff_projective _).mp hproj
    · have hproj : CategoryTheory.Projective (resolutionSyzygy P n) :=
        (IsProjective.iff_projective _).mp
          hproj
      simpa [resolutionSyzygy, hn] using hproj
  have hbase₃ : CategoryTheory.HasProjectiveDimensionLT S.X₃ 1 :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₃
  have htarget : CategoryTheory.HasProjectiveDimensionLT S.X₃ 2 := by
    exact hasProjectiveDimensionLT_of_ge_explicit S.X₃ 1 2 (by omega) hbase₃
  have hbase₂ : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
  have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 := by
    exact hbase₂
  have h := hS.hasProjectiveDimensionLT_X₁ 1 hmid htarget
  have hproj₁ : CategoryTheory.Projective S.X₁ :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr h
  have hmodule : Module.Projective R (S.X₁ : Type u) :=
    (IsProjective.iff_projective (S.X₁ : Type u)).mpr hproj₁
  by_cases hn : n = 0
  · subst n
    have hobj : resolutionSyzygy P (0 + 1) = S.X₁ := by
      dsimp [resolutionSyzygy, S, resolutionSyzygyShortComplex]
    rw [hobj]
    exact hmodule
  ·
    have hobj : resolutionSyzygy P (n + 1) = S.X₁ := by
      simp [resolutionSyzygy, S, resolutionSyzygyShortComplex, hn]
    rw [hobj]
    exact hmodule

private theorem resolutionSyzygy_zero_projective_of_projective_module {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M)
    (hprojM : Module.Projective R (M : Type u)) :
    Module.Projective R (resolutionSyzygy P 0 : Type u) := by
  let S := ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0)
    (kernel.condition (P.π.f 0))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel (P.π.f 0)
      mono_f := by infer_instance
      epi_g := by infer_instance }
  have hproj₂ : CategoryTheory.Projective S.X₂ := by
    dsimp [S]
    exact P.projective 0
  have hproj₃ : CategoryTheory.Projective S.X₃ := by
    dsimp [S]
    exact (IsProjective.iff_projective _).mp hprojM
  have hbase₃ : CategoryTheory.HasProjectiveDimensionLT S.X₃ 1 :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₃
  have htarget : CategoryTheory.HasProjectiveDimensionLT S.X₃ 2 := by
    exact hasProjectiveDimensionLT_of_ge_explicit S.X₃ 1 2 (by omega) hbase₃
  have hbase₂ : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
  have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 := by
    exact hbase₂
  have h := hS.hasProjectiveDimensionLT_X₁ 1 hmid htarget
  have hproj₁ : CategoryTheory.Projective S.X₁ :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr h
  have hmodule : Module.Projective R (S.X₁ : Type u) :=
    (IsProjective.iff_projective (S.X₁ : Type u)).mpr hproj₁
  change Module.Projective R (S.X₁ : Type u)
  exact hmodule

private theorem resolutionSyzygy_projective_of_projective_module {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (e : ℕ)
    (hprojM : Module.Projective R (M : Type u)) :
    Module.Projective R (resolutionSyzygy P e : Type u) := by
  induction e with
  | zero => exact resolutionSyzygy_zero_projective_of_projective_module P hprojM
  | succ e ih =>
      exact resolutionSyzygy_projective_succ P e ih

/-- The source-facing assertion that the minimal projective-resolution length
is exactly `d`. -/
def HasProjectiveDimensionExactly {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  CategoryTheory.HasProjectiveDimensionLE M d ∧
    ∀ e : ℕ, e < d → ¬ CategoryTheory.HasProjectiveDimensionLE M e

/-- Finite projective dimension is equivalent to the existence of a finite
canonical projective-dimension bound. -/
theorem hasFiniteProjectiveDimension_iff_exists_projective_dimension_bound
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    HasFiniteProjectiveDimension M ↔
      ∃ d : ℕ, CategoryTheory.HasProjectiveDimensionLE M d := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    by_cases hd0 : d = 0
    · subst d
      rw [HasFiniteProjectiveResolutionLE, if_pos rfl] at hd
      have hprojM : CategoryTheory.Projective M :=
        (IsProjective.iff_projective (M : Type u)).mp hd
      exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mp hprojM
    · rw [HasFiniteProjectiveResolutionLE, if_neg hd0] at hd
      rcases hd with ⟨P, hP⟩
      have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
        (IsProjective.iff_projective _).mp hP
      have hterminal : CategoryTheory.HasProjectiveDimensionLT
          (resolutionSyzygy P (d - 1)) 1 :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hprojP
      have hzero := resolutionSyzygy_bound_down P (d - 1) 1 hterminal
      have hzero' : CategoryTheory.HasProjectiveDimensionLT
          (resolutionSyzygy P 0) d := by
        have hdeg : 1 + (d - 1) = d := by omega
        simpa [hdeg] using hzero
      let S := ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0)
        (kernel.condition (P.π.f 0))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_kernel (P.π.f 0)
          mono_f := by infer_instance
          epi_g := by infer_instance }
      have hproj₂ : CategoryTheory.Projective S.X₂ := by
        dsimp [S]
        exact P.projective 0
      have hbase₂ : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
      have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ (d + 1) := by
        exact hasProjectiveDimensionLT_of_ge_explicit
          S.X₂ 1 (d + 1) (by omega) hbase₂
      have h := hS.hasProjectiveDimensionLT_X₃ d (by simpa [S, resolutionSyzygy] using hzero') hmid
      simpa [S, CategoryTheory.HasProjectiveDimensionLE] using h
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    by_cases hd0 : d = 0
    · subst d
      have hprojM : CategoryTheory.Projective M :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr hd
      have hmoduleM : Module.Projective R (M : Type u) :=
        (IsProjective.iff_projective (M : Type u)).mpr hprojM
      simpa [HasFiniteProjectiveResolutionLE] using hmoduleM
    · rw [HasFiniteProjectiveResolutionLE, if_neg hd0]
      let P : ProjectiveResolution M := ProjectiveResolution.of M
      have hterminal := resolutionSyzygy_bound_up P d (d - 1) (by omega) hd
      have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
        CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr (by
          have hdeg : d - (d - 1) = 1 := by omega
          simpa [hdeg] using hterminal)
      have hmoduleP : Module.Projective R (resolutionSyzygy P (d - 1) : Type u) :=
        (IsProjective.iff_projective _).mpr hprojP
      exact ⟨P, hmoduleP⟩

/-- Finite projective dimension is equivalent to the canonical projective
dimension not being infinite. -/
theorem hasFiniteProjectiveDimension_iff_projectiveDimension_ne_top
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    HasFiniteProjectiveDimension M ↔
      CategoryTheory.projectiveDimension M ≠ ⊤ := by
  rw [hasFiniteProjectiveDimension_iff_exists_projective_dimension_bound,
    CategoryTheory.projectiveDimension_ne_top_iff]

/-- The source's degree bound for an arbitrary projective resolution. -/
def ResolutionHasProjectiveSyzygyAt {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) (d : ℕ) : Prop :=
  if d = 0 then
    Module.Projective R M
  else
    Module.Projective R (resolutionSyzygy P (d - 1))

/-- The four resolution conditions in the source's characterization of
projective dimension. -/
def projectiveDimensionResolutionConditions {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (d : ℕ) : List Prop :=
  [ CategoryTheory.HasProjectiveDimensionLE M d,
    HasFiniteProjectiveResolutionLE M d,
    ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d ]

/-- A projective resolution has a projective syzygy at every degree allowed by
the projective dimension bound. -/
theorem independent_projective_resolution {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (d e : ℕ)
    (hM : HasProjectiveDimensionExactly M d)
    (he : d - 1 ≤ e) (P : ProjectiveResolution M) :
    Module.Projective R (resolutionSyzygy P e) := by
  by_cases hd0 : d = 0
  · subst d
    have hprojM : CategoryTheory.Projective M :=
      (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr hM.1
    have hmoduleM : Module.Projective R (M : Type u) :=
      (IsProjective.iff_projective (M : Type u)).mpr hprojM
    exact resolutionSyzygy_projective_of_projective_module P e hmoduleM
  · have hbound : CategoryTheory.HasProjectiveDimensionLT M (d + 1) := hM.1
    have hterminal := resolutionSyzygy_bound_up P d (d - 1) (by omega) hbound
    have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
      CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr (by
        have hdeg : d - (d - 1) = 1 := by omega
        simpa [hdeg] using hterminal)
    have hmoduleP : Module.Projective R (resolutionSyzygy P (d - 1) : Type u) :=
      (IsProjective.iff_projective _).mpr hprojP
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    induction k with
    | zero => exact hmoduleP
    | succ k ih =>
        exact resolutionSyzygy_projective_succ P (d - 1 + k) (ih (by omega))

/-- The four conditions for a projective resolution are equivalent. -/
theorem projective_dimension_resolution_criteria {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (d : ℕ) :
    List.TFAE (projectiveDimensionResolutionConditions M d) := by
  have hAB : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionLE M d := by
    constructor
    · intro hA
      by_cases hd0 : d = 0
      · subst d
        have hprojM : CategoryTheory.Projective M :=
          (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr hA
        have hmoduleM : Module.Projective R (M : Type u) :=
          (IsProjective.iff_projective (M : Type u)).mpr hprojM
        simpa [HasFiniteProjectiveResolutionLE] using hmoduleM
      · rw [HasFiniteProjectiveResolutionLE, if_neg hd0]
        let P : ProjectiveResolution M := ProjectiveResolution.of M
        have hterminal := resolutionSyzygy_bound_up P d (d - 1) (by omega) hA
        have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
          CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr (by
            have hdeg : d - (d - 1) = 1 := by omega
            simpa [hdeg] using hterminal)
        have hmoduleP : Module.Projective R (resolutionSyzygy P (d - 1) : Type u) :=
          (IsProjective.iff_projective _).mpr hprojP
        exact ⟨P, hmoduleP⟩
    · intro hB
      by_cases hd0 : d = 0
      · subst d
        rw [HasFiniteProjectiveResolutionLE, if_pos rfl] at hB
        exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mp
          ((IsProjective.iff_projective _).mp hB)
      · rw [HasFiniteProjectiveResolutionLE, if_neg hd0] at hB
        rcases hB with ⟨P, hP⟩
        have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
          (IsProjective.iff_projective _).mp hP
        have hterminal : CategoryTheory.HasProjectiveDimensionLT
            (resolutionSyzygy P (d - 1)) 1 :=
          CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hprojP
        have hzero := resolutionSyzygy_bound_down P (d - 1) 1 hterminal
        have hzero' : CategoryTheory.HasProjectiveDimensionLT
            (resolutionSyzygy P 0) d := by
          have hdeg : 1 + (d - 1) = d := by omega
          simpa [hdeg] using hzero
        let S := ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0)
          (kernel.condition (P.π.f 0))
        have hS : S.ShortExact :=
          { exact := ShortComplex.exact_kernel (P.π.f 0)
            mono_f := by infer_instance
            epi_g := by infer_instance }
        have hproj₂ : CategoryTheory.Projective S.X₂ := by
          dsimp [S]
          exact P.projective 0
        have hbase₂ : CategoryTheory.HasProjectiveDimensionLT S.X₂ 1 :=
          CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj₂
        have hmid : CategoryTheory.HasProjectiveDimensionLT S.X₂ (d + 1) := by
          exact hasProjectiveDimensionLT_of_ge_explicit
            S.X₂ 1 (d + 1) (by omega) hbase₂
        have h := hS.hasProjectiveDimensionLT_X₃ d
          (by simpa [S, resolutionSyzygy] using hzero') hmid
        simpa [S, CategoryTheory.HasProjectiveDimensionLE] using h
  have hBC : HasFiniteProjectiveResolutionLE M d ↔
      ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d := by
    by_cases hd0 : d = 0
    · subst d
      simp only [HasFiniteProjectiveResolutionLE, ResolutionHasProjectiveSyzygyAt]
      constructor
      · intro h
        exact ⟨ProjectiveResolution.of M, h⟩
      · rintro ⟨P, h⟩
        exact h
    · simp only [HasFiniteProjectiveResolutionLE, ResolutionHasProjectiveSyzygyAt,
        if_neg hd0]
  have hAD : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d := by
    constructor
    · intro hA P
      by_cases hd0 : d = 0
      · subst d
        have hprojM : CategoryTheory.Projective M :=
          (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr hA
        have hmoduleM : Module.Projective R (M : Type u) :=
          (IsProjective.iff_projective (M : Type u)).mpr hprojM
        simpa [ResolutionHasProjectiveSyzygyAt] using hmoduleM
      · rw [ResolutionHasProjectiveSyzygyAt, if_neg hd0]
        have hterminal := resolutionSyzygy_bound_up P d (d - 1) (by omega) hA
        have hprojP : CategoryTheory.Projective (resolutionSyzygy P (d - 1)) :=
          CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr (by
            have hdeg : d - (d - 1) = 1 := by omega
            simpa [hdeg] using hterminal)
        exact (IsProjective.iff_projective _).mpr hprojP
    · intro hD
      apply hAB.mpr
      apply hBC.mpr
      exact ⟨ProjectiveResolution.of M, hD (ProjectiveResolution.of M)⟩
  have hAC : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    hAB.trans hBC
  change List.TFAE [
    CategoryTheory.HasProjectiveDimensionLE M d,
    HasFiniteProjectiveResolutionLE M d,
    ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d]
  apply List.tfae_of_forall (CategoryTheory.HasProjectiveDimensionLE M d)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact hAD.symm
  · exact False.elim h

/-- Projective dimension zero is the projective-module case. -/
theorem projective_dimension_zero_iff_projective {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) :
    HasProjectiveDimensionExactly M 0 ↔ Module.Projective R M := by
  constructor
  · intro h
    exact (IsProjective.iff_projective _).mpr
      ((CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr h.1)
  · intro h
    refine ⟨(CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mp
      ((IsProjective.iff_projective _).mp h), ?_⟩
    intro e he
    omega

/-! ## Local and Noetherian resolution criteria -/

/-- A finite free resolution of length at most d, represented by a
projective resolution with free terms in the finite prefix and a free terminal
syzygy. -/
def HasFiniteFreeProjectiveResolutionLE {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  if d = 0 then
    Module.Free R M
  else
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, i < d → Module.Free R (P.complex.X i)) ∧
        Module.Free R (resolutionSyzygy P (d - 1))

/-- A finite projective resolution of length at most d whose finite prefix
is represented with finite projective terms. -/
def HasFiniteProjectiveResolutionWithFiniteTermsLE {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  if d = 0 then
    Module.Finite R M ∧ Module.Projective R M
  else
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, i < d → Module.Finite R (P.complex.X i)) ∧
        Module.Finite R (resolutionSyzygy P (d - 1)) ∧
          Module.Projective R (resolutionSyzygy P (d - 1))

/-- A finite free resolution of length at most d in which every finite term
is both finite and free. -/
def HasFiniteFreeResolutionWithFiniteTermsLE {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  if d = 0 then
    Module.Finite R M ∧ Module.Free R M
  else
    ∃ P : ProjectiveResolution M,
      (∀ i : ℕ, i < d →
        Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) ∧
        Module.Finite R (resolutionSyzygy P (d - 1)) ∧
          Module.Free R (resolutionSyzygy P (d - 1))

/-- Over a local ring, the projective resolution criteria are equivalent to a
finite free resolution. -/
theorem projective_dimension_resolution_criteria_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (d : ℕ) :
    List.TFAE
      [ CategoryTheory.HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLE M d,
        ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        HasFiniteFreeProjectiveResolutionLE M d ] := by
  have hBF : HasFiniteProjectiveResolutionLE M d ↔
      HasFiniteFreeProjectiveResolutionLE M d := by
    by_cases hd0 : d = 0
    · subst d
      simp only [HasFiniteProjectiveResolutionLE, HasFiniteFreeProjectiveResolutionLE]
      constructor
      · intro h
        exact Formalization.Books.Algebra.Unit85.projective_free_over_local_ring h
      · intro h
        let : Module.Free R (M : Type u) := h
        exact (inferInstance : Module.Projective R (M : Type u))
    · simp only [HasFiniteProjectiveResolutionLE, HasFiniteFreeProjectiveResolutionLE,
        if_neg hd0]
      constructor
      · rintro ⟨P, hP⟩
        refine ⟨P, ?_, ?_⟩
        · intro i hi
          exact Formalization.Books.Algebra.Unit85.projective_free_over_local_ring
            ((IsProjective.iff_projective _).mpr (P.projective i))
        · exact Formalization.Books.Algebra.Unit85.projective_free_over_local_ring hP
      · rintro ⟨P, hterms, hterminal⟩
        refine ⟨P, ?_⟩
        let : Module.Free R (resolutionSyzygy P (d - 1) : Type u) := hterminal
        exact (inferInstance : Module.Projective R (resolutionSyzygy P (d - 1) : Type u))
  have hcriteria := projective_dimension_resolution_criteria M d
  have hAB : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionLE M d :=
    List.TFAE.out hcriteria 0 1
  have hAC : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hcriteria 0 2
  have hAD : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hcriteria 0 3
  have hAE : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteFreeProjectiveResolutionLE M d :=
    hAB.trans hBF
  change List.TFAE [
    CategoryTheory.HasProjectiveDimensionLE M d,
    HasFiniteProjectiveResolutionLE M d,
    ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    HasFiniteFreeProjectiveResolutionLE M d]
  apply List.tfae_of_forall (CategoryTheory.HasProjectiveDimensionLE M d)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact hAD.symm
  · exact hAE.symm
  · exact False.elim h

private noncomputable def finiteFreeResolutionProjectiveResolution {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FiniteFreeResolution R M) : ProjectiveResolution M := {
  complex := F.complex
  projective := fun n => by
    let hfree := F.resolution.free n
    let := hfree
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨F.resolution.resolution.augmentation,
      F.resolution.resolution.augmentation_condition⟩
  quasiIso := by
    refine ⟨fun n => ?_⟩
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨F.resolution.resolution.exact_zero,
          F.resolution.resolution.augmentation_epi⟩
      · change F.complex.d 0 0 = 0
        exact F.complex.shape 0 0 (by
          simp only [ComplexShape.down_Rel]
          omega)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
          (by simp) (by simp)]
        exact F.resolution.resolution.exact_succ n
      · exact ChainComplex.exactAt_succ_single_obj _ _ }

/-- Over a Noetherian ring, finite modules have finite-projective resolution
criteria. -/
theorem projective_dimension_resolution_criteria_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) :
    List.TFAE
      [ CategoryTheory.HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLE M d,
        ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        HasFiniteProjectiveResolutionWithFiniteTermsLE M d ] := by
  have hcriteria := projective_dimension_resolution_criteria M d
  have hAB : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionLE M d :=
    List.TFAE.out hcriteria 0 1
  have hAC : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hcriteria 0 2
  have hAD : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hcriteria 0 3
  have hAE : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionWithFiniteTermsLE M d := by
    constructor
    · intro hA
      by_cases hd0 : d = 0
      · subst d
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_pos rfl]
        exact ⟨inferInstance, (IsProjective.iff_projective _).mpr
          ((CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).mpr hA)⟩
      · obtain ⟨F⟩ := Formalization.Books.Algebra.Unit71.exists_finite_free_resolution M
        let P := finiteFreeResolutionProjectiveResolution F
        have kernel_finite {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
            [Module.Finite R X] :
              Module.Finite R
                ((CategoryTheory.Limits.kernel f : ModuleCat.{u} R) : Type u) := by
          let _ : IsNoetherian R (X : Type u) :=
            isNoetherian_of_isNoetherianRing_of_finite R (X : Type u)
          apply Module.Finite.of_injective (R := R) (S := R)
            (M := ((CategoryTheory.Limits.kernel f : ModuleCat.{u} R) : Type u))
            (N := (X : Type u))
            (kernel.ι f).hom
          exact (ModuleCat.mono_iff_injective _).mp inferInstance
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_neg hd0]
        refine ⟨P, ?_, ?_, ?_⟩
        · intro i hi
          change Module.Finite R (F.complex.X i : Type u)
          exact F.finite i
        · rw [resolutionSyzygy]
          by_cases hzero : d - 1 = 0
          · rw [if_pos hzero]
            let _ : Module.Finite R (P.complex.X 0) := by
              change Module.Finite R (F.complex.X 0 : Type u)
              exact F.finite 0
            exact kernel_finite (P.π.f 0)
          · rw [if_neg hzero]
            let _ : Module.Finite R (P.complex.X (d - 1)) := by
              change Module.Finite R (F.complex.X (d - 1) : Type u)
              exact F.finite (d - 1)
            exact kernel_finite (P.complex.d (d - 1) (d - 1 - 1))
        · have hterminal := resolutionSyzygy_bound_up P d (d - 1) (by omega) hA
          have hterminal' : CategoryTheory.HasProjectiveDimensionLT
              (resolutionSyzygy P (d - 1)) 1 := by
            have hdeg : d - (d - 1) = 1 := by omega
            simpa [hdeg] using hterminal
          exact (IsProjective.iff_projective _).mpr
            (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hterminal')
    · intro hE
      apply hAB.mpr
      by_cases hd0 : d = 0
      · subst d
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_pos rfl] at hE
        rw [HasFiniteProjectiveResolutionLE, if_pos rfl]
        exact hE.2
      · rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_neg hd0] at hE
        rw [HasFiniteProjectiveResolutionLE, if_neg hd0]
        exact ⟨hE.choose, hE.choose_spec.2.2⟩
  change List.TFAE [
    CategoryTheory.HasProjectiveDimensionLE M d,
    HasFiniteProjectiveResolutionLE M d,
    ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    HasFiniteProjectiveResolutionWithFiniteTermsLE M d]
  apply List.tfae_of_forall (CategoryTheory.HasProjectiveDimensionLE M d)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact hAD.symm
  · exact hAE.symm
  · exact False.elim h

/-- Over a local Noetherian ring, the local and Noetherian criteria are also
equivalent to a finite free resolution. -/
theorem projective_dimension_resolution_criteria_noetherian_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) :
    List.TFAE
      [ CategoryTheory.HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLE M d,
        ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
        HasFiniteFreeProjectiveResolutionLE M d,
        HasFiniteProjectiveResolutionWithFiniteTermsLE M d,
        HasFiniteFreeResolutionWithFiniteTermsLE M d ] := by
  have hlocal := projective_dimension_resolution_criteria_local M d
  have hnoetherian := projective_dimension_resolution_criteria_noetherian M d
  have hAB : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionLE M d :=
    List.TFAE.out hlocal 0 1
  have hAC : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hlocal 0 2
  have hAD : CategoryTheory.HasProjectiveDimensionLE M d ↔
      ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d :=
    List.TFAE.out hlocal 0 3
  have hAE : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteFreeProjectiveResolutionLE M d :=
    List.TFAE.out hlocal 0 4
  have hAF : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteProjectiveResolutionWithFiniteTermsLE M d :=
    List.TFAE.out hnoetherian 0 4
  have hFG : HasFiniteProjectiveResolutionWithFiniteTermsLE M d ↔
      HasFiniteFreeResolutionWithFiniteTermsLE M d := by
    constructor
    · intro hF
      by_cases hd0 : d = 0
      · subst d
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_pos rfl] at hF
        rw [HasFiniteFreeResolutionWithFiniteTermsLE, if_pos rfl]
        exact ⟨hF.1,
          Formalization.Books.Algebra.Unit85.projective_free_over_local_ring hF.2⟩
      · rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_neg hd0] at hF
        rw [HasFiniteFreeResolutionWithFiniteTermsLE, if_neg hd0]
        rcases hF with ⟨P, hterms, hterminal, hprojective⟩
        refine ⟨P, ?_, ?_, ?_⟩
        · intro i hi
          exact ⟨hterms i hi,
            Formalization.Books.Algebra.Unit85.projective_free_over_local_ring
              ((IsProjective.iff_projective _).mpr (P.projective i))⟩
        · exact hterminal
        · exact Formalization.Books.Algebra.Unit85.projective_free_over_local_ring hprojective
    · intro hG
      by_cases hd0 : d = 0
      · subst d
        rw [HasFiniteFreeResolutionWithFiniteTermsLE, if_pos rfl] at hG
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_pos rfl]
        let : Module.Free R (M : Type u) := hG.2
        exact ⟨hG.1, inferInstance⟩
      · rw [HasFiniteFreeResolutionWithFiniteTermsLE, if_neg hd0] at hG
        rw [HasFiniteProjectiveResolutionWithFiniteTermsLE, if_neg hd0]
        rcases hG with ⟨P, hterms, hterminal, hfree⟩
        refine ⟨P, ?_, ?_, ?_⟩
        · intro i hi
          exact (hterms i hi).1
        · exact hterminal
        · let : Module.Free R (resolutionSyzygy P (d - 1) : Type u) := hfree
          exact (inferInstance :
            Module.Projective R (resolutionSyzygy P (d - 1) : Type u))
  have hAG : CategoryTheory.HasProjectiveDimensionLE M d ↔
      HasFiniteFreeResolutionWithFiniteTermsLE M d := hAF.trans hFG
  change List.TFAE [
    CategoryTheory.HasProjectiveDimensionLE M d,
    HasFiniteProjectiveResolutionLE M d,
    ∃ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    ∀ P : ProjectiveResolution M, ResolutionHasProjectiveSyzygyAt P d,
    HasFiniteFreeProjectiveResolutionLE M d,
    HasFiniteProjectiveResolutionWithFiniteTermsLE M d,
    HasFiniteFreeResolutionWithFiniteTermsLE M d]
  apply List.tfae_of_forall (CategoryTheory.HasProjectiveDimensionLE M d)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact hAD.symm
  · exact hAE.symm
  · exact hAF.symm
  · exact hAG.symm
  · exact False.elim h

/-
/-! ## Minimal finite free resolutions and depth -/

private theorem localDepth_eq_of_linearEquiv
    {R M N : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    localDepth R M = localDepth R N := by
  unfold localDepth
  rw [depth_eq_sSup_weaklyRegular, depth_eq_sSup_weaklyRegular]
  congr 1
  ext n
  constructor
  · rintro ⟨rs, rfl, hmem, hreg⟩
    refine ⟨rs, rfl, hmem, ?_⟩
    exact (e.toAddEquiv.isWeaklyRegular_congr
      (List.forall₂_same.mpr fun r _ x => e.map_smul r x)).mp hreg
  · rintro ⟨rs, rfl, hmem, hreg⟩
    refine ⟨rs, rfl, hmem, ?_⟩
    exact (e.symm.toAddEquiv.isWeaklyRegular_congr
      (List.forall₂_same.mpr fun r _ x => e.symm.map_smul r x)).mp hreg

private theorem localDepth_fin_succ_ge
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (k : ℕ) :
    localDepth R (Fin k.succ → R) ≥ localDepth R R := by
  induction k with
  | zero =>
      exact le_of_eq (localDepth_eq_of_linearEquiv
        (LinearEquiv.piUnique R (fun _ : Fin 1 => R))).symm
  | succ k ih =>
      let e : (R × (Fin k.succ → R)) ≃ₗ[R] (Fin k.succ.succ → R) :=
        Fin.consLinearEquiv R (fun _ : Fin k.succ.succ => R)
      let f := e.toLinearMap.comp (LinearMap.inl R R (Fin k.succ → R))
      let g := (LinearMap.snd R R (Fin k.succ → R)).comp e.symm.toLinearMap
      have hf : Function.Injective f :=
        e.injective.comp LinearMap.inl_injective
      have hfg : Function.Exact f g :=
        (LinearEquiv.conj_exact_iff_exact
          (LinearMap.inl R R (Fin k.succ → R))
          (LinearMap.snd R R (Fin k.succ → R)) e).2 Function.Exact.inl_snd
      have hsnd : Function.Surjective
          (LinearMap.snd R R (Fin k.succ → R)) := LinearMap.snd_surjective
      have hg : Function.Surjective g := hsnd.comp e.symm.surjective
      have hseq := localDepth_shortExact f g hf hfg hg
      simpa [ih] using hseq.1

/-- A coordinate minimal finite free resolution of `M` of exact length `d`.

Besides exactness at the positive terms, the augmentation condition records
exactness at degree zero.  Minimality is the basis-independent local
condition in coordinates: every differential matrix has entries in the
maximal ideal.  The last nonzero term makes the displayed length exact. -/
structure MinimalFiniteFreeResolution
    (R M : Type u) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (d : ℕ) where
  complex : FiniteFreeComplex R d
  augmentation : (Fin (complex.termRank 0) → R) →ₗ[R] M
  augmentation_surjective : Function.Surjective augmentation
  augmentation_exact : Function.Exact (complex.differential 0) augmentation
  exact : complex.IsExact
  minimal : complex.MatrixEntriesInIdeal (IsLocalRing.maximalIdeal R)
  last_nonzero : complex.termRank d ≠ 0

/-- The depth information carried by a minimal finite free resolution. -/
structure MinimalFiniteFreeResolutionDepthInterface
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (d : ℕ) where
  resolution : MinimalFiniteFreeResolution R M d
  depth_lower : localDepth R M ≥ localDepth R R - d

private theorem exists_minimal_finite_free_cover
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M),
      Function.Surjective f ∧
        LinearMap.ker f ≤
          IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin n → R)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  let : Fintype ι := Fintype.ofFinite ι
  let b : Basis (Fin (Fintype.card ι)) k (k ⊗[R] M) :=
    (Module.Free.chooseBasis k (k ⊗[R] M)).reindex (Fintype.equivFin ι)
  have hmk : Function.Surjective (TensorProduct.mk R k M 1) :=
    TensorProduct.mk_surjective R M k Quotient.mk_surjective
  choose v hv using fun i : Fin (Fintype.card ι) => hmk (b i)
  let f : (Fin (Fintype.card ι) → R) →ₗ[R] M :=
    Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b (fun i => by
      simpa using hv i)
  have hbbij : Function.Bijective (Fintype.linearCombination k b) := by
    have heq : Fintype.linearCombination k b = b.equivFun.symm.toLinearMap := by
      ext x
      simp [Fintype.linearCombination_apply]
    rw [heq]
    exact b.equivFun.symm.bijective
  have hvbij : Function.Bijective
      (Fintype.linearCombination k (TensorProduct.mk R k M 1 ∘ v)) := by
    simpa [Function.comp_def, hv] using hbbij
  let e : k ⊗[R] (Fin (Fintype.card ι) → R) ≃ₗ[k]
      (Fin (Fintype.card ι) → k) :=
    TensorProduct.piScalarRight R k k (Fin (Fintype.card ι))
  have hcomp :
      (f.baseChange k).comp e.symm.toLinearMap =
        Fintype.linearCombination k (TensorProduct.mk R k M 1 ∘ v) := by
    apply LinearMap.pi_ext
    intro i r
    simp [e, f, LinearMap.baseChange_tmul,
      Fintype.linearCombination_apply_single, Function.comp_def]
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    change r ⊗ₜ[R] v i = r ⊗ₜ[R] v i
    rfl
  have hbasebij : Function.Bijective (f.baseChange k) := by
    have hcompbij : Function.Bijective
        ((f.baseChange k).comp e.symm.toLinearMap) := by
      rw [hcomp]
      exact hvbij
    exact (Function.Bijective.of_comp_iff (f.baseChange k) e.symm.bijective).mp
      hcompbij
  refine ⟨Fintype.card ι, f, hf, ?_⟩
  intro x hx
  rw [← LinearMap.ker_tensorProductMk]
  apply hbasebij.1
  change (f.baseChange k) (1 ⊗ₜ[R] x) = (f.baseChange k) 0
  rw [LinearMap.baseChange_tmul]
  simp [LinearMap.mem_ker.mp hx]

private noncomputable def prependMinimalFiniteFreeResolution
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (d n : ℕ) (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Surjective f)
    (hmin : LinearMap.ker f ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin n → R)))
    (D : MinimalFiniteFreeResolution R (LinearMap.ker f) d) :
    MinimalFiniteFreeResolution R M (d + 1) := by
  let r : ℕ → ℕ
    | 0 => n
    | i + 1 => D.complex.termRank i
  let δ : ∀ i : ℕ, (Fin (r (i + 1)) → R) →ₗ[R] (Fin (r i) → R)
    | 0 => (LinearMap.ker f).subtype.comp D.augmentation
    | i + 1 => D.complex.differential i
  let C : FiniteFreeComplex R (d + 1) :=
    { termRank := r
      termRank_zero := by
        intro i hi
        cases i with
        | zero => omega
        | succ i =>
          simpa [r] using D.complex.termRank_zero i (by omega)
      differential := δ
      differential_zero := by
        intro i hi
        cases i with
        | zero => omega
        | succ i =>
          simpa [δ] using D.complex.differential_zero i (by omega)
      differential_comp := by
        intro i
        cases i with
        | zero =>
          simpa [δ, r, LinearMap.comp_assoc] using congrArg
            (fun g => (LinearMap.ker f).subtype.comp g)
            D.augmentation_exact.linearMap_comp_eq_zero
        | succ i =>
          simpa [δ] using D.complex.differential_comp i }
  have hCexact : C.IsExact := by
    intro i
    cases d with
    | zero =>
      by_cases hi0 : i = 0
      · subst i
        simp [FiniteFreeComplex.IsExactAt]
      · by_cases hi1 : i = 1
        · subst i
          have hDinj : Function.Injective D.augmentation := by
            rw [← LinearMap.ker_eq_bot]
            have hDexact := D.augmentation_exact
            rw [LinearMap.exact_iff] at hDexact
            rw [hDexact]
            exact LinearMap.range_eq_bot.mpr
              (D.complex.differential_zero 0 (by omega))
          simpa [FiniteFreeComplex.IsExactAt, C, δ, r,
            FiniteFreeComplex.previousDifferential] using
              Subtype.val_injective.comp hDinj
        · simp [FiniteFreeComplex.IsExactAt, hi0, hi1]
    | succ d =>
      cases i with
      | zero => simp [FiniteFreeComplex.IsExactAt]
      | succ j =>
        by_cases hjL : j = d + 1
        · subst j
          have hDex := D.exact (d + 1)
          rw [FiniteFreeComplex.IsExactAt, dif_neg (by omega : d + 1 ≠ 0),
            dif_pos rfl] at hDex
          simpa [FiniteFreeComplex.IsExactAt, C, δ, r,
            FiniteFreeComplex.previousDifferential] using hDex
        · by_cases hjLt : j < d + 1
          · cases j with
            | zero =>
              have h := (Subtype.val_injective : Function.Injective
                ((LinearMap.ker f).subtype : LinearMap.ker f → Fin n → R))
              have hexact := (Function.Injective.comp_exact_iff_exact
                (f := D.complex.differential 0) (g := D.augmentation)
                (i := (LinearMap.ker f).subtype) h).mpr
                  D.augmentation_exact
              simpa [FiniteFreeComplex.IsExactAt, C, δ, r,
                FiniteFreeComplex.previousDifferential] using hexact
            | succ j =>
              have hDex := D.exact (j + 1)
              rw [FiniteFreeComplex.IsExactAt, dif_neg (by omega : j + 1 ≠ 0),
                dif_neg (by omega : j + 1 ≠ d + 1), dif_pos (by omega)] at hDex
              rw [FiniteFreeComplex.IsExactAt, dif_neg (by omega : j + 2 ≠ 0),
                dif_neg (by omega : j + 2 ≠ d + 2), dif_pos (by omega)]
              simpa [FiniteFreeComplex.IsExactAt, C, δ, r,
                FiniteFreeComplex.previousDifferential] using hDex
          · rw [FiniteFreeComplex.IsExactAt, dif_neg (by omega : j + 1 ≠ 0),
              dif_neg (by omega : j + 1 ≠ d + 2), dif_neg (by omega : ¬j + 1 < d + 2)]
            trivial
  refine
    { complex := C
      augmentation := f
      augmentation_surjective := hf
      augmentation_exact := by
        rw [LinearMap.exact_iff]
        change LinearMap.ker f =
          LinearMap.range ((LinearMap.ker f).subtype.comp D.augmentation)
        rw [LinearMap.range_comp,
          LinearMap.range_eq_top.mpr D.augmentation_surjective,
          Submodule.map_top, Submodule.range_subtype]
      exact := hCexact
      minimal := by
        intro i hi a b
        cases i with
        | zero =>
          let p : (Fin n → R) →ₗ[R] R := LinearMap.proj a
          have hp : Function.Surjective p := by
            intro x
            exact ⟨Pi.single a x, by simp [p]⟩
          have hx : ((D.augmentation (Pi.single b 1) : LinearMap.ker f) :
              Fin n → R) ∈
              IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin n → R)) :=
            hmin (D.augmentation (Pi.single b 1)).property
          have hxmap : p (D.augmentation (Pi.single b 1)) ∈
              Submodule.map p (IsLocalRing.maximalIdeal R •
                (⊤ : Submodule R (Fin n → R))) :=
            Submodule.mem_map_of_mem hx
          rw [Submodule.map_smul'', Submodule.map_top,
            LinearMap.range_eq_top.mpr hp] at hxmap
          have hentry : ((LinearMap.toMatrix'
              ((LinearMap.ker f).subtype.comp D.augmentation)) a b : R) ∈
              IsLocalRing.maximalIdeal R := by
            simpa [p, Ideal.smul_eq_mul] using hxmap
          simpa [C, δ, r] using hentry
        | succ i =>
          simpa [C, δ, r] using D.minimal i (by omega) a b
      last_nonzero := by
        simpa [C, r] using D.last_nonzero }

/-- A nonzero finite module of exact finite projective dimension over a
Noetherian local ring has a minimal coordinate finite free resolution of
that exact length. -/
theorem exists_minimalFiniteFreeResolution
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hM : HasProjectiveDimensionExactly (ModuleCat.of R M) d) :
    Nonempty (MinimalFiniteFreeResolution R M d) := by
  induction d generalizing M with
  | zero =>
      have hproj : Module.Projective R M :=
        (projective_dimension_zero_iff_projective (ModuleCat.of R M)).mp hM
      let hfree : Module.Free R M :=
        Formalization.Books.Algebra.Unit85.projective_free_over_local_ring hproj
      let : Module.Free R M := hfree
      let ι := Module.Free.ChooseBasisIndex R M
      let b₀ : Basis ι R M := Module.Free.chooseBasis R M
      let : Fintype ι := Fintype.ofFinite ι
      let b : Basis (Fin (Fintype.card ι)) R M :=
        b₀.reindex (Fintype.equivFin ι)
      let e : (Fin (Fintype.card ι) → R) ≃ₗ[R] M := b.equivFun.symm
      let C : FiniteFreeComplex R 0 :=
        { termRank := fun i => if i = 0 then Fintype.card ι else 0
          termRank_zero := by
            intro i hi
            simp [show i ≠ 0 by omega]
          differential := fun _ => 0
          differential_zero := by intro i hi; rfl
          differential_comp := by intro i; rfl }
      refine ⟨{
        complex := C
        augmentation := e.toLinearMap
        augmentation_surjective := e.surjective
        augmentation_exact := by
          simpa [C] using
            (LinearMap.exact_zero_iff_injective (Fin 0 → R) e.toLinearMap).mpr
              e.injective
        exact := by
          intro i
          simp [FiniteFreeComplex.IsExactAt]
        minimal := by
          intro i hi
          omega
        last_nonzero := ?_ }⟩
      intro hcard
      have hcard' : Fintype.card ι = 0 := by
        simp [C] at hcard
      have hdom : Subsingleton (Fin (Fintype.card ι) → R) := by
        rw [hcard']
        infer_instance
      have hMsub : Subsingleton M := by
        constructor
        intro x y
        obtain ⟨x', rfl⟩ := e.surjective x
        obtain ⟨y', rfl⟩ := e.surjective y
        exact congrArg e (hdom.elim x' y')
      exact not_subsingleton_iff_nontrivial.mpr inferInstance hMsub
  | succ d ih =>
      obtain ⟨n, f, hf, hmin⟩ := exists_minimal_finite_free_cover (R := R) (M := M)
      let K : Type u := LinearMap.ker f
      let : IsNoetherian R (Fin n → R) :=
        isNoetherian_of_isNoetherianRing_of_finite R (Fin n → R)
      let : IsNoetherian R K :=
        isNoetherian_of_submodule_of_noetherian R (Fin n → R) (LinearMap.ker f)
          inferInstance
      let : Module.Finite R K := inferInstance
      have hKnontrivial : Nontrivial K := by
        apply not_subsingleton_iff_nontrivial.mp
        intro hKsub
        have hfinj : Function.Injective f := by
          rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
          exact hKsub
        let e : (Fin n → R) ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hfinj, hf⟩
        have hprojF : CategoryTheory.Projective (ModuleCat.of R (Fin n → R)) := by
          exact (IsProjective.iff_projective _).mp inferInstance
        have hprojM : CategoryTheory.Projective (ModuleCat.of R M) := by
          exact CategoryTheory.Projective.of_iso e.toModuleIso hprojF
        exact hM.2 0 (by omega)
          ((CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
            (ModuleCat.of R M)).mp hprojM)
      let : Nontrivial K := hKnontrivial
      let S := ShortComplex.moduleCatMk (LinearMap.ker f).subtype f
        f.exact_subtype_ker_map.linearMap_comp_eq_zero
      have hS : S.ShortExact :=
        ModuleCat.shortComplex_shortExact S f.exact_subtype_ker_map
          Subtype.val_injective hf
      have hprojF : CategoryTheory.Projective S.X₂ := by
        dsimp [S]
        exact (IsProjective.iff_projective _).mp inferInstance
      have hFbound (q : ℕ) (hq : 1 ≤ q) :
          CategoryTheory.HasProjectiveDimensionLT S.X₂ q := by
        exact hasProjectiveDimensionLT_of_ge_explicit S.X₂ 1 q hq
          (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hprojF)
      have hKbound : CategoryTheory.HasProjectiveDimensionLE S.X₁ d := by
        exact hS.hasProjectiveDimensionLT_X₁ (d + 1) (hFbound (d + 1) (by omega)) hM.1
      change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R K) d at hKbound
      have hKexact : HasProjectiveDimensionExactly (ModuleCat.of R K) d := by
        refine ⟨?_, ?_⟩
        · exact hKbound
        · intro q hqd hq
          have hq' : CategoryTheory.HasProjectiveDimensionLE S.X₁ q := by
            change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R K) q
            exact hq
          have hMbound : CategoryTheory.HasProjectiveDimensionLE S.X₃ (q + 1) :=
            hS.hasProjectiveDimensionLT_X₃ (q + 1) hq'
              (hFbound (q + 2) (by omega))
          change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) (q + 1) at hMbound
          exact hM.2 (q + 1) (by omega) hMbound
      obtain ⟨D⟩ := ih hKexact
      exact ⟨prependMinimalFiniteFreeResolution d n f hf hmin D⟩

/-- The minimal resolution can be chosen together with the depth inequality
obtained by breaking it into short exact sequences. -/
theorem exists_minimalFiniteFreeResolutionDepthInterface
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hM : HasProjectiveDimensionExactly (ModuleCat.of R M) d) :
    Nonempty (MinimalFiniteFreeResolutionDepthInterface R M d) := by
  induction d generalizing M with
  | zero =>
      obtain ⟨F⟩ := exists_minimalFiniteFreeResolution 0 hM
      have hfinj : Function.Injective F.augmentation := by
        have hexact := F.augmentation_exact
        rw [F.complex.differential_zero 0 (by omega)] at hexact
        exact (LinearMap.exact_zero_iff_injective
          (Fin (F.complex.termRank 1) → R) F.augmentation).mp hexact
      let e : (Fin (F.complex.termRank 0) → R) ≃ₗ[R] M :=
        LinearEquiv.ofBijective F.augmentation ⟨hfinj, F.augmentation_surjective⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero F.last_nonzero
      have hfree := localDepth_fin_succ_ge (R := R) k
      have heq : localDepth R (Fin (F.complex.termRank 0) → R) = localDepth R M :=
        localDepth_eq_of_linearEquiv e
      refine ⟨{ resolution := F, depth_lower := ?_ }⟩
      rw [← hk] at hfree
      rw [heq] at hfree
      simpa using hfree
  | succ d ih =>
      obtain ⟨n, f, hf, hmin⟩ := exists_minimal_finite_free_cover (R := R) (M := M)
      let K : Type u := LinearMap.ker f
      let : IsNoetherian R (Fin n → R) :=
        isNoetherian_of_isNoetherianRing_of_finite R (Fin n → R)
      let : IsNoetherian R K :=
        isNoetherian_of_submodule_of_noetherian R (Fin n → R) (LinearMap.ker f)
          inferInstance
      let : Module.Finite R K := inferInstance
      have hKnontrivial : Nontrivial K := by
        apply not_subsingleton_iff_nontrivial.mp
        intro hKsub
        have hfinj : Function.Injective f := by
          rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
          exact hKsub
        let e : (Fin n → R) ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hfinj, hf⟩
        have hprojF : CategoryTheory.Projective (ModuleCat.of R (Fin n → R)) :=
          (IsProjective.iff_projective _).mp inferInstance
        have hprojM : CategoryTheory.Projective (ModuleCat.of R M) :=
          CategoryTheory.Projective.of_iso e.toModuleIso hprojF
        exact hM.2 0 (by omega)
          ((CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
            (ModuleCat.of R M)).mp hprojM)
      let : Nontrivial K := hKnontrivial
      let S := ShortComplex.moduleCatMk (LinearMap.ker f).subtype f
        f.exact_subtype_ker_map.linearMap_comp_eq_zero
      have hS : S.ShortExact :=
        ModuleCat.shortComplex_shortExact S f.exact_subtype_ker_map
          Subtype.val_injective hf
      have hprojF : CategoryTheory.Projective S.X₂ := by
        dsimp [S]
        exact (IsProjective.iff_projective _).mp inferInstance
      have hFbound (q : ℕ) (hq : 1 ≤ q) :
          CategoryTheory.HasProjectiveDimensionLT S.X₂ q :=
        hasProjectiveDimensionLT_of_ge_explicit S.X₂ 1 q hq
          (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hprojF)
      have hKbound : CategoryTheory.HasProjectiveDimensionLE S.X₁ d :=
        hS.hasProjectiveDimensionLT_X₁ (d + 1) (hFbound (d + 1) (by omega)) hM.1
      change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R K) d at hKbound
      have hKexact : HasProjectiveDimensionExactly (ModuleCat.of R K) d := by
        refine ⟨hKbound, ?_⟩
        intro q hqd hq
        have hq' : CategoryTheory.HasProjectiveDimensionLE S.X₁ q := by
          change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R K) q
          exact hq
        have hMbound : CategoryTheory.HasProjectiveDimensionLE S.X₃ (q + 1) :=
          hS.hasProjectiveDimensionLT_X₃ (q + 1) hq' (hFbound (q + 2) (by omega))
        change CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) (q + 1) at hMbound
        exact hM.2 (q + 1) (by omega) hMbound
      obtain ⟨D⟩ := ih hKexact
      have hn : n ≠ 0 := by
        intro hn
        have hdom : Subsingleton (Fin n → R) := by
          rw [hn]
          infer_instance
        have hMsub : Subsingleton M := by
          constructor
          intro x y
          obtain ⟨x', rfl⟩ := hf x
          obtain ⟨y', rfl⟩ := hf y
          exact congrArg f (hdom.elim x' y')
        exact not_subsingleton_iff_nontrivial.mpr inferInstance hMsub
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hfree : localDepth R (Fin n → R) ≥ localDepth R R := by
        rw [hk]
        exact localDepth_fin_succ_ge (R := R) k
      let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      let : Nontrivial (Fin n → R) := inferInstance
      have hseq := localDepth_shortExact (LinearMap.ker f).subtype f
        Subtype.val_injective f.exact_subtype_ker_map hf
      have hsub : localDepth R R - (d + 1 : ℕ) ≤ localDepth R R := tsub_le_self
      have hsubK : localDepth R R - (d + 1 : ℕ) ≤ localDepth R K - 1 := by
        calc
          localDepth R R - (d + 1 : ℕ) = (localDepth R R - d) - 1 := by
            rw [← tsub_add_eq_tsub_tsub]
            norm_num
          _ ≤ localDepth R K - 1 := tsub_le_tsub_right D.depth_lower 1
      refine ⟨{
        resolution := prependMinimalFiniteFreeResolution d n f hf hmin D.resolution
        depth_lower := ?_ }⟩
      exact (le_min (hsub.trans hfree) hsubK).trans hseq.2.1

/-- The exact length of a minimal finite free resolution is bounded by the
depth of the local ring. -/
theorem MinimalFiniteFreeResolution.length_le_localDepth
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] {d : ℕ}
    (F : MinimalFiniteFreeResolution R M d) :
    (d : ℕ∞) ≤ localDepth R R := by
  cases d with
  | zero => simp
  | succ d =>
      let φ := F.complex.previousDifferential (d + 1) (by omega)
      have hφinj : Function.Injective φ := by
        have hexact := F.exact (d + 1)
        rw [FiniteFreeComplex.IsExactAt, dif_neg (by omega : d + 1 ≠ 0),
          dif_pos rfl] at hexact
        exact hexact.2
      have hφne : φ ≠ 0 := by
        intro hφ
        let b : Fin (F.complex.termRank (d + 1)) :=
          ⟨0, Nat.pos_of_ne_zero F.last_nonzero⟩
        have hb : (Pi.single b (1 : R) :
            Fin (F.complex.termRank (d + 1)) → R) ≠ 0 := by
          intro h
          have h' := congrFun h b
          simp at h'
        apply hb
        apply hφinj
        simp [hφ]
      have hrank : rank φ ≠ 0 := by
        intro h
        exact hφne ((rank_eq_zero_iff φ).mp h)
      let : Nonempty (Fin (rank φ)) := ⟨⟨0, Nat.pos_of_ne_zero hrank⟩⟩
      have hentries (a : Fin (F.complex.termRank d))
          (b : Fin (F.complex.termRank (d + 1))) :
          (LinearMap.toMatrix' φ) a b ∈ IsLocalRing.maximalIdeal R := by
        simpa [φ, FiniteFreeComplex.previousDifferential] using
          F.minimal d (by omega) a b
      have hrankIdeal : rankIdeal φ ≤ IsLocalRing.maximalIdeal R := by
        rw [rankIdeal]
        apply Ideal.span_le.2
        rintro x ⟨p, rfl⟩
        change ((LinearMap.toMatrix' φ).submatrix p.1 p.2).det ∈
          IsLocalRing.maximalIdeal R
        rw [← IsLocalRing.residue_eq_zero_iff]
        rw [RingHom.map_det]
        have hmatrix :
            (IsLocalRing.residue R).mapMatrix
                ((LinearMap.toMatrix' φ).submatrix p.1 p.2) = 0 := by
          ext a b
          simp only [RingHom.mapMatrix_apply, Matrix.zero_apply]
          change IsLocalRing.residue R
            ((LinearMap.toMatrix' φ) (p.1 a) (p.2 b)) = 0
          rw [IsLocalRing.residue_eq_zero_iff]
          exact hentries (p.1 a) (p.2 b)
        rw [hmatrix]
        simp
      have hconditions := (proposition_what_exact F.complex).mp F.exact
      have hideal := hconditions.2 (d + 1) (by omega) (by omega)
      have hregular : ContainsRegularSequence (rankIdeal φ) (d + 1) := by
        rcases hideal with htop | hregular
        · exfalso
          apply (IsLocalRing.maximalIdeal.isMaximal R).ne_top
          apply top_unique
          rw [← htop]
          exact hrankIdeal
        · exact hregular
      rcases hregular with ⟨xs, hxslen, hxsideal, hxsreg⟩
      have hxsmax : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R := by
        intro x hx
        exact hrankIdeal (hxsideal x hx)
      rw [localDepth, depth]
      split_ifs with htop
      · exact False.elim
          ((smul_top_ne_top_of_le_ring_jacobson
            (IsLocalRing.maximalIdeal R) R
            (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))) htop)
      · apply le_sSup
        exact ⟨xs, by simp [hxslen], hxsmax, hxsreg⟩

private theorem projectiveDimension_eq_of_exact
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) [Nontrivial M]
    (d : ℕ) (hM : HasProjectiveDimensionExactly M d) :
    CategoryTheory.projectiveDimension M = (d : WithBot ℕ∞) := by
  apply le_antisymm
  · exact (CategoryTheory.projectiveDimension_le_iff M d).2 hM.1
  · rw [CategoryTheory.projectiveDimension_ge_iff]
    intro hlt
    cases d with
    | zero =>
        rw [CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero] at hlt
        have hsub : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hlt
        exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub
    | succ d =>
        exact hM.2 d (by omega) hlt

/-- At depth zero, finite projective dimension is exactly the local depth of
the ring.  This is the base equality supplied by the checked minimal
finite-free resolution/depth interface. -/
theorem auslander_buchsbaum_depth_zero
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hpd : HasFiniteProjectiveDimension (ModuleCat.of R M))
    (hdepth : localDepth R M = 0) :
    ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) := by
  classical
  have hbounds : ∃ d : ℕ,
      CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) d :=
    (hasFiniteProjectiveDimension_iff_exists_projective_dimension_bound
      (ModuleCat.of R M)).mp hpd
  let d := Nat.find hbounds
  have hd : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) d :=
    Nat.find_spec hbounds
  have hexact : HasProjectiveDimensionExactly (ModuleCat.of R M) d := by
    refine ⟨hd, ?_⟩
    intro e he hbound
    exact (not_le_of_gt he) (Nat.find_min' hbounds hbound)
  obtain ⟨F⟩ := exists_minimalFiniteFreeResolutionDepthInterface d hexact
  have hle : localDepth R R ≤ (d : ℕ∞) := by
    apply (tsub_eq_zero_iff_le).mp
    apply le_zero_iff.mp
    simpa [hdepth] using F.depth_lower
  have heq : localDepth R R = (d : ℕ∞) :=
    le_antisymm hle F.resolution.length_le_localDepth
  rw [heq, projectiveDimension_eq_of_exact (ModuleCat.of R M) d hexact]
  rfl

private theorem auslander_buchsbaum_of_depth_eq_nat
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (hdepth : localDepth R M = (e : ℕ∞))
    (hpd : HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) +
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  induction e generalizing M with
  | zero =>
      have hbase := auslander_buchsbaum_depth_zero (R := R) (M := M) hpd
        (by simpa using hdepth)
      simpa [hdepth] using hbase
  | succ e ih =>
      obtain ⟨ys, hysreg, hysdepth⟩ :=
        regular_sequence_extend_to_localDepth (R := R) (M := M) []
          (RingTheory.Sequence.IsRegular.nil R M)
      simp only [List.nil_append] at hysreg hysdepth
      have hyslen : ys.length = e + 1 := by
        have hlen : (ys.length : ℕ∞) = (e + 1 : ℕ∞) := by
          calc
            (ys.length : ℕ∞) = localDepth R M := by simpa using hysdepth.symm
            _ = (e + 1 : ℕ∞) := hdepth
        exact_mod_cast hlen
      cases ys with
      | nil => simp at hyslen
      | cons x xs =>
          have hxreg : IsSMulRegular M x :=
            (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hysreg |>.1
          have hxmax : x ∈ IsLocalRing.maximalIdeal R := by
            by_contra hx
            have hxunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hx
            have hxideal : x ∈ Ideal.ofList (x :: xs) := Ideal.subset_span (by simp)
            have htop : Ideal.ofList (x :: xs) = ⊤ :=
              Ideal.eq_top_of_isUnit_mem _ hxideal hxunit
            apply hysreg.top_ne_smul
            simp [htop]
          let Q : Type u := QuotSMulTop x M
          let : Module.Finite R Q := inferInstance
          let : Nontrivial Q := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxmax
          have hdepthQ : localDepth R Q = (e : ℕ∞) := by
            have hdrop := localDepth_drops_by_one (R := R) (M := M) x hxmax hxreg
            rw [hdrop, hdepth]
            rw [← ENat.natCast_one]
            rw [← ENat.natCast_sub]
            simp
          have hpdeq : CategoryTheory.projectiveDimension (ModuleCat.of R Q) =
              CategoryTheory.projectiveDimension (ModuleCat.of R M) + 1 := by
            exact ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
              (ModuleCat.of R M) x hxreg hxmax
          have hpdQ : HasFiniteProjectiveDimension (ModuleCat.of R Q) := by
            rw [hasFiniteProjectiveDimension_iff_projectiveDimension_ne_top, hpdeq]
            have hpne :=
              (hasFiniteProjectiveDimension_iff_projectiveDimension_ne_top
                (ModuleCat.of R M)).mp hpd
            generalize hp : CategoryTheory.projectiveDimension (ModuleCat.of R M) = p at hpne ⊢
            cases p with
            | bot => simp
            | coe p =>
              cases p with
              | top => simp at hpne
              | coe p =>
                intro htop
                change ((((p : ℕ∞) + 1 : ℕ∞)) : WithBot ℕ∞) = ⊤ at htop
                have htop' : (p : ℕ∞) + 1 = ⊤ := WithBot.coe_eq_top.mp htop
                rw [← ENat.natCast_one, ← Nat.cast_add] at htop'
                exact ENat.natCast_ne_top (p + 1) htop'
          have hIH := ih (M := Q) hdepthQ hpdQ
          rw [hpdeq, hdepthQ] at hIH
          simpa [hdepth, Nat.cast_add, add_assoc, add_comm] using hIH

/-- Auslander--Buchsbaum, exposed in Chapter 109 through the minimal finite
free resolution/depth interface needed by the later chapter. -/
theorem auslander_buchsbaum_of_finite_projective_dimension
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hpd : HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) +
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨e, hdepth, _, _⟩ := localDepth_eq_min_ext (R := R) (M := M)
  exact auslander_buchsbaum_of_depth_eq_nat e hdepth hpd

-/
/-! ## Ext characterization and short exact sequences -/

/-- Vanishing of all Ext groups in degrees strictly above n. -/
def ExtVanishesAbove {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R) (i : ℕ), n + 1 ≤ i →
    ∀ e : ExtGroup M N i, e = 0

/-- Vanishing of the first Ext group above degree n. -/
def ExtVanishesAtNext {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} R), ∀ e : ExtGroup M N (n + 1), e = 0

/-- Projective dimension is characterized by Ext vanishing. -/
theorem projective_dimension_ext_criteria {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    List.TFAE
      [ CategoryTheory.HasProjectiveDimensionLE M n,
        ExtVanishesAbove M n,
        ExtVanishesAtNext M n ] := by
  let : CategoryTheory.EnoughInjectives (ModuleCat.{u} R) := ModuleCat.enoughInjectives R
  have hAB : CategoryTheory.HasProjectiveDimensionLE M n ↔ ExtVanishesAbove M n := by
    change CategoryTheory.HasProjectiveDimensionLT M (n + 1) ↔ ExtVanishesAbove M n
    rw [CategoryTheory.hasProjectiveDimensionLT_iff]
    constructor
    · intro h N i hi e
      exact h i hi e
    · intro h i hi Y e
      exact h Y i hi e
  have hAC : CategoryTheory.HasProjectiveDimensionLE M n ↔ ExtVanishesAtNext M n := by
    constructor
    · intro h N e
      let : CategoryTheory.HasProjectiveDimensionLT M (n + 1) := h
      exact CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e (n + 1) (by rfl)
    · intro h
      apply CategoryTheory.hasProjectiveDimensionLT_of_enoughInjectives M (n + 1)
      intro Y
      constructor
      intro e₁ e₂
      exact (h Y e₁).trans (h Y e₂).symm
  change List.TFAE [
    CategoryTheory.HasProjectiveDimensionLE M n,
    ExtVanishesAbove M n,
    ExtVanishesAtNext M n]
  apply List.tfae_of_forall (CategoryTheory.HasProjectiveDimensionLE M n)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact False.elim h

/-- The projective-dimension bounds in a short exact sequence. -/
theorem exact_sequence_projective_dimension {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    (CategoryTheory.HasProjectiveDimensionLE S.X₂ n ∧
        CategoryTheory.HasProjectiveDimensionLE S.X₃ (n + 1) →
      CategoryTheory.HasProjectiveDimensionLE S.X₁ n) ∧
      (CategoryTheory.HasProjectiveDimensionLE S.X₁ n ∧
        CategoryTheory.HasProjectiveDimensionLE S.X₃ n →
      CategoryTheory.HasProjectiveDimensionLE S.X₂ n) ∧
      (CategoryTheory.HasProjectiveDimensionLE S.X₁ n ∧
          CategoryTheory.HasProjectiveDimensionLE S.X₂ (n + 1) →
        CategoryTheory.HasProjectiveDimensionLE S.X₃ (n + 1)) := by
  constructor
  · intro h
    exact hS.hasProjectiveDimensionLT_X₁ (n + 1) h.1 h.2
  · constructor
    · intro h
      exact hS.hasProjectiveDimensionLT_X₂ (n + 1) h.1 h.2
    · intro h
      exact hS.hasProjectiveDimensionLT_X₃ (n + 1) h.1 h.2

/-! ## Global dimension -/

/-- Every module has projective dimension at most n. -/
def HasGlobalDimensionLE (R : Type u) [Ring R] (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} R, CategoryTheory.HasProjectiveDimensionLE M n

/-- A ring has finite global dimension. -/
def HasFiniteGlobalDimension (R : Type u) [Ring R] : Prop :=
  ∃ n : ℕ, HasGlobalDimensionLE R n

/-- The global projective dimension, as the supremum of the canonical
projective dimensions of all modules in ModuleCat. -/
noncomputable def globalDimension (R : Type u) [Ring R] : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{u} R, CategoryTheory.projectiveDimension M

/-- The global dimension is bounded by n exactly when every module has that
projective-dimension bound. -/
theorem globalDimension_le_iff {R : Type u} [Ring R] (n : ℕ) :
    globalDimension R ≤ ((n : ℕ∞) : WithBot ℕ∞) ↔ HasGlobalDimensionLE R n := by
  simp [globalDimension, CategoryTheory.projectiveDimension_le_iff, HasGlobalDimensionLE]

/-- Finiteness of global dimension is equivalent to the global dimension not
being infinite. -/
theorem hasFiniteGlobalDimension_iff_globalDimension_ne_top
    {R : Type u} [Ring R] :
    HasFiniteGlobalDimension R ↔ globalDimension R ≠ ⊤ := by
  constructor
  · rintro ⟨n, hn⟩
    exact ne_top_of_le_ne_top
      (by
        intro htop
        apply ENat.natCast_ne_top n
        exact WithBot.coe_eq_top.mp htop)
      ((globalDimension_le_iff n).2 hn)
  · intro h
    have hbound : ∃ n : ℕ, globalDimension R ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
      by_contra hbound
      apply h
      rw [ENat.WithBot.eq_top_iff_forall_ge]
      intro m
      exact (lt_of_not_ge (fun hm => hbound ⟨m, hm⟩)).le
    rcases hbound with ⟨n, hn⟩
    exact ⟨n, (globalDimension_le_iff n).1 hn⟩

/-! ## Well-ordered unions of modules -/

/-- A well-ordered increasing filtration by submodules whose union is the
ambient module. -/
structure WellOrderedSubmoduleFiltration
    (R M : Type u) (E : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [LinearOrder E] [WellFoundedLT E] where
  stage : E → Submodule R M
  monotone : Monotone stage
  exhaustive : ⨆ e, stage e = ⊤

/-- The submodule of a stage generated by all earlier stages. -/
def WellOrderedSubmoduleFiltration.predecessor
    {R M : Type u} {E : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [LinearOrder E] [WellFoundedLT E]
    (F : WellOrderedSubmoduleFiltration R M E) (e : E) :
    Submodule R (F.stage e) :=
  Submodule.comap (F.stage e).subtype
    (⨆ e' : {e' : E // e' < e}, F.stage e'.1)

/-- The successive quotient of a well-ordered filtration. -/
def WellOrderedSubmoduleFiltration.successiveQuotient
    {R M : Type u} {E : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [LinearOrder E] [WellFoundedLT E]
    (F : WellOrderedSubmoduleFiltration R M E) (e : E) : ModuleCat.{u} R :=
  ModuleCat.of R ((F.stage e : Type u) ⧸ F.predecessor e)

/-- A well-ordered union of modules has projective dimension bounded by the
common bound on its successive quotients. -/
theorem colimit_projective_dimension
    {R M : Type u} {E : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [LinearOrder E] [WellFoundedLT E]
    (F : WellOrderedSubmoduleFiltration R M E) (n : ℕ)
    (hF : ∀ e : E,
      CategoryTheory.HasProjectiveDimensionLE (F.successiveQuotient e) n) :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  sorry
/-
  induction n with
  | zero =>
      let Q : E → Type u := fun e => (F.stage e : Type u) ⧸ F.predecessor e
      let q : ∀ e : E, (F.stage e : Type u) →ₗ[R] Q e :=
        fun e => (F.predecessor e).mkQ
      have hproj : ∀ e : E, CategoryTheory.Projective (ModuleCat.of R (Q e)) := by
        intro e
        change CategoryTheory.Projective (F.successiveQuotient e)
        exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero _).mpr (hF e)
      have hprojM : ∀ e : E, Module.Projective R (Q e) := by
        intro e
        exact (IsProjective.iff_projective (ModuleCat.of R (Q e) : Type u)).mpr (hproj e)
      let s : ∀ e : E, Q e →ₗ[R] (F.stage e : Type u) := fun e =>
        Classical.choose (Module.projective_lifting_property (R := R) (P := Q e)
          (M := (F.stage e : Type u)) (N := Q e) (h := hprojM e) (q e)
          (LinearMap.id) (Submodule.mkQ_surjective (F.predecessor e)))
      have hs : ∀ e : E, (q e).comp (s e) = LinearMap.id := by
        intro e
        exact Classical.choose_spec (Module.projective_lifting_property (R := R) (P := Q e)
          (M := (F.stage e : Type u)) (N := Q e) (h := hprojM e) (q e)
          (LinearMap.id) (Submodule.mkQ_surjective (F.predecessor e)))
      let p : ∀ e : E, Submodule R M := fun e =>
        Submodule.map (F.stage e).subtype (LinearMap.range (s e))
      have hp : ∀ e : E, Module.Projective R (p e : Type u) := by
        intro e
        let es : Q e ≃ₗ[R] LinearMap.range (s e) :=
          LinearEquiv.ofInjective (s e) (by
            intro x y hxy
            have := congrArg (q e) hxy
            calc
              x = (q e) (s e x) := by
                rw [← LinearMap.comp_apply, hs e]
                rfl
              _ = (q e) (s e y) := this
              _ = y := by
                rw [← LinearMap.comp_apply, hs e]
                rfl)
        let ep : LinearMap.range (s e) ≃ₗ[R] p e :=
          Submodule.equivMapOfInjective (F.stage e).subtype
            (F.stage e).subtype_injective _
        exact @Module.Projective.of_equiv' R _ (p e : Type u) _ _ (Q e) _ _
          (hprojM e) (es.trans ep)
      have hdir : ∀ e : E,
          Directed (· ≤ ·) (fun e' : {e' : E // e' < e} => F.stage e'.1) := by
        intro e a b
        refine ⟨⟨max a.1 b.1, max_lt a.2 b.2⟩, ?_, ?_⟩
        · exact F.monotone (le_max_left _ _)
        · exact F.monotone (le_max_right _ _)
      have hstage : ∀ e : E, F.stage e ≤ ⨆ e, p e := by
        intro e
        induction e using WellFoundedLT.induction with
        | ind e ih =>
            intro x hx
            let xe : F.stage e := ⟨x, hx⟩
            let z : Q e := q e xe
            let y : F.stage e := s e z
            have hy : (y : M) ∈ ⨆ e, p e := by
              apply Submodule.mem_iSup_of_mem e
              exact Submodule.mem_map_of_mem ⟨z, rfl⟩
            have hq : q e (xe - y) = 0 := by
              rw [map_sub]
              change q e xe - q e (s e z) = 0
              have hzs : q e (s e z) = z := by
                have := congrArg (fun f : Q e →ₗ[R] Q e => f z) (hs e)
                simpa [LinearMap.comp_apply] using this
              rw [show q e xe = z by rfl, hzs, sub_self]
            have hpred : xe - y ∈ F.predecessor e := by
              have hk : xe - y ∈ LinearMap.ker (q e) := by
                exact (LinearMap.mem_ker).mpr hq
              change xe - y ∈ LinearMap.ker ((F.predecessor e).mkQ) at hk
              rw [Submodule.ker_mkQ] at hk
              exact hk
            change (F.stage e).subtype (xe - y) ∈
                (⨆ e' : {e' : E // e' < e}, F.stage e'.1)
              at hpred
            by_cases hne : Nonempty {e' : E // e' < e}
            · obtain ⟨e', he'⟩ :=
                (@Submodule.mem_iSup_of_directed R M _ _ _
                  {e' : E // e' < e} hne _ (hdir e)).mp hpred
              have hi := ih e' e'.property
              have hxy : x - (y : M) ∈ ⨆ e, p e := by
                exact hi he'
              have hadd : x - (y : M) + (y : M) ∈ ⨆ e, p e := add_mem hxy hy
              simpa only [sub_add_cancel] using hadd
            · have hzero : (x - (y : M)) = 0 := by
                have hEmpty : IsEmpty {e' : E // e' < e} :=
                  ⟨fun e' => hne ⟨e'⟩⟩
                change (F.stage e).subtype (xe - y) ∈
                  (⨆ e' : {e' : E // e' < e}, F.stage e'.1) at hpred
                have : (F.stage e).subtype (xe - y) = 0 := by
                  rw [@iSup_of_empty _ _ _ hEmpty] at hpred
                  simpa using hpred
                exact this
              rw [sub_eq_zero.mp hzero]
              exact hy
      have htop : (⨆ e, p e) = (⊤ : Submodule R M) := by
        apply le_antisymm
        · exact le_top
        · rw [← F.exhaustive]
          exact iSup_le hstage
      let sectionLift := s
      have hsectionLift : ∀ e : E,
          (q e).comp (sectionLift e) = LinearMap.id := by
        intro e
        simpa [sectionLift] using hs e
      have hind : iSupIndep p := by
        rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
        intro t v hv hsum i hi
        have hzero : ∀ s : Finset E,
            (∀ j ∈ s, v j ∈ p j) →
              ((∑ j ∈ s, v j) = 0) → ∀ j ∈ s, v j = 0 := by
          intro s
          refine Finset.strongInductionOn s ?_
          intro s ih hs hsum' j hj
          let m : E := s.max' ⟨j, hj⟩
          have hm : m ∈ s := s.max'_mem ⟨j, hj⟩
          have hle : ∀ k ∈ s, k ≤ m := by
            intro k hk
            simpa [m] using s.le_max' k hk
          have hmem_stage : ∀ k ∈ s, v k ∈ F.stage k := by
            intro k hk
            rcases (Submodule.mem_map.mp (hs k hk)) with ⟨w, hw, hwv⟩
            rw [← hwv]
            exact w.property
          have hmem_m : ∀ k ∈ s, v k ∈ F.stage m := by
            intro k hk
            exact F.monotone (hle k hk) (hmem_stage k hk)
          have hsum_mem : (∑ k ∈ s, v k) ∈ F.stage m := by
            exact Submodule.sum_mem _ (fun k hk => hmem_m k hk)
          let vm : ∀ k : E, k ∈ s → F.stage m := fun k hk =>
            ⟨v k, hmem_m k hk⟩
          have hsum_stage :
              (∑ k ∈ s.attach, vm k.1 k.2) = ⟨∑ k ∈ s, v k, hsum_mem⟩ := by
            apply Subtype.ext
            simp only [Submodule.coe_sum]
            calc
              (∑ k ∈ s.attach, (vm k.1 k.2 : M)) =
                  ∑ k ∈ s.attach, v k.1 := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rfl
              _ = ∑ k ∈ s, v k := Finset.sum_attach s v
          have hqsum : (∑ k ∈ s.attach, q m (vm k.1 k.2)) = 0 := by
            have hsum_zero : (⟨∑ k ∈ s, v k, hsum_mem⟩ : F.stage m) = 0 := by
              apply Subtype.ext
              simpa using hsum'
            have h := congrArg (q m) hsum_stage
            rw [hsum_zero] at h
            simpa using h
          have hqpred : ∀ k ∈ s.attach, k.1 ≠ m →
              q m (vm k.1 k.2) = 0 := by
            intro k hk hkm
            have hlt : k.1 < m := lt_of_le_of_ne (hle k.1 k.2) hkm
            have hpred : vm k.1 k.2 ∈ F.predecessor m := by
              change (F.stage m).subtype (vm k.1 k.2) ∈
                (⨆ e' : {e' : E // e' < m}, F.stage e'.1)
              apply Submodule.mem_iSup_of_mem ⟨k.1, hlt⟩
              exact hmem_stage k.1 k.2
            apply (LinearMap.mem_ker).mp
            change vm k.1 k.2 ∈ LinearMap.ker ((F.predecessor m).mkQ)
            rw [Submodule.ker_mkQ]
            exact hpred
          have hqmax : q m (vm m hm) = 0 := by
            have h := hqsum
            rw [Finset.sum_eq_single (⟨m, hm⟩ : s.attach)] at h
            · simpa using h
            · intro k hk hkm
              exact hqpred k hk (fun h => hkm (Subtype.ext h))
            · intro hnot
              exact (hnot (by simp)).elim
          have hvm : v m = 0 := by
            rcases (Submodule.mem_map.mp (hs m hm)) with ⟨w, hw, hwv⟩
            rcases hw with ⟨z, hzw⟩
            have hvm_sub : vm m hm = sectionLift m z := by
              apply Subtype.ext
              change v m = (sectionLift m z : M)
              exact hwv.symm.trans ((congrArg (F.stage m).subtype hzw).symm)
            have hqz := congrArg (q m) hvm_sub
            have hq_lift : q m (sectionLift m z) = z := by
              have h := congrArg (fun f : Q m →ₗ[R] Q m => f z) (hsectionLift m)
              simpa [LinearMap.comp_apply] using h
            rw [hqmax, hq_lift] at hqz
            exact hqz.symm
          have hrest : ∀ k ∈ s.erase m, v k = 0 := by
            apply ih (s.erase m)
            · exact Finset.erase_ssubset hm
            · intro k hk
              exact hs k (Finset.mem_of_mem_erase hk)
            · have hsum_erase := hsum'
              rw [← Finset.sum_erase_add _ _ hm, hvm, add_zero] at hsum_erase
              exact hsum_erase
          by_cases hje : j = m
          · subst j
            exact hvm
          · exact hrest j (Finset.mem_erase.mpr ⟨hje, hj⟩)
        exact hzero t hv hsum i hi
      let hInternal : DirectSum.IsInternal p :=
        DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
      let e : (⨁ e, (p e : Type u)) ≃ₗ[R] M :=
        LinearEquiv.ofBijective (DirectSum.coeLinearMap p) hInternal
      have hprojDS : Module.Projective R (⨁ e, (p e : Type u)) := by
        apply Module.Projective.directSum_iff.mpr
        intro e
        exact hp e
      have hprojM : Module.Projective R M := by
        exact @Module.Projective.of_equiv' R _ M _ _ (⨁ e, (p e : Type u)) _ _
          hprojDS e.symm
      have hprojCat : CategoryTheory.Projective (ModuleCat.of R M) :=
        (IsProjective.iff_projective (ModuleCat.of R M : Type u)).mp hprojM
      exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero _).mp hprojCat
  | succ n ih =>
      sorry
-/

/-! ## Finite and cyclic modules -/

/-- Finite modules and cyclic quotient modules detect a finite global-dimension
bound. -/
theorem finite_global_dimension_criterion {R : Type u} [CommRing R] (n : ℕ) :
    List.TFAE
      [ HasGlobalDimensionLE R n,
        ∀ M : ModuleCat.{u} R, Module.Finite R M →
          CategoryTheory.HasProjectiveDimensionLE M n,
        ∀ I : Ideal R,
          CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n ] := by
  have hcyclic :
      (∀ I : Ideal R,
        CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n) →
      HasGlobalDimensionLE R n := by
    intro h M
    exact (by
        let M₀ : Type u := M
        let hWO := exists_wellFoundedLT M₀
        let : AddCommGroup M₀ := inferInstance
        let : Module R M₀ := inferInstance
        let : LinearOrder M₀ := hWO.choose
        let : WellFoundedLT M₀ := hWO.choose_spec
        let stage : M₀ → Submodule R M₀ :=
          fun e => Submodule.span R (Set.Iic e)
        let F : WellOrderedSubmoduleFiltration R M₀ M₀ :=
          { stage := stage
            monotone := by
              intro e₁ e₂ he
              apply Submodule.span_mono
              intro x hx
              exact Set.mem_Iic.mpr (hx.trans he)
            exhaustive := by
              rw [eq_top_iff]
              intro x hx
              exact (le_iSup (fun e => stage e) x)
                (Submodule.subset_span (Set.mem_Iic.mpr le_rfl)) }
        apply colimit_projective_dimension F n
        intro e
        let x : F.stage e :=
          ⟨e, by exact Submodule.subset_span (Set.mem_Iic.mpr le_rfl)⟩
        let g : R →ₗ[R] ((F.stage e : Type u) ⧸ F.predecessor e) :=
          (F.predecessor e).mkQ.comp (LinearMap.toSpanSingleton R (F.stage e) x)
        have hg : Function.Surjective g := by
          intro y
          obtain ⟨z, rfl⟩ := (F.predecessor e).mkQ_surjective y
          have hs : ∀ (a : M₀) (ha : a ∈ F.stage e),
              ∃ r : R, g r = (F.predecessor e).mkQ ⟨a, ha⟩ := by
            intro a ha
            induction ha using Submodule.span_induction with
          | mem a ha =>
              by_cases hae : a = e
              · subst a
                exact ⟨1, by simp [g, x]
                  ⟩
              · have hae' : a < e := lt_of_le_of_ne ha (by
                  intro h; exact hae h)
                have hpred : a ∈ (⨆ e' : {e' : M₀ // e' < e},
                    F.stage e'.1) := by
                  exact (le_iSup (fun e' : {e' : M₀ // e' < e} =>
                    F.stage e'.1) ⟨a, hae'⟩)
                    (Submodule.subset_span (Set.mem_Iic.mpr le_rfl))
                have hprede : (⟨a, Submodule.subset_span ha⟩ : F.stage e) ∈
                    F.predecessor e := by
                  change a ∈ (⨆ e' : {e' : M₀ // e' < e}, F.stage e'.1)
                  exact hpred
                exact ⟨0, by
                  rw [show g 0 = 0 by simp [g]]
                  exact (Submodule.Quotient.mk_eq_zero
                    (p := F.predecessor e)).mpr hprede |>.symm⟩
          | zero => exact ⟨0, by
              change g 0 = (F.predecessor e).mkQ ⟨0, _⟩
              rw [show g 0 = 0 by simp [g]]
              exact (Submodule.Quotient.mk_eq_zero
                (p := F.predecessor e)).mpr
                (F.predecessor e).zero_mem |>.symm
              ⟩
          | add a b ha hb hpa hpb =>
              obtain ⟨ra, hra⟩ := hpa
              obtain ⟨rb, hrb⟩ := hpb
              refine ⟨ra + rb, ?_⟩
              calc
                g (ra + rb) = g ra + g rb := map_add g ra rb
                _ = (F.predecessor e).mkQ ⟨a, ha⟩ +
                    (F.predecessor e).mkQ ⟨b, hb⟩ := by rw [hra, hrb]
                _ = (F.predecessor e).mkQ ⟨a + b, _⟩ := by
                  simpa using ((F.predecessor e).mkQ.map_add
                    ⟨a, ha⟩ ⟨b, hb⟩).symm
          | smul r a ha hpa =>
              obtain ⟨ra, hra⟩ := hpa
              refine ⟨r * ra, ?_⟩
              change g (r • ra) = (F.predecessor e).mkQ ⟨r • a, _⟩
              calc
                g (r • ra) = r • g ra := map_smul g r ra
                _ = r • (F.predecessor e).mkQ ⟨a, ha⟩ := by rw [hra]
                _ = (F.predecessor e).mkQ ⟨r • a, _⟩ := by
                  simpa using ((F.predecessor e).mkQ.map_smul r
                    ⟨a, ha⟩).symm
          obtain ⟨r, hr⟩ := hs z.1 z.2
          exact ⟨r, hr⟩
        let : CategoryTheory.HasProjectiveDimensionLE
            (ModuleCat.of R (R ⧸ LinearMap.ker g)) n := h (LinearMap.ker g)
        let eQ := LinearMap.quotKerEquivOfSurjective g hg
        let eQ' : (ModuleCat.of R (R ⧸ LinearMap.ker g) : Type u) ≃ₗ[R]
            (F.successiveQuotient e : Type u) := eQ
        exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv eQ' n)
  have hAB : HasGlobalDimensionLE R n ↔
      (∀ M : ModuleCat.{u} R, Module.Finite R M →
        CategoryTheory.HasProjectiveDimensionLE M n) := by
    constructor
    · intro h M hM
      exact h M
    · intro h M
      exact hcyclic (fun I => h (ModuleCat.of R (R ⧸ I)) (by infer_instance)) M
  have hBC :
      (∀ M : ModuleCat.{u} R, Module.Finite R M →
        CategoryTheory.HasProjectiveDimensionLE M n) ↔
      (∀ I : Ideal R,
        CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n) := by
    constructor
    · intro h I
      exact h (ModuleCat.of R (R ⧸ I))
        (by infer_instance)
    · intro h M hM
      exact hcyclic h M
  have hAC : HasGlobalDimensionLE R n ↔
      (∀ I : Ideal R,
        CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n) :=
    hAB.trans hBC
  change List.TFAE [
    HasGlobalDimensionLE R n,
    ∀ M : ModuleCat.{u} R, Module.Finite R M →
      CategoryTheory.HasProjectiveDimensionLE M n,
    ∀ I : Ideal R,
      CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n]
  apply List.tfae_of_forall (HasGlobalDimensionLE R n)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil] at ha
  rcases ha with rfl | rfl | rfl | h
  · exact Iff.rfl
  · exact hAB.symm
  · exact hAC.symm
  · exact False.elim h

/-! ## Localization -/

/-- Localization preserves the projective-dimension bound for a module and a
finite global-dimension bound for a ring. -/
theorem localize_projective_dimension {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (S : Submonoid R) (n : ℕ) :
      (CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n →
      CategoryTheory.HasProjectiveDimensionLE
        (ModuleCat.of (Localization S) (localizedModule S M)) n) ∧
      (HasGlobalDimensionLE R n → HasGlobalDimensionLE (Localization S) n) := by
  constructor
  · intro h
    let : CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n := h
    let : CategoryTheory.HasProjectiveDimensionLE
        (ModuleCat.localizedModule (ModuleCat.of R M) S) n :=
      ModuleCat.localizedModule_hasProjectiveDimensionLE n S (ModuleCat.of R M)
    let e : (ModuleCat.localizedModule (ModuleCat.of R M) S : Type u) ≃ₗ[Localization S]
        (ModuleCat.of (Localization S) (localizedModule S M) : Type u) :=
      Shrink.linearEquiv (Localization S) (LocalizedModule S M)
    exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e n
  · intro h M'
    let : Module R (M' : Type u) :=
      Module.compHom (M' : Type u) (algebraMap R (Localization S))
    let : IsScalarTower R (Localization S) (M' : Type u) :=
      IsScalarTower.of_compHom R (Localization S) (M' : Type u)
    let : CategoryTheory.HasProjectiveDimensionLE
        (ModuleCat.of R (M' : Type u)) n := h (ModuleCat.of R (M' : Type u))
    let : IsLocalizedModule S
        (LinearMap.id : (M' : Type u) →ₗ[R] (M' : Type u)) :=
      isLocalizedModule_id S (M' : Type u) (Localization S)
    let e₀ : LocalizedModule S (M' : Type u) ≃ₗ[R] (M' : Type u) :=
      IsLocalizedModule.linearEquiv S
        (LocalizedModule.mkLinearMap S (M' : Type u))
        (LinearMap.id : (M' : Type u) →ₗ[R] (M' : Type u))
    let e₁ : (ModuleCat.localizedModule (ModuleCat.of R (M' : Type u)) S : Type u) ≃ₗ[R]
        (M' : Type u) :=
      (Shrink.linearEquiv R (LocalizedModule S (M' : Type u))).trans e₀
    let e : (ModuleCat.localizedModule (ModuleCat.of R (M' : Type u)) S : Type u) ≃ₗ[Localization S]
        (M' : Type u) := e₁.extendScalarsOfIsLocalization S (Localization S)
    let : CategoryTheory.HasProjectiveDimensionLE
        (ModuleCat.localizedModule (ModuleCat.of R (M' : Type u)) S) n :=
      ModuleCat.localizedModule_hasProjectiveDimensionLE n S
        (ModuleCat.of R (M' : Type u))
    exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e n

end

end Formalization.Books.Algebra.Unit109
