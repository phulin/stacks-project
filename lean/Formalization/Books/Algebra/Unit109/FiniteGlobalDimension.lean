import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.Algebra.Unit85.ProjectiveModulesLocalRing
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Module.Projective

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

/-- The unbundled-module form of a short exact sequence
0 → K → P → M → 0. -/
def IsShortExactLinearSequence {R K P M : Type u} [Semiring R]
    [AddCommMonoid K] [AddCommMonoid P] [AddCommMonoid M]
    [Module R K] [Module R P] [Module R M]
    (c : K →ₗ[R] P) (p : P →ₗ[R] M) : Prop :=
  Function.Exact c p ∧ Function.Injective c ∧ Function.Surjective p

/-- The commutative diagram in the precise form of Schanuel's lemma.

The two displayed vertical arrows are bundled as linear equivalences, and the
two square-commutativity conditions are written using productLinearMap. -/
def SchanuelDiagram {R K L P₁ P₂ M : Type u} [Semiring R]
    [AddCommMonoid K] [AddCommMonoid L] [AddCommMonoid P₁] [AddCommMonoid P₂]
    [AddCommMonoid M] [Module R K] [Module R L] [Module R P₁] [Module R P₂]
    [Module R M] (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M) : Prop :=
  ∃ e₁ : (K × P₂) ≃ₗ[R] (P₁ × L),
    ∃ e₂ : (P₁ × P₂) ≃ₗ[R] (P₁ × P₂),
      e₂.toLinearMap.comp (productLinearMap c₁ (LinearMap.id : P₂ →ₗ[R] P₂)) =
          (productLinearMap (LinearMap.id : P₁ →ₗ[R] P₁) c₂).comp e₁.toLinearMap ∧
        productLinearMap p₁ (0 : P₂ →ₗ[R] M) =
          (productLinearMap (0 : P₁ →ₗ[R] M) p₂).comp e₂.toLinearMap

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
  sorry

/-- Projective dimension zero is the projective-module case. -/
theorem projective_dimension_zero_iff_projective {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) :
    HasProjectiveDimensionExactly M 0 ↔ Module.Projective R M := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Finiteness of global dimension is equivalent to the global dimension not
being infinite. -/
theorem hasFiniteGlobalDimension_iff_globalDimension_ne_top
    {R : Type u} [Ring R] :
    HasFiniteGlobalDimension R ↔ globalDimension R ≠ ⊤ := by
  sorry

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
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit109
