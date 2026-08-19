import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit90.CoherentRings
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# More on Algebra, Chapter 53: Abelian categories of modules

The category of modules is represented by Mathlib's `ModuleCat`.  Full
subcategories are specified by `ObjectProperty`, and the Serre conditions are
the canonical `IsSerreClass` and `IsWeakSerreClass` interfaces from the
homological-algebra formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.MoreAlgebra.Unit53

/-! ## The ambient category and coherent modules -/

/-- Mathlib's bundled category of `R`-modules. -/
abbrev moduleCategory (R : Type u) [CommRing R] := ModuleCat.{u} R

theorem moduleCategory_is_abelian (R : Type u) [CommRing R] :
    Nonempty (Abelian (moduleCategory R)) :=
  ⟨inferInstance⟩

/- The coherent-module property and category are the canonical declarations
   from More Algebra's earlier coherent-rings chapter. -/
abbrev coherentModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  Formalization.Books.Algebra.Unit90.coherentModuleProperty R

abbrev coherentModuleCategory (R : Type u) [CommRing R] :=
  (coherentModuleProperty R).FullSubcategory

instance coherentModuleProperty_isWeakSerreClass
    (R : Type u) [CommRing R] :
    (coherentModuleProperty R).IsWeakSerreClass := by
  let P := coherentModuleProperty R
  have hzero : P (0 : ModuleCat.{u} R) := by
    change Formalization.Books.Algebra.Unit90.IsCoherentModule R
      (0 : ModuleCat.{u} R)
    refine ⟨inferInstance, ?_⟩
    intro N _
    exact inferInstance
  have hIso : P.IsClosedUnderIsomorphisms := by
    refine { of_iso := ?_ }
    intro X Y e hX
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (0 : (0 : ModuleCat.{u} R) ⟶ X) e.hom (by simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · exact (S.exact_iff_mono (by simp [S])).2 inferInstance
      · infer_instance
      · infer_instance
    exact (Formalization.Books.Algebra.Unit90.coherent_of_shortExact hS).1
      ⟨hzero, hX⟩
  have hK : P.IsClosedUnderKernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
    have h := Formalization.Books.Algebra.Unit90.coherent_kernel_cokernel_of_coherent
      f hX hY
    exact P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (ModuleCat.kernelIsLimit f) hk) h.1
  have hC : P.IsClosedUnderCokernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, ⟨hX, hY⟩⟩
    have h := Formalization.Books.Algebra.Unit90.coherent_kernel_cokernel_of_coherent
      f hX hY
    exact P.prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit f) hk) h.2
  have hExt : P.IsClosedUnderExtensions := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    exact (Formalization.Books.Algebra.Unit90.coherent_of_shortExact hS).2.1
      ⟨h₁, h₃⟩
  exact (Formalization.Books.Homology.Unit10.weak_serre_subcategory_characterization P).2
    ⟨hzero, hIso, ⟨hK, hC⟩, hExt⟩

theorem coherentModuleCategory_is_abelian
    (R : Type u) [CommRing R] :
    Nonempty (Abelian (coherentModuleCategory R)) :=
  ⟨inferInstance⟩

/-! ## Modules on which a multiplicative subset acts invertibly -/

/-- The property that every element of `S` acts bijectively on a module. -/
abbrev localizationModuleProperty (R : Type u) [CommRing R] (S : Submonoid R) :
    ObjectProperty (moduleCategory R) :=
  Formalization.Books.Algebra.Unit09.localizationModuleProperty S

/-- The full subcategory of modules on which `S` acts by isomorphisms. -/
abbrev localizationModuleCategory (R : Type u) [CommRing R] (S : Submonoid R) :=
  (localizationModuleProperty R S).FullSubcategory

instance localizationModuleProperty_isSerreClass
    (R : Type u) [CommRing R] (S : Submonoid R) :
    (localizationModuleProperty R S).IsSerreClass := by
  sorry

theorem localizationModuleCategory_is_abelian
    (R : Type u) [CommRing R] (S : Submonoid R) :
    Nonempty (Abelian (localizationModuleCategory R S)) := by
  obtain ⟨e⟩ := Formalization.Books.Algebra.Unit09.localization_module_category_equivalence S
  letI : HasFiniteProducts (localizationModuleCategory R S) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact ⟨abelianOfEquivalence e.functor⟩

/-! ## Ideal-power torsion modules -/

/-- Every element of `M` is killed by a positive power of the ideal `I`. -/
def IsIPowerTorsion {R : Type u} [CommRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ x : M, ∃ n : ℕ, 0 < n ∧ ∀ a : R, a ∈ I ^ n → a • x = 0

/-- The object property of `I`-power torsion modules. -/
def iPowerTorsionModuleProperty (R : Type u) [CommRing R] (I : Ideal R) :
    ObjectProperty (moduleCategory R) :=
  fun M => IsIPowerTorsion I (M : Type u)

/-- The full subcategory of `I`-power torsion modules. -/
abbrev iPowerTorsionModuleCategory (R : Type u) [CommRing R] (I : Ideal R) :=
  (iPowerTorsionModuleProperty R I).FullSubcategory

theorem iPowerTorsionModuleProperty_isSerreClass
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    (iPowerTorsionModuleProperty R I).IsSerreClass := by
  classical
  let P := iPowerTorsionModuleProperty R I
  have hzero : P (0 : ModuleCat.{u} R) := by
    change IsIPowerTorsion I ((0 : ModuleCat.{u} R) : Type u)
    intro x
    refine ⟨1, by simp, ?_⟩
    intro a ha
    simp
  have hsub : P.IsClosedUnderSubobjects := by
    refine ⟨?_⟩
    intro X Y f _ hY
    change IsIPowerTorsion I (X : Type u)
    change IsIPowerTorsion I (Y : Type u) at hY
    intro x
    obtain ⟨n, hn, hkill⟩ := hY (f.hom x)
    refine ⟨n, hn, ?_⟩
    intro a ha
    have hinj : Function.Injective f.hom :=
      (ModuleCat.mono_iff_injective f).mp inferInstance
    apply hinj
    simpa only [map_smul, map_zero] using hkill a ha
  have hquot : P.IsClosedUnderQuotients := by
    refine ⟨?_⟩
    intro X Y f _ hX
    change IsIPowerTorsion I (Y : Type u)
    change IsIPowerTorsion I (X : Type u) at hX
    intro y
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance y
    obtain ⟨n, hn, hkill⟩ := hX x
    refine ⟨n, hn, ?_⟩
    intro a ha
    change a • f.hom x = 0
    rw [← map_smul, hkill a ha]
  have hiso : P.IsClosedUnderIsomorphisms := by
    letI : P.IsClosedUnderSubobjects := hsub
    exact inferInstance
  have hext : P.IsClosedUnderExtensions := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    change IsIPowerTorsion I (S.X₁ : Type u) at h₁
    change IsIPowerTorsion I (S.X₃ : Type u) at h₃
    change IsIPowerTorsion I (S.X₂ : Type u)
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    intro x
    obtain ⟨n, hn, h₃kill⟩ := h₃ (S.g.hom x)
    have hJ : (I ^ n).FG := Ideal.FG.pow (n := n) hI
    obtain ⟨t, ht⟩ := hJ
    have hex_mem : ∀ a : R, a ∈ t →
        ∃ y : (S.X₁ : Type u), S.f.hom y = a • x := by
      intro a ha
      obtain ⟨y, hy⟩ := (hex (a • x)).mp (by
        rw [map_smul, h₃kill a (by rw [← ht]; exact Ideal.subset_span ha)])
      exact ⟨y, hy⟩
    let yOf (a : R) : (S.X₁ : Type u) :=
      if ha : a ∈ t then Classical.choose (hex_mem a ha) else 0
    let mOf (a : R) : ℕ :=
      if ha : a ∈ t then (h₁ (yOf a)).choose else 0
    let m : ℕ := t.sup mOf
    have hyOf (a : R) (ha : a ∈ t) : S.f.hom (yOf a) = a • x := by
      dsimp [yOf]
      rw [dif_pos ha]
      exact Classical.choose_spec (hex_mem a ha)
    have hmOf (a : R) (ha : a ∈ t) :
        ∀ c : R, c ∈ I ^ mOf a → c • yOf a = 0 := by
      dsimp [mOf]
      rw [dif_pos ha]
      exact (h₁ (yOf a)).choose_spec.2
    have hQ : ∀ b : R, b ∈ I ^ n →
        ∀ c : R, c ∈ I ^ m → c • (b • x) = 0 := by
      intro b hb
      rw [← ht] at hb
      refine Submodule.span_induction
        (p := fun b _ => ∀ c : R, c ∈ I ^ m → c • (b • x) = 0) ?_ ?_ ?_ ?_ hb
      · intro a ha c hc
        have hle : mOf a ≤ m := Finset.le_sup ha
        have hc' : c ∈ I ^ mOf a :=
          (Ideal.pow_le_pow_right hle) hc
        calc
          c • (a • x) = c • S.f.hom (yOf a) := by rw [hyOf a ha]
          _ = S.f.hom (c • yOf a) := by rw [map_smul]
          _ = 0 := by rw [hmOf a ha c hc', map_zero]
      · intro c hc
        simp
      · intro b₁ b₂ hb₁ hb₂ hleft hright c hc
        rw [add_smul, smul_add, hleft c hc, hright c hc, add_zero]
      · intro r b hb hprev c hc
        calc
          c • ((r • b) • x) = c • (r • (b • x)) := by rw [smul_smul]
          _ = (c * r) • (b • x) := by rw [mul_smul]
          _ = 0 := hprev (c * r) ((I ^ m).mul_mem_left c hc)
    have hmul : I ^ n * I ^ m ≤ Ideal.torsionOf R x := by
      rw [Ideal.mul_le]
      intro b hb c hc
      apply (Ideal.mem_torsionOf_iff x (b * c)).2
      calc
        (b * c) • x = (c * b) • x := by rw [mul_comm]
        _ = c • (b • x) := by rw [mul_smul]
        _ = 0 := hQ b hb c hc
    refine ⟨n + m, Nat.add_pos_left hn m, ?_⟩
    intro a ha
    apply (Ideal.mem_torsionOf_iff x a).mp
    rw [Ideal.IsTwoSided.pow_add] at ha
    exact hmul ha
  exact (Formalization.Books.Homology.Unit10.serre_subcategory_characterization P).2
    ⟨hzero, hiso, ⟨hsub, hquot⟩, hext⟩

theorem iPowerTorsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    Nonempty (Abelian (iPowerTorsionModuleCategory R I)) := by
  let hSerre : (iPowerTorsionModuleProperty R I).IsSerreClass :=
    iPowerTorsionModuleProperty_isSerreClass R I hI
  exact ⟨by sorry⟩

/-! ## Torsion modules -/

/-- The property that every element is killed by a non-zero-divisor. -/
def torsionModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  fun M => Module.IsTorsion R (M : Type u)

/-- The full subcategory of torsion modules. -/
abbrev torsionModuleCategory (R : Type u) [CommRing R] :=
  (torsionModuleProperty R).FullSubcategory

instance torsionModuleProperty_isSerreClass
    (R : Type u) [CommRing R] :
    (torsionModuleProperty R).IsSerreClass := by
  sorry

theorem torsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] :
    Nonempty (Abelian (torsionModuleCategory R)) := by
  exact ⟨by sorry⟩

/-! ## Finitely generated modules and the non-Noetherian obstruction -/

/-- The property defining finitely generated modules. -/
abbrev finitelyGeneratedModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (moduleCategory R) :=
  ModuleCat.isFG R

/-- The full subcategory of finitely generated modules. -/
abbrev finitelyGeneratedModuleCategory (R : Type u) [CommRing R] :=
  FGModuleCat.{u} R

/-- The map `R → R/I`, viewed as a morphism of finitely generated modules. -/
def idealQuotientMap (R : Type u) [CommRing R] (I : Ideal R) :
    FGModuleCat.of R R ⟶ FGModuleCat.of R (R ⧸ I) :=
  FGModuleCat.ofHom (Ideal.Quotient.mkₐ R I).toLinearMap

/-- A non-finitely generated ideal gives a quotient map with no kernel in the
finitely generated module category. -/
theorem idealQuotientMap_has_no_kernel
    (R : Type u) [CommRing R] (I : Ideal R) (hI : ¬ I.FG) :
    ¬ HasKernel (idealQuotientMap R I) := by
  sorry

theorem finitelyGeneratedModuleCategory_not_abelian_of_not_noetherian
    (R : Type u) [CommRing R] (hR : ¬ IsNoetherianRing R) :
    ¬ Nonempty (Abelian (finitelyGeneratedModuleCategory R)) := by
  sorry

/-! ## The Noetherian case -/

/-- Over a Noetherian ring, coherence agrees with finite generation. -/
theorem coherentModuleProperty_iff_finitelyGenerated
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : moduleCategory R) :
    coherentModuleProperty R M ↔ finitelyGeneratedModuleProperty R M := by
  sorry

theorem finitelyGeneratedModuleCategory_is_abelian
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Nonempty (Abelian (finitelyGeneratedModuleCategory R)) :=
  ⟨inferInstance⟩

instance finitelyGeneratedModuleProperty_isSerreClass
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (finitelyGeneratedModuleProperty R).IsSerreClass := by
  sorry

end Formalization.Books.MoreAlgebra.Unit53
