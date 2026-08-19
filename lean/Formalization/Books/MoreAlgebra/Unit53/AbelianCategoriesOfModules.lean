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
  have hzero : P (ModuleCat.of R (Fin 0 → R)) := by
    change Formalization.Books.Algebra.Unit90.IsCoherentModule R
      (ModuleCat.of R (Fin 0 → R))
    refine ⟨inferInstance, ?_⟩
    intro N _
    exact inferInstance
  have hIso : P.IsClosedUnderIsomorphisms := by
    refine { of_iso := ?_ }
    intro X Y e hX
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (0 : (ModuleCat.of R (Fin 0 → R)) ⟶ X) e.hom (by simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · exact (S.exact_iff_mono (by simp [S])).2 inferInstance
      · exact (ModuleCat.mono_iff_injective S.f).2 (by
          intro x y _
          exact Subsingleton.elim _ _)
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
  /- Prior attempt: the intended characterization theorem is commented out in
     the imported Homology chapter, and its local reverse-direction proof also
     requires unavailable exactness elaboration support in this API.
  exact (Formalization.Books.Homology.Unit10.weak_serre_subcategory_characterization P).2
       ⟨hzero, hIso, ⟨hK, hC⟩, hExt⟩
  -/
  refine @CategoryTheory.ObjectProperty.IsWeakSerreClass.mk _ _ _ P ?_ ?_
  · exact ⟨ModuleCat.of R (Fin 0 → R), hzero⟩
  · intro S hS h₀ h₁ h₃ h₄
    let f₀ := CategoryTheory.ComposableArrows.map' S 0 1
    let f₁ := CategoryTheory.ComposableArrows.map' S 1 2
    let f₂ := CategoryTheory.ComposableArrows.map' S 2 3
    let f₃ := CategoryTheory.ComposableArrows.map' S 3 4
    let Q := cokernel f₀
    let K := kernel f₃
    let u := cokernel.desc f₀ f₁ (hS.toIsComplex.zero 0)
    let v := kernel.lift f₃ f₂ (hS.toIsComplex.zero 2)
    let : P.IsClosedUnderKernels := hK
    let : P.IsClosedUnderCokernels := hC
    have hQ : P Q := by
      exact P.prop_cokernel f₀ h₀ h₁
    have hK' : P K := by
      exact P.prop_kernel f₃ h₃ h₄
    let : Epi (cokernel.π f₀) := by infer_instance
    let : Mono (kernel.ι f₃) := by infer_instance
    let T₁ : ShortComplex (moduleCategory R) := ShortComplex.mk u f₂ (by
      apply (cancel_epi (cokernel.π f₀)).1
      dsimp [u]
      rw [← Category.assoc, cokernel.π_desc, hS.toIsComplex.zero 1]
      simp)
    have hT₁ : T₁.Exact := by
      let φ : S.sc hS.toIsComplex 1 ⟶ T₁ := ShortComplex.homMk
        (cokernel.π f₀) (𝟙 _) (𝟙 _)
        (by dsimp [T₁, u]; simp [f₁])
        (by dsimp [T₁]; simp [f₂])
      let : Epi φ.τ₁ := by
        change Epi (cokernel.π f₀)
        infer_instance
      let : IsIso φ.τ₂ := by
        change IsIso (𝟙 _)
        infer_instance
      let : Mono φ.τ₃ := by
        change Mono (𝟙 _)
        infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (hS.exact 1)
    let T : ShortComplex (moduleCategory R) := ShortComplex.mk u v (by
      apply (cancel_mono (kernel.ι f₃)).1
      dsimp [v]
      rw [Category.assoc, kernel.lift_ι]
      apply (cancel_epi (cokernel.π f₀)).1
      dsimp [u]
      rw [← Category.assoc, cokernel.π_desc, hS.toIsComplex.zero 1]
      simp)
    have hT : T.Exact := by
      let φ : T ⟶ T₁ := ShortComplex.homMk
        (𝟙 _) (𝟙 _) (kernel.ι f₃)
        (by dsimp [T, T₁]; simp)
        (by dsimp [T, T₁, v]; simp)
      let : Epi φ.τ₁ := by
        change Epi (𝟙 _)
        infer_instance
      let : IsIso φ.τ₂ := by
        change IsIso (𝟙 _)
        infer_instance
      let : Mono φ.τ₃ := by
        change Mono (kernel.ι f₃)
        infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT₁
    let : Mono u := by
      dsimp [u]
      exact (hS.exact 0).mono_cokernelDesc
    let : Epi v := by
      dsimp [v]
      exact (hS.exact 2).epi_kernelLift
    exact hExt.prop_X₂_of_shortExact
      (ShortComplex.ShortExact.mk' hT inferInstance inferInstance) hQ hK'

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

/- The localization property is closed under exact five-term sequences, but
   not under arbitrary ambient subobjects. -/
instance localizationModuleProperty_isWeakSerreClass
    (R : Type u) [CommRing R] (S : Submonoid R) :
    (localizationModuleProperty R S).IsWeakSerreClass := by
  let P := localizationModuleProperty R S
  refine @CategoryTheory.ObjectProperty.IsWeakSerreClass.mk _ _ _ P ?_ ?_
  · refine ⟨ModuleCat.of R (Fin 0 → R), ?_⟩
    intro s
    constructor
    · intro x y hxy
      exact Subsingleton.elim _ _
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  · intro T hT h₀ h₁ h₃ h₄
    change (∀ s : S, Function.Bijective
      (fun x : (T.obj' 0 : Type u) => (s : R) • x)) at h₀
    change (∀ s : S, Function.Bijective
      (fun x : (T.obj' 1 : Type u) => (s : R) • x)) at h₁
    change (∀ s : S, Function.Bijective
      (fun x : (T.obj' 3 : Type u) => (s : R) • x)) at h₃
    change (∀ s : S, Function.Bijective
      (fun x : (T.obj' 4 : Type u) => (s : R) • x)) at h₄
    change ∀ s : S, Function.Bijective
      (fun x : (T.obj' 2 : Type u) => (s : R) • x)
    intro s
    let f₀ := T.map' 0 1
    let f₁ := T.map' 1 2
    let f₂ := T.map' 2 3
    let f₃ := T.map' 3 4
    have h₀' : Function.Exact f₀.hom f₁.hom := by
      rw [LinearMap.exact_iff]
      exact (ShortComplex.moduleCat_exact_iff_range_eq_ker
        (T.sc (hT.toIsComplex) 0)).1 (hT.exact 0) |>.symm
    have h₁' : Function.Exact f₁.hom f₂.hom := by
      rw [LinearMap.exact_iff]
      exact (ShortComplex.moduleCat_exact_iff_range_eq_ker
        (T.sc (hT.toIsComplex) 1)).1 (hT.exact 1) |>.symm
    have h₂' : Function.Exact f₂.hom f₃.hom := by
      rw [LinearMap.exact_iff]
      exact (ShortComplex.moduleCat_exact_iff_range_eq_ker
        (T.sc (hT.toIsComplex) 2)).1 (hT.exact 2) |>.symm
    constructor
    · intro x y hxy
      change (s : R) • x = (s : R) • y at hxy
      have hf₂ : f₂.hom x = f₂.hom y := by
        apply (h₃ s).1
        change (s : R) • f₂.hom x = (s : R) • f₂.hom y
        rw [← map_smul, ← map_smul, hxy]
      have hdiff : f₂.hom (x - y) = 0 := by
        rw [map_sub, hf₂, sub_self]
      obtain ⟨z, hz⟩ := (h₁' (x - y)).mp hdiff
      have hf₁ : f₁.hom ((s : R) • z) = 0 := by
        rw [map_smul, hz, smul_sub, hxy, sub_self]
      obtain ⟨w, hw⟩ := (h₀' ((s : R) • z)).mp hf₁
      obtain ⟨v, hv⟩ := (h₀ s).2 w
      change (s : R) • v = w at hv
      have hz' : f₀.hom v = z := by
        apply (h₁ s).1
        change (s : R) • f₀.hom v = (s : R) • z
        rw [← map_smul, hv, hw]
      apply sub_eq_zero.mp
      rw [← hz, ← hz']
      exact congrArg (fun q => q v) (hT.toIsComplex.zero 0)
    · intro x
      obtain ⟨y, hy⟩ := (h₃ s).2 (f₂.hom x)
      change (s : R) • y = f₂.hom x at hy
      have hf₃ : f₃.hom y = 0 := by
        apply (h₄ s).1
        change (s : R) • f₃.hom y = (s : R) • 0
        simp only [smul_zero]
        rw [← map_smul, hy]
        exact congrArg (fun q => q x) (hT.toIsComplex.zero 2)
      obtain ⟨z, hz⟩ := (h₂' y).mp hf₃
      have hf₂ : f₂.hom ((s : R) • z - x) = 0 := by
        rw [map_sub, map_smul, hz, hy, sub_self]
      obtain ⟨w, hw⟩ := (h₁' ((s : R) • z - x)).mp hf₂
      obtain ⟨v, hv⟩ := (h₁ s).2 w
      change (s : R) • v = w at hv
      refine ⟨z - f₁.hom v, ?_⟩
      change (s : R) • (z - f₁.hom v) = x
      calc
        (s : R) • (z - f₁.hom v) =
            (s : R) • z - f₁.hom ((s : R) • v) := by
          rw [smul_sub, map_smul]
        _ = (s : R) • z - f₁.hom w := by rw [hv]
        _ = x := by rw [hw, sub_sub_cancel]

theorem localizationModuleCategory_is_abelian
    (R : Type u) [CommRing R] (S : Submonoid R) :
    Nonempty (Abelian (localizationModuleCategory R S)) := by
  obtain ⟨e⟩ := Formalization.Books.Algebra.Unit09.localization_module_category_equivalence S
  let : HasFiniteProducts (localizationModuleCategory R S) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  exact ⟨abelianOfEquivalence e.inverse⟩

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
  have hzero : P (ModuleCat.of R (Fin 0 → R)) := by
    change IsIPowerTorsion I ((ModuleCat.of R (Fin 0 → R)) : Type u)
    intro x
    refine ⟨1, by simp, ?_⟩
    intro a ha
    exact Subsingleton.elim _ _
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
    simpa only [map_smul, map_zero] using congrArg f.hom (hkill a ha)
  have hiso : P.IsClosedUnderIsomorphisms := by
    refine { of_iso := ?_ }
    intro X Y e hX
    exact hsub.prop_of_mono e.inv hX
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
      rw [if_pos ha]
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
          c • ((r • b) • x) = c • (r • (b • x)) := by
            simp [smul_smul]
          _ = (c * r) • (b • x) := by rw [mul_smul]
          _ = 0 := hprev (c * r) (by
            simpa [mul_comm] using (I ^ m).mul_mem_left r hc)
    have hmul : I ^ n * I ^ m ≤ Ideal.torsionOf R (S.X₂ : Type u) x := by
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
  have hZ : IsZero (ModuleCat.of R (Fin 0 → R)) :=
    ModuleCat.isZero_of_subsingleton _
  exact (Formalization.Books.Homology.Unit10.serre_subcategory_characterization P).2
    ⟨P.prop_of_iso (hZ.iso (isZero_zero (moduleCategory R))) hzero,
      hiso, ⟨hsub, hquot⟩, hext⟩

theorem iPowerTorsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    Nonempty (Abelian (iPowerTorsionModuleCategory R I)) := by
  let hSerre : (iPowerTorsionModuleProperty R I).IsSerreClass :=
    iPowerTorsionModuleProperty_isSerreClass R I hI
  let P : ObjectProperty (moduleCategory R) := iPowerTorsionModuleProperty R I
  let : P.IsSerreClass := hSerre
  let : P.IsClosedUnderSubobjects := hSerre.toIsClosedUnderSubobjects
  let : P.IsClosedUnderQuotients := hSerre.toIsClosedUnderQuotients
  let : P.IsClosedUnderExtensions := hSerre.toIsClosedUnderExtensions
  let : P.IsClosedUnderKernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, hXY⟩
    let : Mono (ModuleCat.kernelCone f).ι := by
      apply (ModuleCat.mono_iff_injective _).2
      intro x y hxy
      exact Subtype.ext hxy
    exact P.prop_of_iso
      (IsLimit.conePointUniqueUpToIso (ModuleCat.kernelIsLimit f) hk)
      (P.prop_of_mono (ModuleCat.kernelCone f).ι hXY.1)
  let : P.IsClosedUnderCokernels := by
    refine ⟨?_⟩
    intro Z hZ
    rcases hZ with ⟨f, k, hk, hXY⟩
    let : Epi (ModuleCat.cokernelCocone f).π := by
      apply (ModuleCat.epi_iff_surjective _).2
      change Function.Surjective (LinearMap.range f.hom).mkQ
      exact (LinearMap.range f.hom).mkQ_surjective
    exact P.prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit f) hk)
      (P.prop_of_epi (ModuleCat.cokernelCocone f).π hXY.2)
  let : P.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    exact P.prop_of_iso
      (IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _)
        (limit.isLimit F) (diagramIsoPair F).symm)
      (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  let : P.IsClosedUnderFiniteProducts := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ⟨inferInstance⟩

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
  classical
  let P := torsionModuleProperty R
  have hzero : P (ModuleCat.of R (Fin 0 → R)) := by
    change Module.IsTorsion R (Fin 0 → R)
    unfold Module.IsTorsion
    intro x
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact Subsingleton.elim _ _
  have hsub : P.IsClosedUnderSubobjects := by
    refine ⟨?_⟩
    intro X Y f _ hY
    change Module.IsTorsion R (X : Type u)
    change Module.IsTorsion R (Y : Type u) at hY
    unfold Module.IsTorsion at hY
    intro x
    rcases hY (x := f.hom x) with ⟨a, hkill⟩
    refine ⟨a, ?_⟩
    apply (ModuleCat.mono_iff_injective f).mp inferInstance
    rw [Submonoid.smul_def, map_smul, map_zero]
    change (a : R) • f.hom x = 0 at hkill
    exact hkill
  have hquot : P.IsClosedUnderQuotients := by
    refine ⟨?_⟩
    intro X Y f _ hX
    change Module.IsTorsion R (Y : Type u)
    change Module.IsTorsion R (X : Type u) at hX
    unfold Module.IsTorsion at hX
    intro y
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance y
    rcases hX (x := x) with ⟨a, hkill⟩
    refine ⟨a, ?_⟩
    rw [Submonoid.smul_def, ← map_smul]
    change (a : R) • x = 0 at hkill
    rw [hkill, map_zero]
  have hiso : P.IsClosedUnderIsomorphisms := by
    refine { of_iso := ?_ }
    intro X Y e hX
    exact hsub.prop_of_mono e.inv hX
  have hext : P.IsClosedUnderExtensions := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    change Module.IsTorsion R (S.X₁ : Type u) at h₁
    change Module.IsTorsion R (S.X₃ : Type u) at h₃
    change Module.IsTorsion R (S.X₂ : Type u)
    unfold Module.IsTorsion at h₁ h₃ ⊢
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    intro x
    rcases h₃ (x := S.g.hom x) with ⟨b, hb⟩
    have hgb : S.g.hom ((b : R) • x) = 0 := by
      rw [map_smul]
      change (b : R) • S.g.hom x = 0 at hb
      exact hb
    obtain ⟨y, hy⟩ := (hex ((b : R) • x)).mp hgb
    rcases h₁ (x := y) with ⟨a, ha⟩
    refine ⟨a * b, ?_⟩
    rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    calc
      (a : R) • ((b : R) • x) = (a : R) • S.f.hom y := by rw [← hy]
      _ = S.f.hom ((a : R) • y) := by rw [map_smul]
      _ = 0 := by
        rw [show (a : R) • y = 0 by
          change (a : R) • y = 0 at ha
          exact ha, map_zero]
  have hZ : IsZero (ModuleCat.of R (Fin 0 → R)) :=
    ModuleCat.isZero_of_subsingleton _
  exact (Formalization.Books.Homology.Unit10.serre_subcategory_characterization P).2
    ⟨P.prop_of_iso (hZ.iso (isZero_zero (moduleCategory R))) hzero,
      hiso, ⟨hsub, hquot⟩, hext⟩

theorem torsionModuleCategory_is_abelian
    (R : Type u) [CommRing R] :
    Nonempty (Abelian (torsionModuleCategory R)) := by
  let hSerre : (torsionModuleProperty R).IsSerreClass :=
    torsionModuleProperty_isSerreClass R
  let P : ObjectProperty (moduleCategory R) := torsionModuleProperty R
  let : P.IsSerreClass := hSerre
  let : P.IsClosedUnderKernels := inferInstance
  let : P.IsClosedUnderCokernels := inferInstance
  have hBin : P.IsClosedUnderBinaryProducts :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (P := P)
      (J := Discrete WalkingPair) (by
        intro j hj
        obtain ⟨F, hF⟩ := hj
        exact P.prop_of_iso
          (IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _)
            (limit.isLimit F) (diagramIsoPair F).symm)
          (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))
  have hFinite : P.IsClosedUnderFiniteProducts :=
    @ObjectProperty.IsClosedUnderFiniteProducts.mk' _ _ P inferInstance inferInstance hBin
  let : Abelian P.FullSubcategory :=
    @ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
      _ _ P inferInstance inferInstance inferInstance inferInstance hFinite
  exact ⟨inferInstance⟩

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
  intro hK
  let := hK
  let f := idealQuotientMap R I
  let k : kernel f ⟶ FGModuleCat.of R R := kernel.ι f
  have hrange : LinearMap.range k.hom.hom = I := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have hx : (Ideal.Quotient.mkₐ R I) (k.hom.hom y) = 0 := by
        have h := congrArg (fun q => q.hom y) (kernel.condition f)
        change f.hom (k.hom y) = 0 at h
        change f.hom (k.hom y) = 0
        exact h
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    · intro x hx
      let q : FGModuleCat.of R R ⟶ FGModuleCat.of R R :=
        FGModuleCat.ofHom (LinearMap.toSpanSingleton R R x)
      have hq : q ≫ f = 0 := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        change (Ideal.Quotient.mkₐ R I) (y • x) = 0
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        simpa [smul_eq_mul] using I.mul_mem_left y hx
      let l := kernel.lift f q hq
      have hl := kernel.lift_ι f q hq
      have hx' : k.hom.hom (l.hom.hom 1) = x := by
        have hval := congrArg (fun m => m.hom.hom 1) hl
        change k.hom.hom (l.hom.hom 1) = q.hom.hom 1 at hval
        calc
          k.hom.hom (l.hom.hom 1) = q.hom.hom 1 := hval
          _ = x := by
            change (LinearMap.toSpanSingleton R R x) 1 = x
            exact LinearMap.toSpanSingleton_apply_one R R x
      exact ⟨l.hom.hom 1, hx'⟩
  apply hI
  rw [← hrange]
  exact Submodule.fg_range _

theorem finitelyGeneratedModuleCategory_not_abelian_of_not_noetherian
    (R : Type u) [CommRing R] (hR : ¬ IsNoetherianRing R) :
    ¬ Nonempty (Abelian (finitelyGeneratedModuleCategory R)) := by
  classical
  intro hA
  rcases hA with ⟨hA⟩
  let := hA
  apply hR
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_contra hI
  exact (idealQuotientMap_has_no_kernel R I hI) inferInstance

/-! ## The Noetherian case -/

/-- Over a Noetherian ring, coherence agrees with finite generation. -/
theorem coherentModuleProperty_iff_finitelyGenerated
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : moduleCategory R) :
    coherentModuleProperty R M ↔ finitelyGeneratedModuleProperty R M := by
  change (Module.Finite R (M : Type u) ∧
    ∀ N : Submodule R (M : Type u),
      Module.Finite R (N : Type u) →
        Module.FinitePresentation R (N : Type u)) ↔
    Module.Finite R (M : Type u)
  constructor
  · exact And.left
  · intro hM
    refine ⟨hM, ?_⟩
    intro N hN
    exact Module.finitePresentation_of_finite R (N : Type u)

theorem finitelyGeneratedModuleCategory_is_abelian
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Nonempty (Abelian (finitelyGeneratedModuleCategory R)) :=
  ⟨inferInstance⟩

instance finitelyGeneratedModuleProperty_isSerreClass
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (finitelyGeneratedModuleProperty R).IsSerreClass := by
  refine @ObjectProperty.IsSerreClass.mk _ _ _ (finitelyGeneratedModuleProperty R) ?_ ?_ ?_ ?_
  · exact ⟨⟨ModuleCat.of R (Fin 0 → R), ModuleCat.isZero_of_subsingleton _,
      by
        change Module.Finite R (Fin 0 → R)
        infer_instance⟩⟩
  · refine ⟨?_⟩
    intro X Y f hf hY
    change Module.Finite R (X : Type u)
    change Module.Finite R (Y : Type u) at hY
    let _ : Module.Finite R (Y : Type u) := hY
    apply Module.Finite.of_injective f.hom
    exact (ModuleCat.mono_iff_injective f).mp hf
  · refine ⟨?_⟩
    intro X Y f hf hX
    change Module.Finite R (X : Type u) at hX
    change Module.Finite R (Y : Type u)
    let _ : Module.Finite R (X : Type u) := hX
    apply Module.Finite.of_surjective f.hom
    exact (ModuleCat.epi_iff_surjective f).mp hf
  · refine ⟨?_⟩
    intro S hS h₁ h₃
    change Module.Finite R (S.X₂ : Type u)
    apply (coherentModuleProperty_iff_finitelyGenerated R S.X₂).mp
    apply (Formalization.Books.Algebra.Unit90.coherent_of_shortExact hS).2.1
    exact ⟨(coherentModuleProperty_iff_finitelyGenerated R S.X₁).mpr h₁,
      (coherentModuleProperty_iff_finitelyGenerated R S.X₃).mpr h₃⟩

end Formalization.Books.MoreAlgebra.Unit53
