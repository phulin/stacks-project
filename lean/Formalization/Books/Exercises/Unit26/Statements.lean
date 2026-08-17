import Formalization.Books.Exercises.Unit26.Core
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
/- The quotient examples below use the canonical ideal-quotient ring API. -/

/-!
# Exercises, Chapter 26: Hilbert functions

The propositions below are the formal interfaces for the chapter's seven
exercises.  Their proofs are intentionally deferred to the proving stage.
-/

noncomputable section

universe u v

open CategoryTheory

namespace Formalization.Books.Exercises.Unit26

/-! ## Exercise 1: Euler–Poincaré functions over a field -/

/-- The value of an Euler–Poincaré function on the one-dimensional vector space. -/
def fieldEulerParameter {k : Type u} [Field k]
    (φ : EulerPoincareFunction k) : ℤ :=
  φ (FGModuleCat.of k k)

private theorem fgmodule_shortExact_finrank_add (k : Type u) [Field k]
    (S : ShortComplex (FGModuleCat k)) (hS : S.ShortExact) :
    Module.finrank k (S.X₂ : Type u) =
      Module.finrank k (S.X₁ : Type u) + Module.finrank k (S.X₃ : Type u) := by
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  let S' := S.map F
  have hExact : S'.Exact :=
    (ShortComplex.exact_map_iff_of_faithful S F).2 hS.exact
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  letI : CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan F := by infer_instance
  letI : CategoryTheory.Limits.PreservesColimitsOfShape
      CategoryTheory.Limits.WalkingSpan F := by infer_instance
  let f : (S.X₁ : Type u) →ₗ[k] (S.X₂ : Type u) := S.f.hom.hom
  let g : (S.X₂ : Type u) →ₗ[k] (S.X₃ : Type u) := S.g.hom.hom
  have hf : Function.Injective f := by
    change Function.Injective (F.map S.f).hom
    apply (ModuleCat.mono_iff_injective _).1
    exact F.map_mono S.f
  have hg : Function.Surjective g := by
    change Function.Surjective (F.map S.g).hom
    apply (ModuleCat.epi_iff_surjective _).1
    exact F.map_epi S.g
  have hfun : Function.Exact f g := by
    change Function.Exact (F.map S.f).hom (F.map S.g).hom
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').1 hExact
  have hrange : LinearMap.range f = LinearMap.ker g := hfun.linearMap_ker_eq.symm
  have hdim := g.finrank_range_add_finrank_ker
  have hrangeg : Module.finrank k (LinearMap.range g) =
      Module.finrank k (S.X₃ : Type u) := by
    rw [LinearMap.range_eq_top.mpr hg, finrank_top]
  have hker : Module.finrank k (LinearMap.ker g) =
      Module.finrank k (LinearMap.range f) := by
    rw [← hrange]
  have hrangef : Module.finrank k (LinearMap.range f) =
      Module.finrank k (S.X₁ : Type u) := LinearMap.finrank_range_of_inj hf
  change Module.finrank k (S.X₂ : Type u) =
    Module.finrank k (S.X₁ : Type u) + Module.finrank k (S.X₃ : Type u)
  calc
    Module.finrank k (S.X₂ : Type u) =
        Module.finrank k (LinearMap.range g) +
          Module.finrank k (LinearMap.ker g) := hdim.symm
    _ = Module.finrank k (S.X₃ : Type u) +
        Module.finrank k (LinearMap.range f) := by
      rw [show LinearMap.range g = ⊤ from LinearMap.range_eq_top.mpr hg,
        finrank_top, hker]
    _ = Module.finrank k (S.X₁ : Type u) +
        Module.finrank k (S.X₃ : Type u) := by rw [hrangef]; ac_rfl


/-- Explicit form of the field classification. -/
theorem eulerPoincareFunction_field_formula (k : Type u) [Field k]
    (φ : EulerPoincareFunction k) (M : FGModuleCat.{u} k) :
    φ M = fieldEulerParameter φ * (Module.finrank k (M : Type u) : ℤ) := by
  classical
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  have hzero : φ (FGModuleCat.of k (Fin 0 → k)) = 0 := by
    let Z : Type u := Fin 0 → k
    letI : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat k) :=
        ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.id : Z →ₗ[k] Z))
        (FGModuleCat.ofHom (0 : Z →ₗ[k] Z)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (0 : Z) = 0
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x _
        exact ⟨x, by change x = x; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact h
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro y
        exact ⟨0, by change (0 : Z) = y; exact Subsingleton.elim _ _⟩
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of k Z) =
        φ (FGModuleCat.of k Z) + φ (FGModuleCat.of k Z) := by
      simpa [S] using h
    have : φ (FGModuleCat.of k Z) = 0 := by omega
    simpa [Z] using this
  have hIso : ∀ {V W : Type u} [AddCommGroup V] [Module k V]
      [Module.Finite k V] [AddCommGroup W] [Module k W] [Module.Finite k W],
      (V ≃ₗ[k] W) →
        φ (FGModuleCat.of k V) = φ (FGModuleCat.of k W) := by
    intro V W _ _ _ _ _ _ e
    let Z : Type u := Fin 0 → k
    letI : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat k) :=
        ShortComplex.mk
        (FGModuleCat.ofHom (0 : Z →ₗ[k] V))
        (FGModuleCat.ofHom e.toLinearMap) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change e.toLinearMap (0 : V) = 0
          simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x hx
        change e x = 0 at hx
        have hx0 : x = 0 := e.injective (hx.trans e.map_zero.symm)
        exact ⟨0, by change (0 : V) = x; rw [hx0]; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact @Subsingleton.elim Z this (x : Z) (y : Z)
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact e.surjective
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of k V) =
        φ (FGModuleCat.of k Z) + φ (FGModuleCat.of k W) := by
      simpa [S] using h
    simpa [Z, hzero, add_zero] using h'
  have hformula : ∀ (n : ℕ) (V : Type u) [AddCommGroup V] [Module k V]
      [Module.Finite k V], Module.finrank k V = n →
        φ (FGModuleCat.of k V) = fieldEulerParameter φ * (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ _ _ hV
        by_cases hn : n = 0
        · have hsub : Subsingleton V :=
            Module.finrank_zero_iff.mp (by simpa [hn] using hV)
          let S : ShortComplex (FGModuleCat k) :=
            ShortComplex.mk
              (FGModuleCat.ofHom (LinearMap.id : V →ₗ[k] V))
              (FGModuleCat.ofHom (0 : V →ₗ[k] V)) (by
                apply FGModuleCat.hom_ext
                apply LinearMap.ext
                intro x
                change (0 : V) = 0
                rfl)
          have hS : S.ShortExact := by
            apply ShortComplex.ShortExact.mk'
            · apply (ShortComplex.exact_map_iff_of_faithful S F).1
              apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
              intro x _
              exact ⟨x, by change x = x; rfl⟩
            · apply F.mono_of_mono_map
              apply (ModuleCat.mono_iff_injective _).2
              intro x y h
              exact h
            · apply F.epi_of_epi_map
              apply (ModuleCat.epi_iff_surjective _).2
              intro y
              exact ⟨0, by change (0 : V) = y; exact hsub.elim _ _⟩
          have h := φ.map_shortExact' S hS
          have h' : φ (FGModuleCat.of k V) =
              φ (FGModuleCat.of k V) + φ (FGModuleCat.of k V) := by
            simpa [S] using h
          have hz : φ (FGModuleCat.of k V) = 0 := by omega
          simpa [hz, hn]
        · have hnpos : 0 < Module.finrank k V := by
            rw [hV]
            exact Nat.pos_of_ne_zero hn
          obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hnpos
          let L : Submodule k V := k ∙ x
          let Q : Type u := V ⧸ L
          have hL : Module.finrank k L = 1 := by
            exact finrank_span_singleton hx
          have hdim := Submodule.finrank_quotient_add_finrank L
          have hdim' : Module.finrank k Q + 1 = n := by
            simpa [Q, hL, hV] using hdim
          have hQlt : Module.finrank k Q < n := by omega
          have hQ := ih (Module.finrank k Q) hQlt Q rfl
          have hLφ : φ (FGModuleCat.of k L) = fieldEulerParameter φ := by
            simpa [L, fieldEulerParameter] using
              (hIso (LinearEquiv.toSpanNonzeroSingleton k V x hx)).symm
          let S : ShortComplex (FGModuleCat k) :=
            ShortComplex.mk
              (FGModuleCat.ofHom L.subtype)
              (FGModuleCat.ofHom L.mkQ) (by
                ext x
                change L.mkQ (L.subtype x) = 0
                simp)
          have hS : S.ShortExact := by
            apply ShortComplex.ShortExact.mk'
            · apply (ShortComplex.exact_map_iff_of_faithful S F).1
              apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
              intro v hv
              change L.mkQ v = 0 at hv
              have hv' : v ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hv
              exact ⟨⟨v, hv'⟩, rfl⟩
            · apply F.mono_of_mono_map
              apply (ModuleCat.mono_iff_injective _).2
              intro x y h
              exact Subtype.ext h
            · apply F.epi_of_epi_map
              apply (ModuleCat.epi_iff_surjective _).2
              intro q
              obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L q
              exact ⟨v, rfl⟩
          have h := φ.map_shortExact' S hS
          have h' : φ (FGModuleCat.of k V) =
              φ (FGModuleCat.of k L) + φ (FGModuleCat.of k Q) := by
            simpa [S] using h
          calc
            φ (FGModuleCat.of k V) =
                φ (FGModuleCat.of k L) + φ (FGModuleCat.of k Q) := h'
            _ = fieldEulerParameter φ +
                fieldEulerParameter φ * (Module.finrank k Q : ℤ) := by
              rw [hLφ, hQ]
            _ = fieldEulerParameter φ * (n : ℤ) := by
              rw [← hdim', Nat.cast_add]
              ring
  simpa [fieldEulerParameter] using
    hformula (Module.finrank k (M : Type u)) (M : Type u) rfl

/-- Over a field, an Euler–Poincaré function is determined by its value on `k`.
The bijectivity statement packages both the classification and the existence of
all integer-valued choices. -/
theorem eulerPoincareFunction_field_classification (k : Type u) [Field k] :
    Function.Bijective (fieldEulerParameter (k := k)) := by
  classical
  constructor
  · intro φ ψ h
    cases φ with
    | mk φ hφ =>
      cases ψ with
      | mk ψ hψ =>
        have hparam : φ (FGModuleCat.of k k) = ψ (FGModuleCat.of k k) := by
          simpa [fieldEulerParameter] using h
        have hfun : φ = ψ := by
          funext M
          have hφM := eulerPoincareFunction_field_formula k
            (⟨φ, hφ⟩ : EulerPoincareFunction k) M
          have hψM := eulerPoincareFunction_field_formula k
            (⟨ψ, hψ⟩ : EulerPoincareFunction k) M
          calc
            φ M = φ (FGModuleCat.of k k) *
                (Module.finrank k (M : Type u) : ℤ) := by
              simpa [fieldEulerParameter] using hφM
            _ = ψ (FGModuleCat.of k k) *
                (Module.finrank k (M : Type u) : ℤ) := by rw [hparam]
            _ = ψ M := by
              simpa [fieldEulerParameter] using hψM.symm
        cases hfun
        rfl
  · intro z
    let φz : EulerPoincareFunction k :=
      { toFun := fun M => z * (Module.finrank k (M : Type u) : ℤ)
        map_shortExact' := by
          intro S hS
          have hdim := fgmodule_shortExact_finrank_add k S hS
          change z * (Module.finrank k (S.X₂ : Type u) : ℤ) =
            z * (Module.finrank k (S.X₁ : Type u) : ℤ) +
              z * (Module.finrank k (S.X₃ : Type u) : ℤ)
          rw [hdim, Nat.cast_add, mul_add] }
    refine ⟨φz, ?_⟩
    simp [φz, fieldEulerParameter]


/-! ## Exercise 2: Euler–Poincaré functions over the integers -/

/-- The value of an Euler–Poincaré function on the rank-one free `ℤ`-module. -/
def integerEulerParameter (φ : EulerPoincareFunction ℤ) : ℤ :=
  φ (FGModuleCat.of ℤ ℤ)

/-- Additivity forces every finite torsion module to have value zero, so an
Euler–Poincaré function on finitely generated abelian groups is determined by
its single value on `ℤ`. -/
theorem eulerPoincareFunction_integer_classification :
    Function.Bijective integerEulerParameter := by
  classical
  let F := forget₂ (FGModuleCat ℤ) (ModuleCat ℤ)
  have hzero : ∀ (φ : EulerPoincareFunction ℤ),
      φ (FGModuleCat.of ℤ (Fin 0 → ℤ)) = 0 := by
    intro φ
    let Z : Type := Fin 0 → ℤ
    letI : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.id : Z →ₗ[ℤ] Z))
        (FGModuleCat.ofHom (0 : Z →ₗ[ℤ] Z)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (0 : Z) = 0
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x _
        exact ⟨x, by change x = x; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact h
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        intro y
        exact ⟨0, by change (0 : Z) = y; exact Subsingleton.elim _ _⟩
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ Z) =
        φ (FGModuleCat.of ℤ Z) + φ (FGModuleCat.of ℤ Z) := by
      simpa [S] using h
    have hz : φ (FGModuleCat.of ℤ Z) = 0 := by omega
    simpa [Z] using hz
  have hIso : ∀ (φ : EulerPoincareFunction ℤ)
      {V W : Type} [AddCommGroup V] [Module ℤ V]
      [Module.Finite ℤ V] [AddCommGroup W] [Module ℤ W]
      [Module.Finite ℤ W],
      (V ≃ₗ[ℤ] W) →
        φ (FGModuleCat.of ℤ V) = φ (FGModuleCat.of ℤ W) := by
    intro φ V W _ _ _ _ _ _ e
    let Z : Type := Fin 0 → ℤ
    letI : Subsingleton Z := by
      dsimp [Z]
      infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (0 : Z →ₗ[ℤ] V))
        (FGModuleCat.ofHom e.toLinearMap) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change e.toLinearMap (0 : V) = 0
          simp)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.moduleCat_exact_iff (S.map F)).2
        intro x hx
        change e x = 0 at hx
        have hx0 : x = 0 := e.injective (hx.trans e.map_zero.symm)
        exact ⟨0, by change (0 : V) = x; rw [hx0]; rfl⟩
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        intro x y h
        exact @Subsingleton.elim Z _ (x : Z) (y : Z)
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact e.surjective
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ V) =
        φ (FGModuleCat.of ℤ Z) + φ (FGModuleCat.of ℤ W) := by
      simpa [S] using h
    simpa [Z, hzero φ, add_zero] using h'
  have hprod : ∀ (φ : EulerPoincareFunction ℤ)
      {V W : Type} [AddCommGroup V] [Module ℤ V]
      [Module.Finite ℤ V] [AddCommGroup W] [Module ℤ W]
      [Module.Finite ℤ W],
      let P : Type := V × W
      letI : Module ℤ P := Prod.instModule
      φ (FGModuleCat.of ℤ P) =
        φ (FGModuleCat.of ℤ V) + φ (FGModuleCat.of ℤ W) := by
    intro φ V W _ _ _ _ _ _
    let P : Type := V × W
    letI : Module ℤ P := Prod.instModule
    letI : Module.Finite ℤ P := by infer_instance
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom (LinearMap.inl ℤ V W))
        (FGModuleCat.ofHom (LinearMap.snd ℤ V W)) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        change Function.Exact (LinearMap.inl ℤ V W) (LinearMap.snd ℤ V W)
        exact Function.Exact.inl_snd
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        change Function.Injective (LinearMap.inl ℤ V W)
        exact LinearMap.inl_injective
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        change Function.Surjective (LinearMap.snd ℤ V W)
        intro y
        exact ⟨(0, y), rfl⟩
    have h := φ.map_shortExact' S hS
    simpa [S] using h
  have hsubzero : ∀ (φ : EulerPoincareFunction ℤ)
      {V : Type} [AddCommGroup V] [Module ℤ V] [Module.Finite ℤ V]
      [Subsingleton V], φ (FGModuleCat.of ℤ V) = 0 := by
    intro φ V _ _ _ _
    let e : V ≃ₗ[ℤ] (Fin 0 → ℤ) :=
      LinearEquiv.ofBijective 0 (by
        constructor
        · intro x y _
          exact Subsingleton.elim _ _
        · intro y
          exact ⟨0, Subsingleton.elim _ _⟩)
    simpa [hzero φ] using hIso φ e
  have hDS : ∀ (ι : Type) [Fintype ι] (Q : ι → Type)
      [∀ i, AddCommGroup (Q i)] [∀ i, Module ℤ (Q i)]
      [∀ i, Module.Finite ℤ (Q i)]
      [Module.Finite ℤ (DirectSum ι Q)] (φ : EulerPoincareFunction ℤ),
      φ (FGModuleCat.of ℤ (DirectSum ι Q)) =
        ∑ i : ι, φ (FGModuleCat.of ℤ (Q i)) := by
    intro ι
    refine Fintype.induction_empty_option
      (P := fun ι _ => ∀ (Q : ι → Type)
        [∀ i, AddCommGroup (Q i)] [∀ i, Module ℤ (Q i)]
        [∀ i, Module.Finite ℤ (Q i)]
        [Module.Finite ℤ (DirectSum ι Q)] (φ : EulerPoincareFunction ℤ),
        φ (FGModuleCat.of ℤ (DirectSum ι Q)) =
          ∑ i : ι, φ (FGModuleCat.of ℤ (Q i))) ?_ ?_ ?_ ι
    · intro α β _ e h Q hQadd hQmod hQfinite hQdirect φ
      letI : Fintype α := Fintype.ofEquiv β e.symm
      letI : ∀ i, AddCommGroup (Q i) := hQadd
      letI : ∀ i, Module ℤ (Q i) := hQmod
      letI : ∀ i, Module.Finite ℤ (Q i) := hQfinite
      letI : ∀ i, AddCommGroup (Q (e i)) := fun i => hQadd (e i)
      letI : ∀ i, Module ℤ (Q (e i)) := fun i => hQmod (e i)
      letI : ∀ i, Module.Finite ℤ (Q (e i)) := fun i => hQfinite (e i)
      letI : Module ℤ (DirectSum α (fun i => Q (e i))) :=
        @DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (e i))
          (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
          (fun i => hQmod (e i))
      have hfiniteDS :
          @Module.Finite ℤ (DirectSum α (fun i => Q (e i))) Int.instSemiring
            (@AddCommGroup.toAddCommMonoid _
              (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
            (AddCommGroup.toIntModule _) := by
        exact @Module.Finite.equiv ℤ
          (DirectSum α (fun i => Q (e i)))
          (DirectSum α (fun i => Q (e i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
          (@DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i)))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (e i)))))
          (AddCommGroup.toIntModule _)
          (@Module.Finite.instDirectSum ℤ α Int.instSemiring inferInstance
            (fun i => Q (e i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
            (fun i => hQmod (e i))
            (fun i => hQfinite (e i)))
          ((AddEquiv.refl (DirectSum α (fun i => Q (e i)))).toIntLinearEquiv
            (modM := @DirectSum.instModule ℤ Int.instSemiring α
              (fun i => Q (e i))
              (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (e i)))
              (fun i => hQmod (e i)))
            (modM₂ := AddCommGroup.toIntModule _))
      letI : Module ℤ (DirectSum α (fun i => Q (e i))) :=
        AddCommGroup.toIntModule _
      letI : Module.Finite ℤ (DirectSum α (fun i => Q (e i))) := hfiniteDS
      have h' :=
        @h (fun i => Q (e i))
          (fun i => hQadd (e i))
          (fun i => hQmod (e i))
          (fun i => hQfinite (e i))
          hfiniteDS φ
      have he :
          φ (FGModuleCat.of ℤ (DirectSum β Q)) =
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (e i)))) :=
        hIso φ ((DirectSum.equivCongrLeft (β := Q) e.symm).toIntLinearEquiv)
      calc
        φ (FGModuleCat.of ℤ (DirectSum β Q)) =
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (e i)))) := he
        _ = ∑ i : α, φ (FGModuleCat.of ℤ (Q (e i))) := h'
        _ = ∑ i : β, φ (FGModuleCat.of ℤ (Q i)) := by
          exact e.sum_comp (fun i => φ (FGModuleCat.of ℤ (Q i)))
    · intro Q hQadd hQmod hQfinite hQdirect φ
      have h := hsubzero φ (V := DirectSum PEmpty Q)
      simpa using h
    · intro α _ h Q hQadd hQmod hQfinite hQdirect φ
      letI : ∀ i, AddCommGroup (Q i) := hQadd
      letI : ∀ i, Module ℤ (Q i) := hQmod
      letI : ∀ i, Module.Finite ℤ (Q i) := hQfinite
      letI : ∀ i, AddCommGroup (Q (some i)) := fun i => hQadd (some i)
      letI : ∀ i, Module ℤ (Q (some i)) := fun i => hQmod (some i)
      letI : ∀ i, Module.Finite ℤ (Q (some i)) := fun i => hQfinite (some i)
      letI : Module ℤ (DirectSum α (fun i => Q (some i))) :=
        @DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (some i))
          (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
          (fun i => hQmod (some i))
      letI : AddCommGroup (Q none) := hQadd none
      letI : Module ℤ (Q none) := hQmod none
      letI : Module.Finite ℤ (Q none) := hQfinite none
      have hfiniteDS :
          @Module.Finite ℤ (DirectSum α (fun i => Q (some i))) Int.instSemiring
            (@AddCommGroup.toAddCommMonoid _
              (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
            (AddCommGroup.toIntModule _) := by
        exact @Module.Finite.equiv ℤ
          (DirectSum α (fun i => Q (some i)))
          (DirectSum α (fun i => Q (some i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (@DirectSum.instModule ℤ Int.instSemiring α (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i)))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (AddCommGroup.toIntModule _)
          (@Module.Finite.instDirectSum ℤ α Int.instSemiring inferInstance
            (fun i => Q (some i))
            (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
            (fun i => hQmod (some i))
            (fun i => hQfinite (some i)))
          ((AddEquiv.refl (DirectSum α (fun i => Q (some i)))).toIntLinearEquiv
            (modM := @DirectSum.instModule ℤ Int.instSemiring α
              (fun i => Q (some i))
              (fun i => @AddCommGroup.toAddCommMonoid _ (hQadd (some i)))
              (fun i => hQmod (some i)))
            (modM₂ := AddCommGroup.toIntModule _))
      letI : Module ℤ (DirectSum α (fun i => Q (some i))) :=
        AddCommGroup.toIntModule _
      letI : Module.Finite ℤ (DirectSum α (fun i => Q (some i))) := hfiniteDS
      letI : Module ℤ
          (Q none × DirectSum α (fun i => Q (some i))) :=
        @Prod.instModule ℤ (Q none) (DirectSum α (fun i => Q (some i)))
          Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _ (hQadd none))
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (hQmod none) (AddCommGroup.toIntModule _)
      letI : Module.Finite ℤ
          (Q none × DirectSum α (fun i => Q (some i))) := by
        exact @Module.Finite.prod ℤ (Q none)
          (DirectSum α (fun i => Q (some i))) Int.instSemiring
          (@AddCommGroup.toAddCommMonoid _ (hQadd none)) (hQmod none)
          (@AddCommGroup.toAddCommMonoid _
            (inferInstance : AddCommGroup (DirectSum α (fun i => Q (some i)))))
          (AddCommGroup.toIntModule _) (hQfinite none) hfiniteDS
      have h' :=
        @h (fun i => Q (some i))
          (fun i => hQadd (some i))
          (fun i => hQmod (some i))
          (fun i => hQfinite (some i))
          hfiniteDS φ
      have he :
        φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ
              (Q none × DirectSum α (fun i => Q (some i)))) :=
        hIso φ ((DirectSum.addEquivProdDirectSum (α := Q)).toIntLinearEquiv)
      calc
        φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ (Q none × DirectSum α (fun i => Q (some i)))) := he
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            φ (FGModuleCat.of ℤ (DirectSum α (fun i => Q (some i)))) := by
          simpa only using
            (hprod φ (V := Q none)
              (W := DirectSum α (fun i => Q (some i))))
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            ∑ i : α, φ (FGModuleCat.of ℤ (Q (some i))) := by rw [h']
        _ = ∑ i : Option α, φ (FGModuleCat.of ℤ (Q i)) := by
          simp [Fintype.sum_option]
  have hfree : ∀ (φ : EulerPoincareFunction ℤ) (n : ℕ),
      φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
        integerEulerParameter φ * (n : ℤ) := by
    intro φ n
    letI : Module.Finite ℤ (DirectSum (Fin n) (fun _ => ℤ)) :=
      Module.Finite.instDirectSum _
    have h := hDS (Fin n) (fun _ => ℤ) φ
    change φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
      φ (FGModuleCat.of ℤ ℤ) * (n : ℤ)
    calc
      φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
          φ (FGModuleCat.of ℤ (DirectSum (Fin n) (fun _ => ℤ))) :=
        hIso φ (finsuppLEquivDirectSum ℤ ℤ (Fin n))
      _ = ∑ i : Fin n, φ (FGModuleCat.of ℤ ℤ) := h
      _ = φ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcyclic : ∀ (φ : EulerPoincareFunction ℤ) (a : ℤ) (ha : a ≠ 0),
      φ (FGModuleCat.of ℤ (ℤ ⧸ ℤ ∙ a)) = 0 := by
    intro φ a ha
    let L : Submodule ℤ ℤ := ℤ ∙ a
    let Q : Type := ℤ ⧸ L
    let f : ℤ →ₗ[ℤ] ℤ := LinearMap.toSpanSingleton ℤ ℤ a
    let g : ℤ →ₗ[ℤ] Q := L.mkQ
    letI : Module.Finite ℤ Q := by infer_instance
    have hcomp : g.comp f = 0 := by
      ext x
      apply (Submodule.Quotient.mk_eq_zero L).mpr
      simpa [f, LinearMap.toSpanSingleton_apply, smul_eq_mul, L] using
        (Submodule.mem_span_singleton_self a : a ∈ ℤ ∙ a)
    have hker : ∀ x, g x = 0 → x ∈ LinearMap.range f := by
      intro x hx
      have hxL : x ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hx
      rcases (Submodule.mem_span_singleton.mp hxL) with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simpa [f, LinearMap.toSpanSingleton_apply, L, smul_eq_mul] using hc
    have hfun : Function.Exact f g :=
      LinearMap.exact_of_comp_of_mem_range hcomp hker
    have hf : Function.Injective f := by
      intro x y hxy
      apply mul_right_cancel₀ ha
      simpa [f, LinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    have hg : Function.Surjective g := by
      exact L.mkQ_surjective
    let S : ShortComplex (FGModuleCat ℤ) :=
      ShortComplex.mk
        (FGModuleCat.ofHom f)
        (FGModuleCat.ofHom g) (by
          apply FGModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change g (f x) = 0
          exact DFunLike.congr_fun hcomp x)
    have hS : S.ShortExact := by
      apply ShortComplex.ShortExact.mk'
      · apply (ShortComplex.exact_map_iff_of_faithful S F).1
        apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).2
        exact hfun
      · apply F.mono_of_mono_map
        apply (ModuleCat.mono_iff_injective _).2
        exact hf
      · apply F.epi_of_epi_map
        apply (ModuleCat.epi_iff_surjective _).2
        exact hg
    have h := φ.map_shortExact' S hS
    have h' : φ (FGModuleCat.of ℤ ℤ) =
        φ (FGModuleCat.of ℤ ℤ) + φ (FGModuleCat.of ℤ Q) := by
      simpa only [S] using h
    have hz : φ (FGModuleCat.of ℤ Q) = 0 := by
      omega
    simpa [Q, L] using hz
  have hclass : ∀ (φ ψ : EulerPoincareFunction ℤ) (M : FGModuleCat ℤ),
      ∃ n : ℕ,
        φ M = integerEulerParameter φ * (n : ℤ) ∧
          ψ M = integerEulerParameter ψ * (n : ℤ) := by
    intro φ ψ M
    obtain ⟨n, ι, fι, p, hp, powExp, ⟨eM⟩⟩ :=
      Module.equiv_free_prod_directSum (R := ℤ) (M := (M : Type))
    letI : Fintype ι := fι
    let Q : ι → Type := fun i => ℤ ⧸ ℤ ∙ p i ^ powExp i
    letI : Module.Finite ℤ (DirectSum ι Q) :=
      Module.Finite.instDirectSum Q
    have hvalue : ∀ θ : EulerPoincareFunction ℤ,
        θ (FGModuleCat.of ℤ (M : Type)) =
          integerEulerParameter θ * (n : ℤ) := by
      intro θ
      have hsum : ∑ i : ι, θ (FGModuleCat.of ℤ (Q i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simpa [Q] using
          hcyclic θ (p i ^ powExp i) (pow_ne_zero _ (hp i).ne_zero)
      have hds := hDS ι Q θ
      change θ (FGModuleCat.of ℤ (M : Type)) =
        integerEulerParameter θ * (n : ℤ)
      calc
        θ (FGModuleCat.of ℤ (M : Type)) =
            θ (FGModuleCat.of ℤ ((Fin n →₀ ℤ) × DirectSum ι Q)) :=
          hIso θ eM
        _ = θ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) +
            θ (FGModuleCat.of ℤ (DirectSum ι Q)) := hprod θ
        _ = integerEulerParameter θ * (n : ℤ) := by
          rw [hfree θ n, hds, hsum, add_zero]
    refine ⟨n, hvalue φ, hvalue ψ⟩
  have hdim_shortExact : ∀ (S : ShortComplex (FGModuleCat ℤ)),
      S.ShortExact →
        Module.finrank ℤ (S.X₂ : Type) =
          Module.finrank ℤ (S.X₁ : Type) + Module.finrank ℤ (S.X₃ : Type) := by
    intro S hS
    let S' := S.map F
    have hExact : S'.Exact :=
      (ShortComplex.exact_map_iff_of_faithful S F).2 hS.exact
    letI : Mono S.f := hS.mono_f
    letI : Epi S.g := hS.epi_g
    letI : CategoryTheory.Limits.PreservesLimitsOfShape
        CategoryTheory.Limits.WalkingCospan F := by infer_instance
    letI : CategoryTheory.Limits.PreservesColimitsOfShape
        CategoryTheory.Limits.WalkingSpan F := by infer_instance
    let f : (S.X₁ : Type) →ₗ[ℤ] (S.X₂ : Type) := S.f.hom.hom
    let g : (S.X₂ : Type) →ₗ[ℤ] (S.X₃ : Type) := S.g.hom.hom
    letI : Module ℤ ((S.X₂ : Type) ⧸ g.ker) := Submodule.Quotient.module g.ker
    letI : Module ℤ g.range := g.range.module
    letI : Module ℤ g.ker := g.ker.module
    letI : Module ℤ f.range := f.range.module
    have hf : Function.Injective f := by
      change Function.Injective (F.map S.f).hom
      apply (ModuleCat.mono_iff_injective _).1
      exact F.map_mono S.f
    have hg : Function.Surjective g := by
      change Function.Surjective (F.map S.g).hom
      apply (ModuleCat.epi_iff_surjective _).1
      exact F.map_epi S.g
    have hfun : Function.Exact f g := by
      change Function.Exact (F.map S.f).hom (F.map S.g).hom
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S').1 hExact
    have hrange : LinearMap.range f = LinearMap.ker g := hfun.linearMap_ker_eq.symm
    have hdim := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
    rw [g.quotKerEquivRange.finrank_eq] at hdim
    have hker : Module.finrank ℤ (LinearMap.ker g) =
        Module.finrank ℤ (LinearMap.range f) := by
      exact (LinearEquiv.ofEq (LinearMap.range f) (LinearMap.ker g) hrange).finrank_eq.symm
    have hrangef_nat :
        @Module.finrank ℤ (LinearMap.range f) Int.instSemiring
            (LinearMap.range f).addCommMonoid f.range.module =
          Module.finrank ℤ (S.X₁ : Type) := LinearMap.finrank_range_of_inj hf
    have hrangeg : Module.finrank ℤ (LinearMap.range g) =
        Module.finrank ℤ (S.X₃ : Type) := by
      exact (LinearEquiv.ofTop (LinearMap.range g)
        (LinearMap.range_eq_top.mpr hg)).finrank_eq
    change Module.finrank ℤ (S.X₂ : Type) =
      Module.finrank ℤ (S.X₁ : Type) + Module.finrank ℤ (S.X₃ : Type)
    calc
      Module.finrank ℤ (S.X₂ : Type) =
          Module.finrank ℤ (LinearMap.range g) +
            Module.finrank ℤ (LinearMap.ker g) := hdim.symm
      _ = Module.finrank ℤ (S.X₃ : Type) +
          Module.finrank ℤ (LinearMap.range f) := by
        rw [hrangeg, hker]
      _ = Module.finrank ℤ (S.X₁ : Type) +
          Module.finrank ℤ (S.X₃ : Type) := by rw [hrangef_nat]; ac_rfl
  constructor
  · intro φ ψ h
    cases φ with
    | mk φ hφ =>
      cases ψ with
      | mk ψ hψ =>
        have hparam : φ (FGModuleCat.of ℤ ℤ) = ψ (FGModuleCat.of ℤ ℤ) := by
          simpa [integerEulerParameter] using h
        have hfun : φ = ψ := by
          funext M
          obtain ⟨n, hφM, hψM⟩ :=
            hclass (⟨φ, hφ⟩ : EulerPoincareFunction ℤ)
              (⟨ψ, hψ⟩ : EulerPoincareFunction ℤ) M
          calc
            φ M = φ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by
              simpa [integerEulerParameter] using hφM
            _ = ψ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by rw [hparam]
            _ = ψ M := by
              simpa [integerEulerParameter] using hψM.symm
        cases hfun
        rfl
  · intro z
    let φz : EulerPoincareFunction ℤ :=
      { toFun := fun M => z * (Module.finrank ℤ (M : Type) : ℤ)
        map_shortExact' := by
          intro S hS
          have hdim := hdim_shortExact S hS
          change z * (Module.finrank ℤ (S.X₂ : Type) : ℤ) =
            z * (Module.finrank ℤ (S.X₁ : Type) : ℤ) +
              z * (Module.finrank ℤ (S.X₃ : Type) : ℤ)
          rw [hdim, Nat.cast_add, mul_add] }
    refine ⟨φz, ?_⟩
    simp [φz, integerEulerParameter]

/-! ## Exercise 3: the node `k[x,y]/(xy)` -/

/-- The homogeneous relation defining the nodal affine curve. -/
def nodePolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The nodal ring `k[x,y]/(xy)`. -/
abbrev nodeRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ nodePolynomialIdeal k

/-- The two component ideals in the nodal ring. -/
def nodeXIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 0)}

def nodeYIdeal (k : Type u) [Field k] : Ideal (nodeRing k) :=
  Ideal.span {Ideal.Quotient.mk (nodePolynomialIdeal k) (MvPolynomial.X 1)}

/-- The two cyclic modules supported on the irreducible components of the node. -/
abbrev nodeXComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeXIdeal k

abbrev nodeYComponent (k : Type u) [Field k] : Type u :=
  nodeRing k ⧸ nodeYIdeal k

/-- The two component values of an Euler–Poincaré function on the nodal ring. -/
def nodeEulerParameters (k : Type u) [Field k]
    (φ : EulerPoincareFunction (nodeRing k)) : ℤ × ℤ :=
  (φ (FGModuleCat.of (nodeRing k) (nodeXComponent k)),
    φ (FGModuleCat.of (nodeRing k) (nodeYComponent k)))

/-- For an algebraically closed field, the two component values classify all
Euler–Poincaré functions on the nodal ring. -/
theorem eulerPoincareFunction_node_classification
    (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Bijective (nodeEulerParameters (k := k)) := by
  sorry

/-! ## Exercise 4: kernels of locally finite graded maps -/

/-- The kernel of a degree-preserving map between locally finite graded modules
admits the induced grading and remains locally finite. -/
theorem kernel_of_graded_map_is_locally_finite
    {A M N : Type u} {ι : Type v}
    [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [DecidableEq ι]
    (G : GradedModuleData A M ι) (H : GradedModuleData A N ι)
    (hG : G.LocallyFinite) (hH : H.LocallyFinite)
    (f : GradedLinearMap G H) :
    ∃ K : GradedModuleData A (LinearMap.ker f.toLinearMap) ι,
      (∀ n : ι, K.component n = f.kernelComponent n) ∧ K.LocallyFinite := by
  classical
  let p : Submodule A M := LinearMap.ker f.toLinearMap
  letI : DirectSum.Decomposition (fun n => G.component n) := G.decomposition
  letI : DirectSum.Decomposition (fun n => H.component n) := H.decomposition
  have hmap_component : ∀ (x : M) (n : ι),
      f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) =
        (DirectSum.decompose (fun n => H.component n)
          (f.toLinearMap x) n : N) := by
    intro x
    refine DirectSum.Decomposition.inductionOn
      (ℳ := fun n => G.component n)
      (motive := fun x => ∀ n : ι,
        f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) =
          (DirectSum.decompose (fun n => H.component n)
            (f.toLinearMap x) n : N)) ?_ ?_ ?_ x
    · intro n
      simp
    · intro i m n
      have hm : (m : M) ∈ G.component i := m.property
      have hfm : f.toLinearMap (m : M) ∈ H.component i :=
        f.map_component' i hm
      by_cases hin : i = n
      · subst n
        rw [DirectSum.decompose_of_mem_same _ hm,
          DirectSum.decompose_of_mem_same _ hfm]
      · rw [DirectSum.decompose_of_mem_ne _ hm hin,
          DirectSum.decompose_of_mem_ne _ hfm hin]
        simp
    · intro x y hx hy n
      have hGadd :
          (DirectSum.decompose (fun n => G.component n) (x + y) n : M) =
            (DirectSum.decompose (fun n => G.component n) x n : M) +
              (DirectSum.decompose (fun n => G.component n) y n : M) := by
        simpa using congrArg (fun z : (⨁ n, G.component n) => (z n : M))
          (DirectSum.decompose_add (fun n => G.component n) x y)
      have hHadd :
          (DirectSum.decompose (fun n => H.component n)
            (f.toLinearMap x + f.toLinearMap y) n : N) =
            (DirectSum.decompose (fun n => H.component n) (f.toLinearMap x) n : N) +
              (DirectSum.decompose (fun n => H.component n) (f.toLinearMap y) n : N) := by
        simpa using congrArg (fun z : (⨁ n, H.component n) => (z n : N))
          (DirectSum.decompose_add (fun n => H.component n)
            (f.toLinearMap x) (f.toLinearMap y))
      calc
        f.toLinearMap
            (DirectSum.decompose (fun n => G.component n) (x + y) n : M) =
            f.toLinearMap
              ((DirectSum.decompose (fun n => G.component n) x n : M) +
                (DirectSum.decompose (fun n => G.component n) y n : M)) := by
          rw [hGadd]
        _ = f.toLinearMap (DirectSum.decompose (fun n => G.component n) x n : M) +
            f.toLinearMap (DirectSum.decompose (fun n => G.component n) y n : M) :=
          map_add _ _ _
        _ = (DirectSum.decompose (fun n => H.component n) (f.toLinearMap x) n : N) +
            (DirectSum.decompose (fun n => H.component n) (f.toLinearMap y) n : N) := by
          rw [hx n, hy n]
        _ = (DirectSum.decompose (fun n => H.component n)
              (f.toLinearMap x + f.toLinearMap y) n : N) := hHadd.symm
        _ = (DirectSum.decompose (fun n => H.component n)
              (f.toLinearMap (x + y)) n : N) := by rw [f.toLinearMap.map_add]
  have hcomponent : ∀ (x : M), x ∈ p → ∀ n : ι,
      (DirectSum.decompose (fun n => G.component n) x n : M) ∈ p := by
    intro x hx n
    change f.toLinearMap x = 0 at hx
    change f.toLinearMap
      (DirectSum.decompose (fun n => G.component n) x n : M) = 0
    simpa [hx] using hmap_component x n
  let Kc : ι → Submodule A p := fun n => f.kernelComponent n
  let e : Submodule A p ≃o Set.Iic p := p.mapIic
  have hmapK (n : ι) :
      (e (Kc n) : Submodule A M) = G.component n ⊓ p := by
    change ((G.component n).comap p.subtype).map p.subtype = _
    rw [Submodule.map_comap_subtype]
    exact inf_comm _ _
  have hKInd : iSupIndep Kc := by
    have hGInd : iSupIndep (fun n => G.component n) :=
      G.decomposition.isInternal.submodule_iSupIndep
    have hInfInd : iSupIndep (fun n => G.component n ⊓ p) :=
      hGInd.mono (fun n => inf_le_left)
    have he : (e ∘ Kc) =
        (fun n => ⟨G.component n ⊓ p,
          (inf_le_right : G.component n ⊓ p ≤ p)⟩ : ι → Set.Iic p) := by
      funext n
      apply Subtype.ext
      exact hmapK n
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact iSupIndep.of_coe_Iic_comp hInfInd
  have hKTop : iSup Kc = ⊤ := by
    apply top_unique
    intro x _
    have hsum :
        (∑ n ∈ (DirectSum.decompose (fun n => G.component n) (x : M)).support,
          (⟨(DirectSum.decompose (fun n => G.component n) (x : M) n : M),
            hcomponent (x : M) x.property n⟩ : p)) = x := by
      apply Subtype.ext
      change p.subtype
          (∑ n ∈ (DirectSum.decompose (fun n => G.component n) (x : M)).support,
            (⟨(DirectSum.decompose (fun n => G.component n) (x : M) n : M),
              hcomponent (x : M) x.property n⟩ : p)) = (x : M)
      rw [map_sum]
      exact DirectSum.sum_support_decompose (fun n => G.component n) (x : M)
    rw [← hsum]
    exact sum_mem fun n hn =>
      (le_iSup (fun n => Kc n) n) (by
        change (DirectSum.decompose (fun n => G.component n) (x : M) n : M) ∈
          G.component n
        exact (DirectSum.decompose (fun n => G.component n) (x : M) n).property)
  have hK : DirectSum.IsInternal Kc :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hKInd hKTop
  let K : GradedModuleData A p ι :=
    { component := Kc
      decomposition := DirectSum.IsInternal.chooseDecomposition Kc hK }
  refine ⟨K, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    letI : Module.Finite A (G.component n) := hG n
    let q : Kc n →ₗ[A] G.component n :=
      { toFun := fun x => ⟨(x : p).1, x.2⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    apply Module.Finite.of_injective q
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa [q] using congrArg Subtype.val hxy

/-! ## Exercise 5: a weighted polynomial ring -/

/-- The weights `2` and `3` on the two polynomial variables. -/
def twoThreeWeights : Fin 2 → ℕ := fun i => if i = 0 then 2 else 3

/-- The canonical weighted decomposition of `k[x,y]` with weights `2` and `3`. -/
def weightedPolynomialGradedModule (k : Type u) [Field k] :
    GradedModuleData k (MvPolynomial (Fin 2) k) ℕ :=
  { component := MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights
    decomposition := MvPolynomial.weightedDecomposition k twoThreeWeights }

/-- The vector-space dimension of a homogeneous component. -/
def fieldDimensionHilbertFunction
    {k M : Type u} {ι : Type v} [Field k]
    [AddCommGroup M] [Module k M] [DecidableEq ι]
    (G : GradedModuleData k M ι) (n : ι) : ℕ :=
  Module.finrank k (G.component n)

def weightedPolynomialHilbertFunction (k : Type u) [Field k] (n : ℕ) : ℕ :=
  fieldDimensionHilbertFunction (weightedPolynomialGradedModule k) n

/-- The number of solutions of `2a + 3b = n`. -/
def weightedTwoThreeFormula (n : ℕ) : ℕ :=
  if n % 6 = 1 then n / 6 else n / 6 + 1

theorem weighted_polynomial_grading_locally_finite (k : Type u) [Field k] :
    (weightedPolynomialGradedModule k).LocallyFinite := by
  exact fun n => Module.Finite.of_fg
    (MvPolynomial.weightedHomogeneousSubmodule_fg k twoThreeWeights
      (by intro x; fin_cases x <;> simp [twoThreeWeights]) n)

/-- The weighted polynomial Hilbert function is the solution-counting formula. -/
theorem weighted_polynomial_hilbert_function (k : Type u) [Field k] (n : ℕ) :
    weightedPolynomialHilbertFunction k n = weightedTwoThreeFormula n := by
  classical
  change Module.finrank k
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
    weightedTwoThreeFormula n
  let S : Set (Fin 2 →₀ ℕ) := {d | Finsupp.weight twoThreeWeights d = n}
  haveI : Finite S :=
    (Finsupp.finite_of_nat_weight_eq twoThreeWeights
      (by intro x; fin_cases x <;> simp [twoThreeWeights]) n).to_subtype
  letI := Fintype.ofFinite S
  have hsub :
      MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n =
        MvPolynomial.restrictSupport k S := by
    rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    rfl
  have hdim : Module.finrank k
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
      Module.finrank k (MvPolynomial.restrictSupport k S) :=
    congrArg (fun T : Submodule k (MvPolynomial (Fin 2) k) => Module.finrank k T) hsub
  let e : (Fin 2 →₀ ℕ) ≃ (ℕ × ℕ) :=
    Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)
  let T : Set (ℕ × ℕ) := {p | 2 * p.1 + 3 * p.2 = n}
  have he : ∀ d, d ∈ S ↔ e d ∈ T := by
    intro d
    simp [S, T, e, Finsupp.weight_eq_sum, twoThreeWeights, finTwoArrowEquiv]
    omega
  let eT : S ≃ T := e.subtypeEquiv he
  letI : Fintype T := Fintype.ofEquiv S eT
  have hcardST : Fintype.card S = Fintype.card T := Fintype.card_congr eT
  calc
    Module.finrank k
        (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) =
        Module.finrank k (MvPolynomial.restrictSupport k S) := hdim
    _ = Fintype.card S :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k S)
    _ = Fintype.card T := hcardST
    _ = weightedTwoThreeFormula n := by
      let L := weightedTwoThreeFormula n
      have hcount : Fintype.card T = L := by
        let eFin : T ≃ Fin L :=
          { toFun := fun x =>
              ⟨x.1.2 / 2, by
                have hx := x.2
                dsimp [T] at hx
                by_cases hs : n % 6 = 1
                · have hL : L = n / 6 := by simp [L, weightedTwoThreeFormula, hs]
                  rw [hL]
                  omega
                · have hL : L = n / 6 + 1 := by simp [L, weightedTwoThreeFormula, hs]
                  rw [hL]
                  omega⟩
            invFun := fun j =>
              ⟨( (n - 3 * (2 * (j : ℕ) + n % 2)) / 2,
                  2 * (j : ℕ) + n % 2), by
                dsimp [T]
                have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                by_cases hs : n % 6 = 1
                · have hL : L = n / 6 := by simp [L, weightedTwoThreeFormula, hs]
                  have hj : (j : ℕ) < n / 6 := by simpa [hL] using j.isLt
                  omega
                · have hL : L = n / 6 + 1 := by simp [L, weightedTwoThreeFormula, hs]
                  have hj : (j : ℕ) < n / 6 + 1 := by simpa [hL] using j.isLt
                  omega⟩
            left_inv := by
              intro x
              have hx := x.2
              dsimp [T] at hx
              apply Subtype.ext
              apply Prod.ext
              · have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                change (n - 3 * (2 * (x.1.2 / 2) + n % 2)) / 2 = x.1.1
                omega
              · have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
                change 2 * (x.1.2 / 2) + n % 2 = x.1.2
                omega
            right_inv := by
              intro j
              apply Fin.ext
              have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
              change (2 * (j : ℕ) + n % 2) / 2 = j
              omega }
        simpa using Fintype.card_congr eFin
      simpa [L] using hcount

/-- The periodic weighted Hilbert function does not eventually agree with a
numerical polynomial. -/
theorem weighted_polynomial_no_hilbert_polynomial (k : Type u) [Field k] :
    ¬ HasHilbertPolynomialOnNat (weightedPolynomialHilbertFunction k) := by
  rintro ⟨P, _hP, hEq⟩
  rcases Filter.eventually_atTop.1 hEq with ⟨N, hN⟩
  let L : Polynomial ℚ := Polynomial.C (1 / 6) * Polynomial.X + Polynomial.C 1
  let f : ℕ → ℚ := fun m => (6 * (m + N) : ℕ)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have hab' : 6 * (a + N) = 6 * (b + N) := by exact_mod_cast hab
    omega
  have hmem : ∀ m : ℕ, P.eval (f m) = L.eval (f m) := by
    intro m
    have hm := hN (6 * (m + N)) (by omega)
    rw [weighted_polynomial_hilbert_function] at hm
    have hlin :
        (weightedTwoThreeFormula (6 * (m + N)) : ℚ) =
          L.eval (f m) := by
      simp [weightedTwoThreeFormula, L, f, Polynomial.eval_add,
        Polynomial.eval_mul]
    exact hm.symm.trans hlin
  have hInf : {x : ℚ | P.eval x = L.eval x}.Infinite := by
    apply Set.infinite_of_injective_forall_mem hf
    intro m
    exact hmem m
  have hP : P = L := Polynomial.eq_of_infinite_eval_eq P L hInf
  have hm := hN (6 * N + 1) (by omega)
  rw [weighted_polynomial_hilbert_function, hP] at hm
  have hmod : (6 * N + 1) % 6 = 1 := by omega
  simp [weightedTwoThreeFormula, hmod] at hm
  have hdiv : (6 * N + 1) / 6 = N := by omega
  rw [hdiv] at hm
  norm_num [L, Polynomial.eval_add, Polynomial.eval_mul] at hm
  linarith

private theorem graded_quotient_data
    {A M N P : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [SetLike P M] [AddSubmonoidClass P M]
    (G : GradedModuleData A M ℕ)
    [hdec : DirectSum.Decomposition (fun n : ℕ => G.component n)]
    (p : P) (q : M →ₗ[A] N)
    (hq : ∀ x : M, q x = 0 ↔ x ∈ p) (hsurj : Function.Surjective q)
    (hp : DirectSum.SetLike.IsHomogeneous (fun n : ℕ => G.component n) p) :
    ∃ Gq : GradedModuleData A N ℕ,
      ∀ n : ℕ, Gq.component n = (G.component n).map q := by
  classical
  let C : ℕ → Submodule A M := fun n => G.component n
  let Q : ℕ → Submodule A N := fun n => (C n).map q
  letI : DirectSum.Decomposition C := hdec
  let r : ∀ n : ℕ, C n →ₗ[A] Q n := fun n =>
    { toFun := fun x => ⟨q x, ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact q.map_add (x : M) (y : M)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact q.map_smul a (x : M) }
  have hr : ∀ n : ℕ, Function.Surjective (r n) := by
    intro n y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let L : DirectSum ℕ (fun n => C n) →ₗ[A] DirectSum ℕ (fun n => Q n) :=
    DirectSum.lmap r
  have hLsurj : Function.Surjective L :=
    (DirectSum.lmap_surjective r).2 hr
  let e : M ≃ₗ[A] DirectSum ℕ (fun n => C n) :=
    DirectSum.decomposeLinearEquiv C
  let d : M →ₗ[A] DirectSum ℕ (fun n => Q n) := L.comp e.toLinearMap
  let coe : DirectSum ℕ (fun n => Q n) →ₗ[A] N :=
    DirectSum.coeLinearMap Q
  have hcoe_d : coe.comp d = q := by
    apply DirectSum.decompose_lhom_ext C
    intro n
    ext x
    simp [coe, d, L, e, r, C]
  have hcoe_surj : Function.Surjective coe := by
    intro y
    rcases hsurj y with ⟨x, hx⟩
    refine ⟨d x, ?_⟩
    simpa [LinearMap.comp_apply] using
      (DFunLike.congr_fun hcoe_d x).trans hx
  have hcoe_inj : Function.Injective coe := by
    intro z z' hzz'
    have hzero : coe (z - z') = 0 := by
      rw [map_sub, hzz', sub_self]
    rcases hLsurj (z - z') with ⟨y, hy⟩
    let x : M := e.symm y
    have hqx : q x = 0 := by
      rw [← DFunLike.congr_fun hcoe_d x]
      change coe (L (e x)) = 0
      rw [show e x = y by simp [x], hy, hzero]
    have hpx : x ∈ p := (hq x).mp hqx
    have hdx : d x = 0 := by
      apply DirectSum.ext
      intro n
      apply Subtype.ext
      change q (e x n : M) = 0
      apply (hq _).mpr
      change (DirectSum.decompose C x n : M) ∈ p
      exact hp n hpx
    have hLy : L y = 0 := by
      simpa [d, x] using hdx
    have hdiff : z - z' = 0 := by
      rw [← hy, hLy]
    exact sub_eq_zero.mp hdiff
  let eQ : DirectSum ℕ (fun n => Q n) ≃ₗ[A] N := LinearEquiv.ofBijective coe
    ⟨hcoe_inj, hcoe_surj⟩
  have hleft : coe.comp eQ.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro y
    change eQ (eQ.symm y) = y
    exact eQ.apply_symm_apply y
  have hright : eQ.symm.toLinearMap.comp coe = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change eQ.symm (coe z) = z
    exact eQ.symm_apply_apply z
  let dec : DirectSum.Decomposition Q :=
    DirectSum.Decomposition.ofLinearMap Q eQ.symm.toLinearMap hleft hright
  let Gq : GradedModuleData A N ℕ :=
    { component := Q
      decomposition := dec }
  refine ⟨Gq, ?_⟩
  intro n
  rfl

/-! ## Exercise 6: a weighted quotient -/

/-- The homogeneous ideal `(x², xy)` in the weighted polynomial ring. -/
def truncatedPolynomialIdeal (k : Type u) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The quotient `k[x,y]/(x²,xy)` with `deg x = 2` and `deg y = 3`. -/
abbrev truncatedPolynomialRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ truncatedPolynomialIdeal k

/-- The computed Hilbert function of the weighted quotient. -/
def truncatedPolynomialHilbertFunction (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n) then 1 else 0

/-- The quotient has the grading induced from the weighted homogeneous pieces,
and its Hilbert function is the displayed formula. -/
theorem truncated_polynomial_graded_quotient_exists (k : Type u) [Field k] :
    ∃ G : GradedModuleData k (truncatedPolynomialRing k) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n).map
              (Ideal.Quotient.mkₐ k (truncatedPolynomialIdeal k)).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = truncatedPolynomialHilbertFunction n := by
  classical
  letI : GradedAlgebra
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights) :=
    MvPolynomial.weightedGradedAlgebra k twoThreeWeights
  have hI : (truncatedPolynomialIdeal k).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl | rfl
    · refine ⟨4, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.pow
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 0) 2)
    · refine ⟨5, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.mul
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 0)
          (MvPolynomial.isWeightedHomogeneous_X (R := k) twoThreeWeights 1))
  let q : MvPolynomial (Fin 2) k →ₗ[k] truncatedPolynomialRing k :=
    (Ideal.Quotient.mkₐ k (truncatedPolynomialIdeal k)).toLinearMap
  have hq : ∀ p : MvPolynomial (Fin 2) k,
      q p = 0 ↔ p ∈ truncatedPolynomialIdeal k := by
    intro p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqsurj : Function.Surjective q := by
    exact Ideal.Quotient.mkₐ_surjective k (truncatedPolynomialIdeal k)
  letI : DirectSum.Decomposition
      (fun n : ℕ => (weightedPolynomialGradedModule k).component n) :=
    (weightedPolynomialGradedModule k).decomposition
  rcases graded_quotient_data (weightedPolynomialGradedModule k)
      (truncatedPolynomialIdeal k) q hq hqsurj hI with ⟨G, hG⟩
  have hfinite : ∀ n : ℕ, Module.Finite k (G.component n) := by
    intro n
    letI : Module.Finite k
        (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) :=
      weighted_polynomial_grading_locally_finite k n
    rw [hG n]
    exact Module.Finite.map
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) q
  let s : Set (Fin 2 →₀ ℕ) :=
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1}
  have hIeq : truncatedPolynomialIdeal k =
      Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' s) := by
    have hsingle : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) + Finsupp.single 0 1 =
        Finsupp.single 0 2 := by
      ext i
      fin_cases i <;> simp
    have himage :
        (fun d : Fin 2 →₀ ℕ => MvPolynomial.monomial d (1 : k)) '' s =
          {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1} := by
      ext z
      constructor
      · rintro ⟨d, hd, rfl⟩
        simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        rcases hd with rfl | rfl
        · left
          simp [MvPolynomial.X, pow_two, hsingle]
        · right
          simp [MvPolynomial.X]
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz
        · refine ⟨Finsupp.single 0 2, by simp [s], ?_⟩
          simpa [MvPolynomial.X, pow_two, hsingle] using hz.symm
        · refine ⟨Finsupp.single 0 1 + Finsupp.single 1 1, by simp [s], ?_⟩
          simpa [MvPolynomial.X] using hz.symm
    ext p
    rw [truncatedPolynomialIdeal, himage]
  have hgen : ∀ {n : ℕ} {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = n →
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) →
        ∃ si ∈ s, si ≤ d := by
    intro n d hn hbad
    by_cases h20 : 2 ≤ d 0
    · refine ⟨Finsupp.single 0 2, by simp [s], ?_⟩
      intro i
      fin_cases i <;> simp <;> omega
    by_cases h11 : 1 ≤ d 1
    · refine ⟨Finsupp.single 0 1 + Finsupp.single 1 1, by simp [s], ?_⟩
      intro i
      fin_cases i <;> simp <;> omega
    have hd0 : d 0 = 0 ∨ d 0 = 1 := by omega
    rcases hd0 with hd0 | hd0
    · have hn' : n = 3 * d 1 := by omega
      by_cases hd1 : d 1 = 0
      · exfalso
        apply hbad
        omega
      · exfalso
        apply hbad
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · omega
        · exact ⟨d 1, by omega⟩
    · have hd1 : d 1 = 0 := by omega
      exfalso
      apply hbad
      omega
  have hmem_bad : ∀ {n : ℕ} {p : MvPolynomial (Fin 2) k},
      p ∈ MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n →
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) →
        p ∈ truncatedPolynomialIdeal k := by
    intro n p hp hbad
    rw [hIeq]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro d hd
    have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
    have hweight' : 2 * d 0 + 3 * d 1 = n := by
      simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
    exact hgen hweight' hbad
  have hnotgen0 : ¬ ∃ si ∈ s, si ≤ (0 : Fin 2 →₀ ℕ) := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl <;>
      have := hle 0 <;> simp at this
  have hnotgen2 : ¬ ∃ si ∈ s, si ≤ Finsupp.single 0 1 := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl
    · have := hle 0
      simp at this
    · have := hle 1
      simp at this
  have hnotgenc (c : ℕ) :
      ¬ ∃ si ∈ s, si ≤ Finsupp.single 1 c := by
    rintro ⟨si, hsi, hle⟩
    simp [s] at hsi
    rcases hsi with rfl | rfl
    · have := hle 0
      simp at this
    · have := hle 0
      simp at this
  have hmonoI : ∀ {d : Fin 2 →₀ ℕ} {r : k},
      (∃ si ∈ s, si ≤ d) →
        MvPolynomial.monomial d r ∈ truncatedPolynomialIdeal k := by
    intro d r hgen'
    rw [hIeq]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro di hdi
    have hdi'' : d = di ∧ r ≠ 0 := by
      simpa [MvPolynomial.coeff_monomial] using
        (MvPolynomial.mem_support_iff.mp hdi)
    have hdi' : d = di := hdi''.1
    subst di
    exact hgen'
  have hclass0 : ∀ {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 0 → d = 0 := by
    intro d hd
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp at hd ⊢ <;> omega
  have hclass2 : ∀ {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 2 → d = Finsupp.single 0 1 := by
    intro d hd
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp at hd ⊢ <;> omega
  have hclassc : ∀ {c : ℕ} {d : Fin 2 →₀ ℕ},
      2 * d 0 + 3 * d 1 = 3 * c →
        d = Finsupp.single 1 c ∨ ∃ si ∈ s, si ≤ d := by
    intro c d hd
    by_cases h0 : d 0 = 0
    · left
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [h0] at hd ⊢ <;> omega
    · right
      by_cases h20 : 2 ≤ d 0
      · refine ⟨Finsupp.single 0 2, ?_, ?_⟩
        · simp [s]
        · intro i
          fin_cases i <;> simp <;> omega
      · have hone : d 0 = 1 := by omega
        exfalso
        omega
  have hqmonomial : ∀ (d : Fin 2 →₀ ℕ) (r : k),
      q (MvPolynomial.monomial d r) =
        r • q (MvPolynomial.monomial d (1 : k)) := by
    intro d r
    have hmon :
        MvPolynomial.monomial d r =
          r • MvPolynomial.monomial d (1 : k) := by
      rw [← MvPolynomial.C_mul', MvPolynomial.C_mul_monomial, mul_one]
    calc
      q (MvPolynomial.monomial d r) =
          q (r • MvPolynomial.monomial d (1 : k)) := congrArg q hmon
      _ = r • q (MvPolynomial.monomial d (1 : k)) := q.map_smul r _
  have hmap0 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).map
          q =
        k ∙ q
          (MvPolynomial.monomial 0 (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change q p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 0 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      have hdeq := hclass0 hweight'
      rw [hdeq, hqmonomial 0 (MvPolynomial.coeff 0 p)]
      exact Submodule.smul_mem
        (k ∙ q (MvPolynomial.monomial 0 (1 : k)))
        _ (Submodule.mem_span_singleton_self _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial 0 (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_one k twoThreeWeights
      · exact q.map_smul a _
  have hmap2 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).map
          q =
        k ∙ q
          (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change q p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 2 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      have hdeq := hclass2 hweight'
      rw [hdeq,
        hqmonomial (Finsupp.single 0 1)
          (MvPolynomial.coeff (Finsupp.single 0 1) p)]
      exact Submodule.smul_mem
        (k ∙ q (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)))
        _ (Submodule.mem_span_singleton_self _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 0 1) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial (R := k)
          twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights])
      · exact q.map_smul a _
  have hmapc (c : ℕ) :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).map
          q =
        k ∙ q
          (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change q p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 3 * c := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm] using hweight
      rcases hclassc hweight' with rfl | ⟨si, hsi, hle⟩
      · rw [hqmonomial (Finsupp.single 1 c)
          (MvPolynomial.coeff (Finsupp.single 1 c) p)]
        exact Submodule.smul_mem
          (k ∙ q (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)))
          _ (Submodule.mem_span_singleton_self _)
      · have hi := hmonoI (r := MvPolynomial.coeff d p) ⟨si, hsi, hle⟩
        rw [(hq _).2 hi]
        exact Submodule.zero_mem _
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply (Submodule.mem_map).2
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 1 c) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial (R := k)
          twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights, Nat.mul_comm])
      · exact q.map_smul a _
  refine ⟨G, hfinite, ?_, ?_⟩
  · intro n
    rw [hG n]
    rfl
  · have hq0_ne : q (MvPolynomial.monomial 0 (1 : k)) ≠ 0 := by
      intro hz
      have hpI : MvPolynomial.monomial 0 (1 : k) ∈ truncatedPolynomialIdeal k :=
        (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (0 : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial 0 (1 : k)).support := by
        simp
      exact hnotgen0
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI) 0 hsupp)
    have hq2_ne :
        q (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)) ≠ 0 := by
      intro hz
      have hpI :
          MvPolynomial.monomial (Finsupp.single 0 1) (1 : k) ∈
            truncatedPolynomialIdeal k := (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)).support := by
        simp
      exact hnotgen2
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI)
          (Finsupp.single 0 1) hsupp)
    have hqc_ne (c : ℕ) :
        q (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)) ≠ 0 := by
      intro hz
      have hpI :
          MvPolynomial.monomial (Finsupp.single 1 c) (1 : k) ∈
            truncatedPolynomialIdeal k := (hq _).mp hz
      rw [hIeq] at hpI
      have hsupp : (Finsupp.single 1 c : Fin 2 →₀ ℕ) ∈
          (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)).support := by
        simp
      exact hnotgenc c
        ((MvPolynomial.mem_ideal_span_monomial_image.mp hpI)
          (Finsupp.single 1 c) hsupp)
    have hbad_component : ∀ n : ℕ,
        ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) → G.component n = ⊥ := by
      intro n hn
      rw [hG n]
      apply le_antisymm
      · rintro y ⟨p, hp, rfl⟩
        have hpI := hmem_bad hp hn
        have hpzero : q p = 0 := (hq p).2 hpI
        change q p = 0
        exact hpzero
      · exact bot_le
    have hdim0 : Module.finrank k (G.component 0) = 1 := by
      rw [hG 0]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0)) = 1
      rw [hmap0]
      exact finrank_span_singleton hq0_ne
    have hdim2 : Module.finrank k (G.component 2) = 1 := by
      rw [hG 2]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2)) = 1
      rw [hmap2]
      exact finrank_span_singleton hq2_ne
    have hdimc (c : ℕ) :
        Module.finrank k (G.component (3 * c)) = 1 := by
      rw [hG (3 * c)]
      change Module.finrank k
        (Submodule.map q
          (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c))) = 1
      rw [hmapc c]
      exact finrank_span_singleton (hqc_ne c)
    intro n
    change Module.finrank k (G.component n) =
      if n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n) then 1 else 0
    by_cases hn0 : n = 0
    · subst n
      simpa using hdim0
    by_cases hn2 : n = 2
    · subst n
      simpa using hdim2
    by_cases hdiv : 0 < n ∧ 3 ∣ n
    · rcases hdiv.2 with ⟨c, rfl⟩
      simpa [hdiv, hn0, hn2] using hdimc c
    · letI : Module.Finite k (G.component n) := hfinite n
      have hbad : ¬(n = 0 ∨ n = 2 ∨ (0 < n ∧ 3 ∣ n)) := by
        intro h
        rcases h with h | h | h
        · exact hn0 h
        · exact hn2 h
        · exact hdiv h
      have hzero : Module.finrank k (G.component n) = 0 :=
        (Submodule.finrank_eq_zero).2 (hbad_component n hbad)
      simpa [hn0, hn2, hdiv] using hzero

theorem truncated_polynomial_no_hilbert_polynomial :
    ¬ HasHilbertPolynomialOnNat truncatedPolynomialHilbertFunction := by
  rintro ⟨P, _hP, hEq⟩
  rcases Filter.eventually_atTop.1 hEq with ⟨N, hN⟩
  let f : ℕ → ℚ := fun m => (6 * (m + N) + 1 : ℕ)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have hab' : 6 * (a + N) + 1 = 6 * (b + N) + 1 := by
      exact_mod_cast hab
    omega
  have hzero : ∀ m : ℕ, P.eval (f m) = 0 := by
    intro m
    have hm : N ≤ 6 * (m + N) + 1 := by omega
    have hm' := hN (6 * (m + N) + 1) hm
    have hval : truncatedPolynomialHilbertFunction (6 * (m + N) + 1) = 0 := by
      simp [truncatedPolynomialHilbertFunction]
      omega
    rw [hval] at hm'
    simpa [f] using hm'.symm
  have hInf : {x : ℚ | P.eval x = 0}.Infinite := by
    apply Set.infinite_of_injective_forall_mem hf
    intro m
    exact hzero m
  have hPzero : P = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq P 0
    simpa using hInf
  have hm := hN (6 * N + 3) (by omega)
  rw [hPzero] at hm
  have hval : truncatedPolynomialHilbertFunction (6 * N + 3) = 1 := by
    simp [truncatedPolynomialHilbertFunction]
    omega
  rw [hval] at hm
  simp at hm

/-! ## Exercise 7: a degree-`d` plane hypersurface -/

/-- The homogeneous equation defining the degree-`d` hypersurface. -/
def hypersurfacePolynomial (k : Type u) [Field k] (d : ℕ) :
    MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d + MvPolynomial.X 2 ^ d

/-- The homogeneous coordinate ring of the degree-`d` hypersurface. -/
abbrev hypersurfaceRing (k : Type u) [Field k] (d : ℕ) : Type u :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {hypersurfacePolynomial k d}

/-- The degree-`n` Hilbert-function formula for the hypersurface quotient. -/
def hypersurfaceHilbertFunction (d n : ℕ) : ℕ :=
  Nat.choose (n + 2) 2 - if d ≤ n then Nat.choose (n - d + 2) 2 else 0

/-- The eventual Hilbert polynomial of a plane degree-`d` hypersurface. -/
def hypersurfaceHilbertPolynomial (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (d : ℚ) * Polynomial.X +
    Polynomial.C ((d : ℚ) * (3 - (d : ℚ)) / 2)

/-- The hypersurface quotient has the grading induced from the homogeneous
pieces and the displayed Hilbert-function formula. -/
theorem hypersurface_graded_quotient_exists (k : Type u) [Field k]
    (d : ℕ) (hd : 0 < d) :
    ∃ G : GradedModuleData k (hypersurfaceRing k d) ℕ,
      G.LocallyFinite ∧
        (∀ n : ℕ,
          G.component n =
            (MvPolynomial.homogeneousSubmodule (Fin 3) k n).map
              (Ideal.Quotient.mkₐ k (Ideal.span {hypersurfacePolynomial k d})).toLinearMap) ∧
        ∀ n : ℕ,
          fieldDimensionHilbertFunction G n = hypersurfaceHilbertFunction d n := by
  classical
  let f : MvPolynomial (Fin 3) k := hypersurfacePolynomial k d
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
    MvPolynomial.gradedAlgebra
  have hf : MvPolynomial.IsHomogeneous f d := by
    dsimp [f, hypersurfacePolynomial]
    apply MvPolynomial.IsHomogeneous.add
    · apply MvPolynomial.IsHomogeneous.add
      · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 0 d)
      · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 1 d)
    · simpa using (MvPolynomial.isHomogeneous_X_pow (R := k) 2 d)
  have hf0 : f ≠ 0 := by
    intro h
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 d)) h
    simp only [f, hypersurfacePolynomial, MvPolynomial.coeff_add,
      MvPolynomial.coeff_X_pow, MvPolynomial.coeff_zero] at hc
    have h10 : (Finsupp.single 1 d : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 d := by
      intro h'
      have h'0 := congrArg (fun e => e 0) h'
      have h'1 := congrArg (fun e => e 1) h'
      simp [hd.ne'] at h'0 h'1
    have h20 : (Finsupp.single 2 d : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 d := by
      intro h'
      have h'0 := congrArg (fun e => e 0) h'
      have h'2 := congrArg (fun e => e 2) h'
      simp [hd.ne'] at h'0 h'2
    have hc' : (1 : k) = 0 := by
      simpa [h10, h20] using hc
    exact (one_ne_zero : (1 : k) ≠ 0) hc'
  let H : GradedModuleData k (MvPolynomial (Fin 3) k) ℕ :=
    { component := MvPolynomial.homogeneousSubmodule (Fin 3) k
      decomposition := MvPolynomial.decomposition }
  have hdimH : ∀ m : ℕ,
      Module.finrank k (H.component m) = Nat.choose (m + 2) 2 := by
    intro m
    let S : Set (Fin 3 →₀ ℕ) := {d | d.degree = m}
    let T : Finset (Fin 3 →₀ ℕ) :=
      (Finset.univ : Finset (Fin 3)).finsuppAntidiag m
    have hST : ∀ z, z ∈ (T : Set (Fin 3 →₀ ℕ)) ↔ z ∈ S := by
      intro z
      simp only [T, Finset.mem_coe, S, Finset.mem_finsuppAntidiag']
      simp only [Finsupp.sum]
      constructor
      · rintro ⟨h, _⟩
        simpa [Finsupp.degree_apply] using h
      · intro h
        exact ⟨by simpa [Finsupp.degree_apply] using h, by simp⟩
    have hSet : (T : Set (Fin 3 →₀ ℕ)) = S := by
      ext z
      exact hST z
    haveI : Finite S := by
      rw [← hSet]
      exact Set.toFinite _
    letI := Fintype.ofFinite S
    have hsub : H.component m = MvPolynomial.restrictSupport k S := by
      rw [show H.component m = MvPolynomial.homogeneousSubmodule (Fin 3) k m by rfl]
      rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
      rfl
    have hcard : Fintype.card S = T.card := by
      let e : S ≃ T :=
        { toFun := fun z => ⟨z.1, (hST z.1).2 z.2⟩
          invFun := fun z => ⟨z.1, (hST z.1).1 z.2⟩
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      simpa using Fintype.card_congr e
    have hTcard : T.card = Nat.choose (m + 2) 2 := by
      have hc := Finset.card_finsuppAntidiag_nat_eq_choose
        (s := (Finset.univ : Finset (Fin 3))) m
      have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
      rw [hcard] at hc
      rw [show 3 + m - 1 = m + 2 by omega] at hc
      rw [Nat.choose_symm_add] at hc
      exact hc
    calc
      Module.finrank k (H.component m) =
          Module.finrank k (MvPolynomial.restrictSupport k S) := by
            rw [hsub]
      _ = Fintype.card S :=
        Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k S)
      _ = T.card := hcard
      _ = Nat.choose (m + 2) 2 := hTcard
  have hcomp_mul : ∀ (m : ℕ) (g : MvPolynomial (Fin 3) k),
      MvPolynomial.homogeneousComponent m (g * f) =
        if d ≤ m then
          f * MvPolynomial.homogeneousComponent (m - d) g
        else 0 := by
    intro m g
    have hterm (i : ℕ) :
        MvPolynomial.homogeneousComponent m
            (MvPolynomial.homogeneousComponent i g * f) =
          if m = i + d then
            MvPolynomial.homogeneousComponent i g * f else 0 := by
      exact MvPolynomial.homogeneousComponent_of_mem
        ((MvPolynomial.homogeneousComponent_isHomogeneous i g).mul hf)
    calc
      MvPolynomial.homogeneousComponent m (g * f) =
          MvPolynomial.homogeneousComponent m
            ((∑ i ∈ Finset.range (g.totalDegree + 1),
              MvPolynomial.homogeneousComponent i g) * f) := by
                rw [MvPolynomial.sum_homogeneousComponent]
      _ = ∑ i ∈ Finset.range (g.totalDegree + 1),
            (if m = i + d then
              MvPolynomial.homogeneousComponent i g * f else 0) := by
        rw [Finset.sum_mul, map_sum]
        simp_rw [hterm]
      _ = if d ≤ m then
            f * MvPolynomial.homogeneousComponent (m - d) g else 0 := by
        by_cases hdm : d ≤ m
        · let j := m - d
          by_cases hj : j ∈ Finset.range (g.totalDegree + 1)
          · rw [Finset.sum_eq_single j]
            · have hmj : m = j + d := by
                dsimp [j]
                omega
              rw [if_pos hmj]
              simp [hmj, mul_comm]
            · intro i hi hne
              rw [if_neg]
              intro heq
              apply hne
              dsimp [j]
              omega
            · intro hj'
              exact (hj' hj).elim
          · have hjgt : g.totalDegree < j := by
              simpa [Finset.mem_range] using hj
            have hz : MvPolynomial.homogeneousComponent j g = 0 :=
              MvPolynomial.homogeneousComponent_eq_zero j g hjgt
            rw [if_pos hdm, hz, mul_zero]
            apply Finset.sum_eq_zero
            intro i hi
            rw [if_neg]
            intro heq
            apply hj
            rw [Finset.mem_range]
            have hi' : i ≤ g.totalDegree := by
              simpa [Finset.mem_range] using hi
            dsimp [j]
            omega
        · rw [if_neg hdm]
          apply Finset.sum_eq_zero
          intro i hi
          rw [if_neg]
          omega
  have hmul_inj (m : ℕ) :
      Function.Injective
        ((LinearMap.mulLeft k f).domRestrict
          (H.component m)) := by
    intro x y hxy
    apply Subtype.ext
    change f * (x : MvPolynomial (Fin 3) k) =
        f * (y : MvPolynomial (Fin 3) k) at hxy
    exact mul_left_cancel₀ hf0 hxy
  have hI : (Ideal.span {f}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl
    exact ⟨d, hf⟩
  have hfiniteH : H.LocallyFinite := by
    intro n
    exact Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) k n)
  let q : MvPolynomial (Fin 3) k →ₗ[k] hypersurfaceRing k d :=
    (Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap
  have hq : ∀ p : MvPolynomial (Fin 3) k, q p = 0 ↔ p ∈ Ideal.span {f} := by
    intro p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqsurj : Function.Surjective q := by
    exact Ideal.Quotient.mkₐ_surjective k (Ideal.span {f})
  have hkerq : LinearMap.ker q = (Ideal.span {f}).restrictScalars k := by
    ext p
    change q p = 0 ↔ p ∈ Ideal.span {f}
    exact hq p
  letI : DirectSum.Decomposition (fun n : ℕ => H.component n) := H.decomposition
  rcases graded_quotient_data H (Ideal.span {f}) q hq hqsurj hI with ⟨G, hG⟩
  have hintersection (n : ℕ) (hdn : d ≤ n) :
      LinearMap.range
          ((LinearMap.mulLeft k f).domRestrict (H.component (n - d))) =
        H.component n ⊓ (Ideal.span {f}).restrictScalars k := by
    let mulf : H.component (n - d) →ₗ[k] MvPolynomial (Fin 3) k :=
      (LinearMap.mulLeft k f).domRestrict (H.component (n - d))
    change LinearMap.range mulf = H.component n ⊓ (Ideal.span {f}).restrictScalars k
    apply le_antisymm
    · rintro p ⟨g, rfl⟩
      constructor
      · change f * (g : MvPolynomial (Fin 3) k) ∈ H.component n
        change MvPolynomial.IsHomogeneous
          (f * (g : MvPolynomial (Fin 3) k)) n
        have hg : MvPolynomial.IsHomogeneous
            (g : MvPolynomial (Fin 3) k) (n - d) := g.property
        convert hf.mul hg using 1 <;> omega
      · exact Ideal.mem_span_singleton'.mpr ⟨(g : MvPolynomial (Fin 3) k), by
          change (g : MvPolynomial (Fin 3) k) * f =
            f * (g : MvPolynomial (Fin 3) k)
          ac_rfl⟩
    · rintro p ⟨hp, hpI⟩
      rcases Ideal.mem_span_singleton'.mp hpI with ⟨g, hg⟩
      let g' : H.component (n - d) :=
        ⟨MvPolynomial.homogeneousComponent (n - d) g,
          MvPolynomial.homogeneousComponent_mem _ _⟩
      refine ⟨g', ?_⟩
      change f * MvPolynomial.homogeneousComponent (n - d) g = p
      calc
        f * MvPolynomial.homogeneousComponent (n - d) g =
            MvPolynomial.homogeneousComponent n (g * f) := by
              rw [hcomp_mul n g, if_pos hdn]
        _ = MvPolynomial.homogeneousComponent n p := by rw [hg]
        _ = p := MvPolynomial.homogeneousComponent_eq_self hp
  have hintersection_zero (n : ℕ) (hn : ¬ d ≤ n) :
      H.component n ⊓ (Ideal.span {f}).restrictScalars k =
        (⊥ : Submodule k (MvPolynomial (Fin 3) k)) := by
    apply bot_unique
    rintro p ⟨hp, hpI⟩
    rcases Ideal.mem_span_singleton'.mp hpI with ⟨g, hg⟩
    have hp0 : p = 0 := by
      calc
        p = MvPolynomial.homogeneousComponent n p :=
          (MvPolynomial.homogeneousComponent_eq_self hp).symm
        _ = MvPolynomial.homogeneousComponent n (g * f) := by rw [hg]
        _ = 0 := by rw [hcomp_mul n g, if_neg hn]
    exact hp0 ▸ Submodule.zero_mem _
  have hdim_component (n : ℕ) :
      Module.finrank k (G.component n) =
        if d ≤ n then
          Module.finrank k (H.component n) -
            Module.finrank k (H.component (n - d))
        else Module.finrank k (H.component n) := by
    letI : Module.Finite k (H.component n) := hfiniteH n
    let qn : H.component n →ₗ[k] hypersurfaceRing k d :=
      q.domRestrict (H.component n)
    let K : Submodule k (MvPolynomial (Fin 3) k) :=
      H.component n ⊓ (Ideal.span {f}).restrictScalars k
    have hrange : LinearMap.range qn = G.component n := by
      rw [hG n]
      exact LinearMap.range_domRestrict _ _
    have hkerqn : LinearMap.ker qn =
        ((Ideal.span {f}).restrictScalars k).comap (H.component n).subtype := by
      dsimp [qn]
      rw [LinearMap.ker_domRestrict, hkerq]
    have hkerdimn :
        Module.finrank k (LinearMap.ker qn) =
          Module.finrank k K := by
      calc
        Module.finrank k (LinearMap.ker qn) =
            Module.finrank k
              ((LinearMap.ker qn).map (H.component n).subtype) := by
                symm
                rw [Submodule.finrank_map_subtype_eq]
        _ = Module.finrank k K := by
          rw [hkerqn, Submodule.map_comap_subtype]
    have hrank := qn.finrank_range_add_finrank_ker
    rw [hrange] at hrank
    by_cases hdn : d ≤ n
    · have hkerdim_mul :
          Module.finrank k (LinearMap.ker qn) =
            Module.finrank k (H.component (n - d)) := by
        calc
          Module.finrank k (LinearMap.ker qn) =
              Module.finrank k K := hkerdimn
          _ = Module.finrank k
                (LinearMap.range
                  ((LinearMap.mulLeft k f).domRestrict (H.component (n - d)))) := by
            simpa [K] using
              congrArg (fun L : Submodule k (MvPolynomial (Fin 3) k) =>
                Module.finrank k L) (hintersection n hdn).symm
          _ = Module.finrank k (H.component (n - d)) :=
            LinearMap.finrank_range_of_inj (hmul_inj (n - d))
      rw [hkerdim_mul] at hrank
      simp only [if_pos hdn]
      omega
    · have hkerdim_zero : Module.finrank k (LinearMap.ker qn) = 0 := by
        calc
          Module.finrank k (LinearMap.ker qn) =
              Module.finrank k K := hkerdimn
          _ = Module.finrank k (⊥ : Submodule k (MvPolynomial (Fin 3) k)) := by
            simpa [K] using
              congrArg (fun L : Submodule k (MvPolynomial (Fin 3) k) =>
                Module.finrank k L) (hintersection_zero n hdn)
          _ = 0 := by simp
      rw [hkerdim_zero] at hrank
      simp only [if_neg hdn]
      omega
  refine ⟨G, ?_, ?_, ?_⟩
  · intro n
    letI : Module.Finite k (H.component n) := hfiniteH n
    rw [hG n]
    exact Module.Finite.map (H.component n) q
  · intro n
    simpa [f] using hG n
  · intro n
    change Module.finrank k (G.component n) = hypersurfaceHilbertFunction d n
    by_cases hdn : d ≤ n
    · rw [hdim_component n, if_pos hdn, hdimH n, hdimH (n - d)]
      simp [hypersurfaceHilbertFunction, hdn]
    · rw [hdim_component n, if_neg hdn, hdimH n]
      simp [hypersurfaceHilbertFunction, hdn]

/-- For positive `d`, the hypersurface Hilbert function eventually agrees with
the stated numerical polynomial. -/
theorem hypersurface_hilbert_polynomial (d : ℕ) (hd : 0 < d) :
    IsNumericalPolynomial (hypersurfaceHilbertPolynomial d) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (hypersurfaceHilbertFunction d n : ℚ) =
          (hypersurfaceHilbertPolynomial d).eval (n : ℚ) := by
  constructor
  · intro z
    refine ⟨(d : ℤ) * z + ((d : ℤ) * (3 - (d : ℤ)) / 2), ?_⟩
    simp [hypersurfaceHilbertPolynomial, Polynomial.eval_add, Polynomial.eval_mul]
    have heven : Even ((d : ℤ) * (3 - (d : ℤ))) := by
      rcases Nat.even_or_odd d with h | h
      · obtain ⟨c, hc⟩ := h
        refine ⟨(c : ℤ) * (3 - (d : ℤ)), ?_⟩
        rw [hc]
        push_cast
        ring
      · obtain ⟨c, hc⟩ := h
        refine ⟨(d : ℤ) * (1 - (c : ℤ)), ?_⟩
        rw [hc]
        push_cast
        ring
    rw [Int.cast_div_charZero heven.two_dvd]
    push_cast
    ring
  · filter_upwards [Filter.eventually_ge_atTop d] with n hn
    simp only [hypersurfaceHilbertFunction, hypersurfaceHilbertPolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [if_pos hn]
    have hchoose : (n - d + 2).choose 2 ≤ (n + 2).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    rw [Nat.cast_sub hchoose]
    rw [Nat.choose_two_right, Nat.choose_two_right]
    have hdiv₁ : 2 ∣ (n + 2) * (n + 2 - 1) := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one (n + 1)
    have hdiv₂ : 2 ∣ (n - d + 2) * (n - d + 2 - 1) := by
      simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one (n - d + 1)
    rw [Nat.cast_div_charZero hdiv₁, Nat.cast_div_charZero hdiv₂]
    push_cast
    rw [Nat.cast_sub hn]
    ring

end Formalization.Books.Exercises.Unit26
