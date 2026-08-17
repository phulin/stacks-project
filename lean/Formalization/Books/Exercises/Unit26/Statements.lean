import Formalization.Books.Exercises.Unit26.Core
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
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
    · intro α β _ e h Q _ _ _ _ φ
      letI : Fintype α := Fintype.ofEquiv β e.symm
      letI : Finite α := Fintype.finite _
      letI : Finite β := Fintype.finite _
      let Q' : α → Type := fun i => Q (e i)
      letI : Module.Finite ℤ (DirectSum α Q') :=
        Module.Finite.instDirectSum Q'
      letI : Module.Finite ℤ (DirectSum β (fun k => Q' (e.symm k))) :=
        Module.Finite.instDirectSum _
      have h' := h Q' φ
      have he :
          φ (FGModuleCat.of ℤ (DirectSum α Q')) =
            φ (FGModuleCat.of ℤ (DirectSum β (fun k => Q' (e.symm k)))) :=
        hIso φ (DirectSum.lequivCongrLeft ℤ e)
      calc
        φ (FGModuleCat.of ℤ (DirectSum β Q)) =
            φ (FGModuleCat.of ℤ (DirectSum α Q')) := by
          simpa [Q'] using he.symm
        _ = ∑ i : α, φ (FGModuleCat.of ℤ (Q' i)) := h'
        _ = ∑ i : α, φ (FGModuleCat.of ℤ (Q (e i))) := by rfl
        _ = ∑ i : β, φ (FGModuleCat.of ℤ (Q i)) := e.sum_comp _
    · intro Q _ _ _ _ φ
      letI : Finite PEmpty := Fintype.finite _
      have h := hsubzero φ (V := DirectSum PEmpty Q)
      simpa using h
    · intro α _ h Q _ _ _ _ φ
      letI : Finite α := Fintype.finite _
      let Q' : α → Type := fun i => Q (some i)
      letI : Module.Finite ℤ (DirectSum α Q') :=
        Module.Finite.instDirectSum Q'
      letI : Module.Finite ℤ (DirectSum α (fun i => Q (some i))) :=
        Module.Finite.instDirectSum _
      have h' := h Q' φ
      have he :
          φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ
              (Q none × DirectSum α (fun i => Q (some i)))) :=
        hIso φ (DirectSum.lequivProdDirectSum ℤ (α := Q))
      calc
        φ (FGModuleCat.of ℤ (DirectSum (Option α) Q)) =
            φ (FGModuleCat.of ℤ (Q none × DirectSum α Q')) := by
          simpa [Q'] using he
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            φ (FGModuleCat.of ℤ (DirectSum α Q')) := hprod φ
        _ = φ (FGModuleCat.of ℤ (Q none)) +
            ∑ i : α, φ (FGModuleCat.of ℤ (Q' i)) := by rw [h']
        _ = ∑ i : Option α, φ (FGModuleCat.of ℤ (Q i)) := by
          simp [Q', Fintype.sum_option]
  have hfree : ∀ (φ : EulerPoincareFunction ℤ) (n : ℕ),
      φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) =
        integerEulerParameter φ * (n : ℤ) := by
    intro φ n
    letI : Module.Finite ℤ (DirectSum (Fin n) (fun _ => ℤ)) :=
      Module.Finite.instDirectSum _
    have h := hDS (Fin n) (fun _ => ℤ) φ
    simpa [integerEulerParameter, Finset.sum_const, nsmul_eq_mul] using h
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
      simp [f, g, L]
    have hker : ∀ x, g x = 0 → x ∈ LinearMap.range f := by
      intro x hx
      have hxL : x ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hx
      rcases (Submodule.mem_span_singleton.mp hxL) with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simpa [f, LinearMap.toSpanSingleton_apply, L, smul_eq_mul] using hc.symm
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
          exact congrArg (fun q : Q => q) (by simpa [g, f, L] using hcomp x))
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
    have h' : φ (FGModuleCat.of ℤ Q) =
        φ (FGModuleCat.of ℤ ℤ) + φ (FGModuleCat.of ℤ Q) := by
      simpa [S] using h
    have hz : φ (FGModuleCat.of ℤ Q) = 0 := by
      rw [integerEulerParameter] at h'
      omega
    simpa [Q, L] using hz
  have hclass : ∀ (φ : EulerPoincareFunction ℤ) (M : FGModuleCat ℤ),
      ∃ n : ℕ, φ M = integerEulerParameter φ * (n : ℤ) := by
    intro φ M
    obtain ⟨n, ι, fι, p, hp, powExp, ⟨eM⟩⟩ :=
      Module.equiv_free_prod_directSum (R := ℤ) (M := (M : Type))
    letI : Fintype ι := fι
    let Q : ι → Type := fun i => ℤ ⧸ ℤ ∙ p i ^ powExp i
    letI : Module.Finite ℤ (DirectSum ι Q) :=
      Module.Finite.instDirectSum Q
    have hsum : ∑ i : ι, φ (FGModuleCat.of ℤ (Q i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simpa [Q] using
        hcyclic φ (p i ^ powExp i) (pow_ne_zero _ (hp i).ne_zero)
    have hds := hDS ι Q φ
    refine ⟨n, ?_⟩
    change φ (FGModuleCat.of ℤ (M : Type)) =
      integerEulerParameter φ * (n : ℤ)
    calc
      φ (FGModuleCat.of ℤ (M : Type)) =
          φ (FGModuleCat.of ℤ ((Fin n →₀ ℤ) × DirectSum ι Q)) :=
        hIso φ eM
      _ = φ (FGModuleCat.of ℤ (Fin n →₀ ℤ)) +
          φ (FGModuleCat.of ℤ (DirectSum ι Q)) := hprod φ
      _ = integerEulerParameter φ * (n : ℤ) := by
        rw [hfree φ n, hds, hsum, add_zero]
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
      rw [← hrange]
    have hrangef : Module.finrank ℤ (LinearMap.range f) =
        Module.finrank ℤ (S.X₁ : Type) := LinearMap.finrank_range_of_inj hf
    change Module.finrank ℤ (S.X₂ : Type) =
      Module.finrank ℤ (S.X₁ : Type) + Module.finrank ℤ (S.X₃ : Type)
    calc
      Module.finrank ℤ (S.X₂ : Type) =
          Module.finrank ℤ (LinearMap.range g) +
            Module.finrank ℤ (LinearMap.ker g) := hdim.symm
      _ = Module.finrank ℤ (S.X₃ : Type) +
          Module.finrank ℤ (LinearMap.range f) := by
        rw [show LinearMap.range g = ⊤ from LinearMap.range_eq_top.mpr hg,
          finrank_top, hker]
      _ = Module.finrank ℤ (S.X₁ : Type) +
          Module.finrank ℤ (S.X₃ : Type) := by rw [hrangef]; ac_rfl
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
          obtain ⟨n, hφM⟩ := hclass (⟨φ, hφ⟩ : EulerPoincareFunction ℤ) M
          obtain ⟨m, hψM⟩ := hclass (⟨ψ, hψ⟩ : EulerPoincareFunction ℤ) M
          calc
            φ M = φ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by
              rw [hφM]
            _ = ψ (FGModuleCat.of ℤ ℤ) * (n : ℤ) := by rw [hparam]
            _ = ψ M := by
              rw [hψM]
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
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (G : GradedModuleData A M ℕ) (p : Submodule A M)
    (hp : SetLike.IsHomogeneous (fun n : ℕ => G.component n) p) :
    ∃ Gq : GradedModuleData A (M ⧸ p) ℕ,
      ∀ n : ℕ, Gq.component n = (G.component n).map p.mkQ := by
  classical
  let C : ℕ → Submodule A M := fun n => G.component n
  let Q : ℕ → Submodule A (M ⧸ p) := fun n => (C n).map p.mkQ
  letI : DirectSum.Decomposition C := G.decomposition
  let r : ∀ n : ℕ, C n →ₗ[A] Q n := fun n =>
    { toFun := fun x => ⟨p.mkQ (x : M), ⟨x, x.property, rfl⟩⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hr : ∀ n : ℕ, Function.Surjective (r n) := by
    intro n y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let L : (⨁ n : ℕ, C n) →ₗ[A] (⨁ n : ℕ, Q n) := DirectSum.lmap r
  have hLsurj : Function.Surjective L :=
    (DirectSum.lmap_surjective r).2 hr
  let e : M ≃ₗ[A] (⨁ n : ℕ, C n) := DirectSum.decomposeLinearEquiv C
  let d : M →ₗ[A] (⨁ n : ℕ, Q n) := L.comp e.toLinearMap
  have hdp : p ≤ LinearMap.ker d := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext n
    apply Subtype.ext
    change p.mkQ ((e x n : C n) : M) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hp n hx
  let dq : (M ⧸ p) →ₗ[A] (⨁ n : ℕ, Q n) := p.liftQ d hdp
  have hdq_surj : Function.Surjective dq := by
    intro z
    rcases hLsurj z with ⟨x, hx⟩
    refine ⟨p.mkQ x, ?_⟩
    simpa [dq] using hx
  have hdq_inj : Function.Injective dq := by
    rintro ⟨x⟩ ⟨y⟩ hxy
    have hzero : d (x - y) = 0 := by
      have hqzero : dq (p.mkQ (x - y)) = 0 := by
        rw [map_sub, hxy, sub_self]
      simpa [dq] using hqzero
    have hcomponents : ∀ n : ℕ, (e (x - y) n : M) ∈ p := by
      intro n
      have hn : r n (e (x - y) n) = 0 := by
        have := congrArg (fun z : (⨁ n : ℕ, Q n) => z n) hzero
        simpa [d, L] using this
      have hn' := congrArg Subtype.val hn
      change p.mkQ ((e (x - y) n : C n) : M) = 0 at hn'
      exact (Submodule.Quotient.mk_eq_zero p).mp hn'
    have hmem : x - y ∈ p :=
      (AddSubmonoidClass.IsHomogeneous.mem_iff C p hp).2 (by
        intro n
        simpa [e, C] using hcomponents n)
    apply (Submodule.Quotient.mk_eq_zero p).mp
    simpa [map_sub] using hmem
  let coe : (⨁ n : ℕ, Q n) →ₗ[A] (M ⧸ p) := DirectSum.coeLinearMap Q
  have hcoe_d : coe.comp d = p.mkQ := by
    apply DirectSum.decompose_lhom_ext C
    intro n
    ext x
    simp [coe, d, L, e, r, C]
  have hcoe_dq : coe.comp dq = LinearMap.id := by
    apply Submodule.linearMap_qext
    rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ, hcoe_d, LinearMap.id_comp]
  have hdq_coe : dq.comp coe = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rcases hdq_surj z with ⟨x, hx⟩
    have hx' := DFunLike.congr_fun hcoe_dq x
    rw [← hx, LinearMap.comp_apply, hx']
  let dec : DirectSum.Decomposition Q :=
    DirectSum.Decomposition.ofLinearMap dq hcoe_dq hdq_coe
  let Gq : GradedModuleData A (M ⧸ p) ℕ :=
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
  have hI : (truncatedPolynomialIdeal k).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights) := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl | rfl
    · refine ⟨4, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.pow
          (MvPolynomial.isWeightedHomogeneous_X twoThreeWeights 0) 2)
    · refine ⟨5, ?_⟩
      simpa [twoThreeWeights] using
        (MvPolynomial.IsWeightedHomogeneous.mul
          (MvPolynomial.isWeightedHomogeneous_X twoThreeWeights 0)
          (MvPolynomial.isWeightedHomogeneous_X twoThreeWeights 1))
  rcases graded_quotient_data (weightedPolynomialGradedModule k)
      (truncatedPolynomialIdeal k) hI with ⟨G, hG⟩
  have hfinite : ∀ n : ℕ, Module.Finite k (G.component n) := by
    intro n
    rw [hG n]
    letI : Module.Finite k
        (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights n) :=
      weighted_polynomial_grading_locally_finite k n
    infer_instance
  let s : Set (Fin 2 →₀ ℕ) :=
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1}
  have hIeq : truncatedPolynomialIdeal k =
      Ideal.span ((fun d => MvPolynomial.monomial d (1 : k)) '' s) := by
    ext p
    simp [truncatedPolynomialIdeal, s, MvPolynomial.X, pow_two]
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
    rcases hd0 with rfl | rfl
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
    have hweight := hp d (MvPolynomial.mem_support_iff.mp hd)
    have hweight' : 2 * d 0 + 3 * d 1 = n := by
      simpa [Finsupp.weight_eq_sum, twoThreeWeights] using hweight
    exact hgen hweight' hbad
  have hnotgen0 : ¬ ∃ si ∈ s, si ≤ (0 : Fin 2 →₀ ℕ) := by
    simp [s]
  have hnotgen2 : ¬ ∃ si ∈ s, si ≤ Finsupp.single 0 1 := by
    simp [s]
  have hnotgenc (c : ℕ) :
      ¬ ∃ si ∈ s, si ≤ Finsupp.single 1 c := by
    simp [s]
  have hmonoI : ∀ {d : Fin 2 →₀ ℕ} {r : k},
      (∃ si ∈ s, si ≤ d) →
        MvPolynomial.monomial d r ∈ truncatedPolynomialIdeal k := by
    intro d r hgen'
    rw [hIeq]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro di hdi
    have hdi' : di = d := by simpa using hdi
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
      · exact ⟨Finsupp.single 0 2, by simp [s], by
          intro i
          fin_cases i <;> simp <;> omega⟩
      · have hone : d 0 = 1 := by omega
        exfalso
        omega
  have hmap0 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).map
          (truncatedPolynomialIdeal k).mkQ =
        k ∙ (truncatedPolynomialIdeal k).mkQ
          (MvPolynomial.monomial 0 (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change (truncatedPolynomialIdeal k).mkQ p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp d (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 0 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights] using hweight
      have hdeq := hclass0 hweight'
      subst d
      rw [← MvPolynomial.C_mul_monomial]
      simp only [map_smul, Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply Submodule.mem_map
      refine ⟨a • MvPolynomial.monomial 0 (1 : k), ?_, ?_⟩
      · rw [← MvPolynomial.C_mul_monomial]
        exact (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 0).smul_mem
          _ (by exact MvPolynomial.isWeightedHomogeneous_one k twoThreeWeights)
      · rw [map_smul]
        rfl
  have hmap2 :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).map
          (truncatedPolynomialIdeal k).mkQ =
        k ∙ (truncatedPolynomialIdeal k).mkQ
          (MvPolynomial.monomial (Finsupp.single 0 1) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change (truncatedPolynomialIdeal k).mkQ p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp d (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 2 := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights] using hweight
      have hdeq := hclass2 hweight'
      subst d
      rw [← MvPolynomial.C_mul_monomial]
      simp only [map_smul, Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span _)
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply Submodule.mem_map
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 0 1) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights 2).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights])
      · rw [map_smul]
        rfl
  have hmapc (c : ℕ) :
      (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).map
          (truncatedPolynomialIdeal k).mkQ =
        k ∙ (truncatedPolynomialIdeal k).mkQ
          (MvPolynomial.monomial (Finsupp.single 1 c) (1 : k)) := by
    apply le_antisymm
    · rintro y ⟨p, hp, rfl⟩
      change (truncatedPolynomialIdeal k).mkQ p ∈ _
      rw [p.as_sum, map_sum]
      apply Submodule.sum_mem
      intro d hd
      have hweight := hp d (MvPolynomial.mem_support_iff.mp hd)
      have hweight' : 2 * d 0 + 3 * d 1 = 3 * c := by
        simpa [Finsupp.weight_eq_sum, twoThreeWeights] using hweight
      rcases hclassc hweight' with rfl | ⟨si, hsi, hle⟩
      · rw [← MvPolynomial.C_mul_monomial]
        simp only [map_smul, Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span _)
      · have hi := hmonoI hsi
        rw [Submodule.Quotient.mk_eq_zero.mpr hi]
        exact Submodule.zero_mem _
    · intro y hy
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨a, rfl⟩
      apply Submodule.mem_map
      refine ⟨a • MvPolynomial.monomial (Finsupp.single 1 c) (1 : k), ?_, ?_⟩
      · apply (MvPolynomial.weightedHomogeneousSubmodule k twoThreeWeights (3 * c)).smul_mem
        exact MvPolynomial.isWeightedHomogeneous_monomial twoThreeWeights _ _ (by
          simp [Finsupp.weight_eq_sum, twoThreeWeights])
      · rw [map_smul]
        rfl
  refine ⟨G, hfinite, ?_, ?_⟩
  · intro n
    rw [hG n]
    rfl
  · sorry

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
  sorry

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
