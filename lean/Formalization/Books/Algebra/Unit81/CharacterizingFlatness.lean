import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit11.CharacterizingFinite
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Commutative Algebra, Chapter 81: Characterizing flatness

The source's finite free modules are represented by `Fin n →₀ R`, Mathlib's
canonical finite-rank free modules.  Directed module systems are represented
by `DirectedSystem` data and the explicit directed colimit `DirectLimit`.
The filtered-colimit presentation of an arbitrary module is already exposed
by Chapter 11, and flatness of a directed limit is already exposed by Chapter
39; the declarations below use those interfaces rather than introducing
parallel predicates.
-/

namespace Formalization.Books.Algebra.Unit81

open Formalization.Books.Algebra.Unit10

universe u v z

/-! ## Factorization through finite free modules -/

/- The source's phrase `N + Rx` is the submodule supremum
   `N ⊔ Submodule.span R {x}`. -/

/-- The four equivalent factorization conditions for a flat module.

This is the source's `lemma-flat-factors-free`.  The finite free modules
`R^n` and `R^m` are written as `Fin n →₀ R` and `Fin m →₀ R`, respectively.
-/
theorem flat_factors_free
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    List.TFAE [
      Module.Flat R M,
      ∀ {n : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        {x : Fin n →₀ R}, x ∈ LinearMap.ker f →
        ∃ (m : ℕ) (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g.comp h ∧ x ∈ LinearMap.ker h,
      ∀ {n m : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        (N : Submodule R (Fin n →₀ R)),
        N ≤ LinearMap.ker f →
        ∀ (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)),
        N ≤ LinearMap.ker h →
        (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g.comp h) →
        ∀ {x : Fin n →₀ R}, x ∈ LinearMap.ker f →
          ∃ (m' : ℕ) (h' : (Fin n →₀ R) →ₗ[R] (Fin m' →₀ R)),
            N ⊔ Submodule.span R ({x} : Set (Fin n →₀ R)) ≤
                LinearMap.ker h' ∧
              ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g'.comp h',
      ∀ {n : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        (N : Submodule R (Fin n →₀ R)),
        N ≤ LinearMap.ker f → N.FG →
      ∃ (m : ℕ) (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g.comp h ∧ N ≤ LinearMap.ker h] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h n f x hx
      obtain ⟨m, h', g, hfg, hx'⟩ :=
        (Module.Flat.iff_forall_exists_factorization (R := R) (M := M)).1 h hx
      exact ⟨m, h', g, by simpa using hfg, by simpa using hx'⟩
    · intro h
      refine (Module.Flat.iff_forall_exists_factorization (R := R) (M := M)).2 (by
        intro n f x hx
        obtain ⟨m, h', g, hfg, hx'⟩ := h x hx
        exact ⟨m, h', g, by simpa using hfg, by simpa using hx'⟩)
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h n f N hN hNfg
      let _ : Module.Finite R N := Module.Finite.of_fg hNfg
      have hcomp : f.comp N.subtype = 0 := by
        ext y
        exact LinearMap.mem_ker.mp (hN y.property)
      obtain ⟨m, h', g, hfg, hker⟩ :=
        Module.Flat.exists_factorization_of_comp_eq_zero_of_free
          (M := M) (K := N) (N := Fin n →₀ R) (f := N.subtype) (x := f) hcomp
      refine ⟨m, h', g, by simpa using hfg, ?_⟩
      intro y hy
      apply LinearMap.mem_ker.mpr
      have hy' := congrArg (fun k => k ⟨y, hy⟩) hker
      simpa [LinearMap.comp_apply] using hy'
    · intro h
      refine (Module.Flat.iff_forall_exists_factorization (R := R) (M := M)).2 (by
        intro n a x hx
        obtain ⟨m, h', g, hfg, hker⟩ :=
          h x (Submodule.span R ({a} : Set (Fin n →₀ R)))
            (by
              refine Submodule.span_le.2 ?_
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              subst y
              exact hx)
            (Submodule.fg_span (Set.finite_singleton a))
        exact ⟨m, h', g, hfg, hker (Submodule.subset_span (by simp))⟩)
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hcond n m f N hN k hk hfac x hx
      obtain ⟨g, hfg⟩ := hfac
      have hxg : k x ∈ LinearMap.ker g := by
        apply LinearMap.mem_ker.mpr
        have hxg' := LinearMap.congr_fun hfg x
        simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp hx] using hxg'.symm
      obtain ⟨m', h', g', hgg, hx'⟩ := hcond g hxg
      refine ⟨m', h'.comp k, ?_, ?_⟩
      · refine sup_le ?_ ?_
        · intro y hy
          apply LinearMap.mem_ker.mpr
          simp [LinearMap.comp_apply, LinearMap.mem_ker.mp (hk hy)]
        · refine Submodule.span_le.2 ?_
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          apply LinearMap.mem_ker.mpr
          simpa [LinearMap.comp_apply] using LinearMap.mem_ker.mp hx'
      · refine ⟨g', ?_⟩
        calc
          f = g.comp k := hfg
          _ = (g'.comp h').comp k := by rw [hgg]
          _ = g'.comp (h'.comp k) := by simp [LinearMap.comp_assoc]
    · intro hcond n f x hx
      have hN : (⊥ : Submodule R (Fin n →₀ R)) ≤ LinearMap.ker f := bot_le
      have hid : (⊥ : Submodule R (Fin n →₀ R)) ≤
          LinearMap.ker (LinearMap.id : (Fin n →₀ R) →ₗ[R] (Fin n →₀ R)) := bot_le
      have hfac : ∃ g : (Fin n →₀ R) →ₗ[R] M,
          f = g.comp (LinearMap.id : (Fin n →₀ R) →ₗ[R] (Fin n →₀ R)) :=
        ⟨f, by simp⟩
      obtain ⟨m', h', hker, ⟨g', hfg'⟩⟩ :=
        hcond f ⊥ hN (LinearMap.id : (Fin n →₀ R) →ₗ[R] (Fin n →₀ R)) hid hfac hx
      refine ⟨m', h', g', hfg', ?_⟩
      apply hker
      exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
  tfae_finish

/-! ## Finitely presented sources and Hom lifting -/

/-- A map from a finitely presented module to a flat module factors through a
finite free module.

This is the source's `lemma-flat-factors-fp`; the finite free target is put in
Mathlib's canonical `Fin n →₀ R` form. -/
theorem flat_factors_finitePresentation
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Type u) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P] (f : P →ₗ[R] M),
      ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R))
          (g : (Fin n →₀ R) →ₗ[R] M), f = g.comp h := by
  constructor
  · intro h P _ _ _ f
    let _ : Module.Flat R M := h
    exact Module.Flat.exists_factorization_of_finitePresentation f
  · intro h
    apply Module.Flat.of_forall_exists_factorization
    intro l f x hx
    sorry

/-- Flatness is equivalent to lifting maps from finitely presented modules
through every surjection by postcomposition on `Hom`.

This is the source's `lemma-flat-surjective-hom`; `internalHomPostcomp` is
Chapter 10's canonical implementation of the induced Hom map. -/
theorem flat_iff_surjective_hom
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Type u) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P]
        (N : Type (max u v)) [AddCommGroup N] [Module R N]
        (q : N →ₗ[R] M), Function.Surjective q →
        Function.Surjective (internalHomPostcomp (M := P) q) := by
  constructor
  · intro h P _ _ _ N _ _ q hq
    let _ : Module.Flat R M := h
    intro φ
    obtain ⟨n, h', g, hφ⟩ :=
      Module.Flat.exists_factorization_of_finitePresentation φ
    obtain ⟨g', hg'⟩ := Module.projective_lifting_property q g hq
    refine ⟨g'.comp h', ?_⟩
    ext x
    simp [LinearMap.comp_apply,
      ← LinearMap.congr_fun hg' (h' x), hφ]
  · intro h
    sorry

/-! ## Directed systems and Lazard's theorem -/

/- A directed system of finite free modules together with its identification
   with the target module.  `DirectLimit` is Mathlib's explicit colimit model
   for a directed system; the existing `directLimit_flat` theorem from Chapter
   39 supplies the flatness assertion used in the source's forward direction.
-/
structure DirectedFreeFiniteSystem
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] where
  index : Type (max u v)
  [indexPreorder : Preorder index]
  [indexNonempty : Nonempty index]
  [indexDirected : IsDirectedOrder index]
  stage : index → Type (max u v)
  [stageAddCommGroup : ∀ i, AddCommGroup (stage i)]
  [stageModule : ∀ i, Module R (stage i)]
  map : ∀ i j, i ≤ j → stage i →ₗ[R] stage j
  [stageDirectedSystem : DirectedSystem stage (map · · ·)]
  free : ∀ i, Module.Free R (stage i)
  finite : ∀ i, Module.Finite R (stage i)
  targetIso : Nonempty (DirectLimit stage map ≃ₗ[R] M)

/- The preliminary assertion in Lazard's proof that every module is a
   filtered colimit of finitely presented modules is already represented by
   `Unit11.exists_filteredColimit_finitelyPresented`, with its canonical
   `FilteredFinitelyPresentedModuleColimit` witness. -/

/-- **Lazard's theorem.** A module is flat exactly when it is a directed
colimit of finite free modules. -/
theorem lazard
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ Nonempty (DirectedFreeFiniteSystem (R := R) (M := M)) := by
  constructor
  · intro h
    sorry
  · intro ⟨s⟩
    let : Preorder s.index := s.indexPreorder
    let : Nonempty s.index := s.indexNonempty
    let : IsDirectedOrder s.index := s.indexDirected
    let : ∀ i, AddCommGroup (s.stage i) := s.stageAddCommGroup
    let : ∀ i, Module R (s.stage i) := s.stageModule
    let : DirectedSystem s.stage (s.map · · ·) := s.stageDirectedSystem
    let hflat : Module.Flat R (DirectLimit s.stage s.map) :=
      Formalization.Books.Algebra.Unit39.directLimit_flat s.map (fun i => by
        let _ : Module.Free R (s.stage i) := s.free i
        infer_instance)
    let _ : Module.Flat R (DirectLimit s.stage s.map) := hflat
    exact Module.Flat.of_linearEquiv (M := DirectLimit s.stage s.map)
      s.targetIso.some.symm

end Formalization.Books.Algebra.Unit81
