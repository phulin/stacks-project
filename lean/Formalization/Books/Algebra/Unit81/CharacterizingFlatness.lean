import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit11.CharacterizingFinite
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Finiteness.Prod

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
open CategoryTheory
open CategoryTheory.Limits

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
    let : Module.Flat R M := h
    exact Module.Flat.exists_factorization_of_finitePresentation f
  · intro h
    apply Module.Flat.of_forall_exists_factorization
    intro l f x hx
    let S : Submodule R (Fin l →₀ R) := Submodule.span R ({f} : Set (Fin l →₀ R))
    let Q : Type u := (Fin l →₀ R) ⧸ S
    have hfree : Module.FinitePresentation R (Fin l →₀ R) := inferInstance
    let : Module.FinitePresentation R Q :=
      Module.finitePresentation_of_surjective (h := hfree) S.mkQ S.mkQ_surjective
        (by
          rw [Submodule.ker_mkQ]
          dsimp [S]
          exact Submodule.fg_span (Set.finite_singleton f))
    have hS : S ≤ LinearMap.ker x := by
      dsimp [S]
      refine Submodule.span_le.2 ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact LinearMap.mem_ker.mpr hx
    let xbar : Q →ₗ[R] M := S.liftQ x hS
    obtain ⟨n, a, g, hag⟩ := h Q xbar
    refine ⟨n, a.comp S.mkQ, g, ?_, ?_⟩
    · calc
        x = xbar.comp S.mkQ := by
          dsimp [xbar]
          exact (S.liftQ_mkQ x hS).symm
        _ = (g.comp a).comp S.mkQ := by rw [hag]
        _ = g.comp (a.comp S.mkQ) := by simp [LinearMap.comp_assoc]
    · have hfQ : S.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        dsimp [S]
        exact Submodule.subset_span (by simp)
      change a (S.mkQ f) = 0
      simpa using congrArg a hfQ

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
    let : Module.Flat R M := h
    intro φ
    obtain ⟨n, h', g, hφ⟩ :=
      Module.Flat.exists_factorization_of_finitePresentation φ
    obtain ⟨g', hg'⟩ := Module.projective_lifting_property q g hq
    refine ⟨g'.comp h', ?_⟩
    ext x
    simp [LinearMap.comp_apply,
      ← LinearMap.congr_fun hg' (h' x), hφ]
  · intro h
    apply Module.Flat.of_forall_exists_factorization
    intro l f x hx
    let S : Submodule R (Fin l →₀ R) := Submodule.span R ({f} : Set (Fin l →₀ R))
    let Q : Type u := (Fin l →₀ R) ⧸ S
    have hfree : Module.FinitePresentation R (Fin l →₀ R) := inferInstance
    let : Module.FinitePresentation R Q :=
      Module.finitePresentation_of_surjective (h := hfree) S.mkQ S.mkQ_surjective
        (by
          rw [Submodule.ker_mkQ]
          dsimp [S]
          exact Submodule.fg_span (Set.finite_singleton f))
    have hS : S ≤ LinearMap.ker x := by
      dsimp [S]
      refine Submodule.span_le.2 ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact LinearMap.mem_ker.mpr hx
    let xbar : Q →ₗ[R] M := S.liftQ x hS
    let N : Type (max u v) := M →₀ R
    let q : N →ₗ[R] M := Finsupp.linearCombination R (id : M → M)
    have hq : Function.Surjective q := by
      dsimp [q, N]
      simpa using (Finsupp.linearCombination_id_surjective R M)
    have hpost : Function.Surjective (internalHomPostcomp (M := Q) q) :=
      h Q N q hq
    obtain ⟨b, hb⟩ := hpost xbar
    classical
    let B := LinearMap.range b
    let : Module.Finite R B := Module.Finite.range b
    obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite R B)
    let T : Finset M := s.biUnion (fun z : B => z.1.support)
    let S' : Set N := (fun z : B => (z : N)) '' (↑s : Set B)
    have hS' : Submodule.span R S' ≤ Finsupp.supported R R (T : Set M) := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨z', hz', rfl⟩
      change (z' : N) ∈ Finsupp.supported R R (T : Set M)
      rw [Finsupp.mem_supported]
      intro m hm
      refine Finset.mem_biUnion.mpr ⟨z', ?_, hm⟩
      simpa using hz'
    have hrange : ∀ q₀ : Q, b q₀ ∈ Submodule.span R S' := by
      intro q₀
      let z : B := ⟨b q₀, LinearMap.mem_range_self b q₀⟩
      have hz : z ∈ Submodule.span R (↑s : Set B) := by
        rw [hs]
        exact Submodule.mem_top
      have hz' : (z : N) ∈
          Submodule.map (Submodule.subtype B) (Submodule.span R (↑s : Set B)) := by
        exact ⟨z, hz, rfl⟩
      rw [Submodule.map_span] at hz'
      simpa [S', z] using hz'
    have hbsupp : ∀ q₀ : Q, b q₀ ∈ Finsupp.supported R R (T : Set M) := by
      intro q₀
      exact hS' (hrange q₀)
    let c : Q →ₗ[R] Finsupp.supported R R (T : Set M) :=
      b.codRestrict _ hbsupp
    let e := Finsupp.supportedEquivFinsupp (M := R) (R := R) (T : Set M)
    let aQ : Q →ₗ[R] (T →₀ R) := e.toLinearMap.comp c
    let gQ : (T →₀ R) →ₗ[R] N :=
      (Submodule.subtype _).comp e.symm.toLinearMap
    have hga : gQ.comp aQ = b := by
      ext q₀
      simp [gQ, aQ, c, e]
    let k := Fintype.card T
    let eT : T ≃ Fin k := Fintype.equivFin T
    let d : (Fin k →₀ R) ≃ₗ[R] (T →₀ R) :=
      Finsupp.domLCongr eT.symm
    let aQ' : Q →ₗ[R] (Fin k →₀ R) := d.symm.toLinearMap.comp aQ
    let gQ' : (Fin k →₀ R) →ₗ[R] N := gQ.comp d.toLinearMap
    have hga' : gQ'.comp aQ' = b := by
      apply LinearMap.ext
      intro q₀
      change gQ (d (d.symm (aQ q₀))) = b q₀
      rw [d.apply_symm_apply]
      exact LinearMap.congr_fun hga q₀
    have hb' : q.comp b = xbar := by
      apply LinearMap.ext
      intro q₀
      simpa [internalHomPostcomp_apply] using
        congrArg (fun k : Q →ₗ[R] M => k q₀) hb
    have hfQ : S.mkQ f = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      dsimp [S]
      exact Submodule.subset_span (by simp)
    refine ⟨k, aQ'.comp S.mkQ, q.comp gQ', ?_, ?_⟩
    · calc
        x = xbar.comp S.mkQ := by
          dsimp [xbar]
          exact (S.liftQ_mkQ x hS).symm
        _ = (q.comp b).comp S.mkQ := by rw [hb']
        _ = (q.comp (gQ'.comp aQ')).comp S.mkQ := by rw [hga']
        _ = (q.comp gQ').comp (aQ'.comp S.mkQ) := by simp [LinearMap.comp_assoc]
    · change aQ' (S.mkQ f) = 0
      simpa using congrArg aQ' hfQ

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

private structure StandardFiniteFreeFactorization
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] where
  rank : ℕ
  factor : (Fin rank →₀ R) →ₗ[R] ULift.{u} M

private structure StandardFiniteFreeFactorization.Hom
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (A B : StandardFiniteFreeFactorization (R := R) (M := M)) where
  hom : (Fin A.rank →₀ R) →ₗ[R] (Fin B.rank →₀ R)
  comm : B.factor.comp hom = A.factor
  lift : ULift.{max u v} (Fin 1)

private theorem StandardFiniteFreeFactorization.Hom.ext
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    {A B : StandardFiniteFreeFactorization (R := R) (M := M)}
    {f g : StandardFiniteFreeFactorization.Hom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  congr
  apply ULift.ext
  exact Subsingleton.elim _ _

private def standardFiniteFreeHomMk
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    {A B : StandardFiniteFreeFactorization (R := R) (M := M)}
    (f : (Fin A.rank →₀ R) →ₗ[R] (Fin B.rank →₀ R))
    (h : B.factor.comp f = A.factor) :
    StandardFiniteFreeFactorization.Hom A B :=
  ⟨f, h, ⟨0⟩⟩

private def standardFiniteFreePointFactor
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (x : ULift.{u} M) :
    (Fin 1 →₀ R) →ₗ[R] ULift.{u} M :=
  { toFun := fun z => z 0 • x
    map_add' := by intro a b; simp [add_smul]
    map_smul' := by intro r a; simp [smul_smul] }

private noncomputable instance standardFiniteFreeFactorizationCategory
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    SmallCategory (StandardFiniteFreeFactorization (R := R) (M := M)) where
  Hom A B := StandardFiniteFreeFactorization.Hom (R := R) (M := M) A B
  id A := by
    change StandardFiniteFreeFactorization.Hom (R := R) (M := M) A A
    refine ⟨LinearMap.id, ?_, ⟨0⟩⟩
    apply LinearMap.ext
    intro x
    simp
  comp f g := by
    change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f g
    refine ⟨g.hom.comp f.hom, ?_, ⟨0⟩⟩
    rw [← LinearMap.comp_assoc, g.comm, f.comm]
  id_comp f := by
    change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f
    apply StandardFiniteFreeFactorization.Hom.ext
    simp
  comp_id f := by
    change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f
    apply StandardFiniteFreeFactorization.Hom.ext
    simp
  assoc f g h := by
    change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f g h
    apply StandardFiniteFreeFactorization.Hom.ext
    simp [LinearMap.comp_assoc]

private noncomputable def standardFiniteFreeLiftMap
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    {A B : StandardFiniteFreeFactorization (R := R) (M := M)}
    (f : StandardFiniteFreeFactorization.Hom A B) :
    ULift.{max u v} (Fin A.rank →₀ R) →ₗ[R]
      ULift.{max u v} (Fin B.rank →₀ R) :=
  (ULift.moduleEquiv.symm.toLinearMap).comp
    (f.hom.comp ULift.moduleEquiv.toLinearMap)

private noncomputable def standardFiniteFreeCoconeLeg
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (A : StandardFiniteFreeFactorization (R := R) (M := M)) :
    ULift.{max u v} (Fin A.rank →₀ R) →ₗ[R] ULift.{u} M :=
  A.factor.comp ULift.moduleEquiv.toLinearMap

private noncomputable def standardFiniteFreeFactorizationDiagram
  {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    StandardFiniteFreeFactorization (R := R) (M := M) ⥤ ModuleCat.{max u v} R :=
  { obj := fun A => ModuleCat.of R (ULift.{max u v} (Fin A.rank →₀ R))
    map := fun f => by
      change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f
      exact ModuleCat.ofHom (standardFiniteFreeLiftMap f)
    map_id := by
      intro A
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (ULift.down x) = x
      exact ULift.up_down x
    map_comp := by
      intro A B C f g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [standardFiniteFreeLiftMap, standardFiniteFreeFactorizationCategory,
        LinearMap.comp_apply]
      change g.hom (f.hom x.down) = g.hom (f.hom x.down)
      rfl }

private noncomputable def standardFiniteFreeFactorizationCocone
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Cocone (standardFiniteFreeFactorizationDiagram (R := R) (M := M)) :=
  { pt := ModuleCat.of R (ULift.{u} M)
    ι := { app := fun A => ModuleCat.ofHom (standardFiniteFreeCoconeLeg A)
           naturality := by
             intro A B f
             apply ModuleCat.hom_ext
             apply LinearMap.ext
             intro x
             change StandardFiniteFreeFactorization.Hom (R := R) (M := M) _ _ at f
             let eA : ULift.{max u v} (Fin A.rank →₀ R) ≃ₗ[R] Fin A.rank →₀ R :=
               ULift.moduleEquiv
             let eB : ULift.{max u v} (Fin B.rank →₀ R) ≃ₗ[R] Fin B.rank →₀ R :=
               ULift.moduleEquiv
             change B.factor (eB (eB.symm (f.hom (eA x)))) = A.factor (eA x)
             rw [eB.apply_symm_apply]
             exact congrArg (fun q : (Fin A.rank →₀ R) →ₗ[R] ULift.{u} M => q (eA x)) f.comm } }

private def finiteFreeProperty {R : Type u} [CommRing R] :
    ObjectProperty (ModuleCat.{max u v} R) :=
  fun X => Module.Free R X ∧ Module.Finite R X

private theorem finiteFreeFactorization_filtered
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (h : Module.Flat R M) :
    IsFiltered
      (CostructuredArrow (finiteFreeProperty (R := R)).ι
        (ModuleCat.of R (ULift.{u} M))) := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := finiteFreeProperty (R := R)
  let D : P.FullSubcategory ⥤ ModuleCat.{max u v} R := P.ι
  let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)
  let : Module.Flat R M := h
  let : Module.Flat R (ULift.{u} M) := inferInstance
  let : IsFilteredOrEmpty
      (CostructuredArrow D X) := by
    refine {
      cocone_objs := ?_
      cocone_maps := ?_ }
    · intro f g
      let : Module.Free R (D.obj f.left) := f.left.property.1
      let : Module.Finite R (D.obj f.left) := f.left.property.2
      let : Module.Free R (D.obj g.left) := g.left.property.1
      let : Module.Finite R (D.obj g.left) := g.left.property.2
      let A : Type (max u v) := D.obj f.left
      let B : Type (max u v) := D.obj g.left
      let : Module.Free R A := f.left.property.1
      let : Module.Finite R A := f.left.property.2
      let : Module.Free R B := g.left.property.1
      let : Module.Finite R B := g.left.property.2
      let Z : P.FullSubcategory :=
        { obj := ModuleCat.of R (A × B)
          property := by
            exact ⟨Module.Free.prod R A B, Module.Finite.prod⟩ }
      let q : D.obj Z ⟶ X := ModuleCat.ofHom
        (LinearMap.coprod f.hom.hom g.hom.hom)
      let z : CostructuredArrow D X := CostructuredArrow.mk q
      let left : f ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom (LinearMap.inl R A B)))
      let right : g ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom (LinearMap.inr R A B)))
      refine ⟨z, left, right, trivial⟩
    · intro f g φ ψ
      let : Module.Free R (D.obj f.left) := f.left.property.1
      let : Module.Finite R (D.obj f.left) := f.left.property.2
      let : Module.Free R (D.obj g.left) := g.left.property.1
      let : Module.Finite R (D.obj g.left) := g.left.property.2
      let : Module.Finite R (f.left.obj : Type (max u v)) := f.left.property.2
      let : Module.Finite R (g.left.obj : Type (max u v)) := g.left.property.2
      have hcomp : g.hom.hom.comp (φ.left.hom.hom - ψ.left.hom.hom) = 0 := by
        have hφ := congrArg ModuleCat.Hom.hom (CostructuredArrow.w φ)
        have hψ := congrArg ModuleCat.Hom.hom (CostructuredArrow.w ψ)
        change g.hom.hom.comp φ.left.hom.hom = f.hom.hom at hφ
        change g.hom.hom.comp ψ.left.hom.hom = f.hom.hom at hψ
        rw [LinearMap.comp_sub, hφ, hψ, sub_self]
      obtain ⟨k, a, b, hab, ha⟩ :=
        Module.Flat.exists_factorization_of_comp_eq_zero_of_free hcomp
      let Z : P.FullSubcategory :=
        { obj := ModuleCat.of R (ULift.{max u v} (Fin k →₀ R))
          property := by exact ⟨inferInstance, inferInstance⟩ }
      let e : ULift.{max u v} (Fin k →₀ R) ≃ₗ[R] (Fin k →₀ R) := ULift.moduleEquiv
      let a' : D.obj g.left →ₗ[R] ULift.{max u v} (Fin k →₀ R) :=
        { toFun := fun x => e.symm (a x)
          map_add' := by intro x y; simp
          map_smul' := by intro r x; simp }
      let b' : ULift.{max u v} (Fin k →₀ R) →ₗ[R] X :=
        { toFun := fun x => b (e x)
          map_add' := by intro x y; simp
          map_smul' := by intro r x; simp }
      let z : CostructuredArrow D X :=
        CostructuredArrow.mk (Y := Z) (ModuleCat.ofHom b' : D.obj Z ⟶ X)
      let t : g ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom a')) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change b (e (e.symm (a x))) = g.hom.hom x
          rw [e.apply_symm_apply]
          simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hab x).symm)
      refine ⟨z, t, ?_⟩
      apply CostructuredArrow.hom_ext
      apply P.hom_ext
      apply ModuleCat.hom_ext
      apply sub_eq_zero.mp
      apply LinearMap.ext
      intro x
      dsimp [t, a']
      change e.symm (a (φ.left.hom.hom x)) - e.symm (a (ψ.left.hom.hom x)) = 0
      have hx := congrArg (fun l => l x) ha
      simpa [LinearMap.comp_apply] using congrArg e.symm hx
  let eR : ULift.{max u v} R ≃ₗ[R] R := ULift.moduleEquiv
  let q0 : ULift.{max u v} R →ₗ[R] ULift.{u} M :=
    (LinearMap.toSpanSingleton R (ULift.{u} M) (0 : ULift.{u} M)).comp eR.toLinearMap
  let Y : P.FullSubcategory :=
    { obj := ModuleCat.of R (ULift.{max u v} R)
      property := by exact ⟨inferInstance, inferInstance⟩ }
  exact { nonempty := ⟨CostructuredArrow.mk
      (Y := Y) (ModuleCat.ofHom q0 : D.obj Y ⟶ X)⟩ }

private def finiteFreeFactorizationDiagram
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    CostructuredArrow (finiteFreeProperty (R := R)).ι (ModuleCat.of R (ULift.{u} M)) ⥤
      ModuleCat.{max u v} R :=
  CostructuredArrow.proj (finiteFreeProperty (R := R)).ι (ModuleCat.of R (ULift.{u} M)) ⋙
    (finiteFreeProperty (R := R)).ι

private def finiteFreeFactorizationCocone
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Cocone (finiteFreeFactorizationDiagram (R := R) (M := M)) := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := finiteFreeProperty (R := R)
  let D : P.FullSubcategory ⥤ ModuleCat.{max u v} R := P.ι
  let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)
  exact {
    pt := X
    ι := {
      app := fun f => f.hom
      naturality := by
        intro f g k
        exact CostructuredArrow.w k } }

private def finiteFreeFactorizationPoint
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (x : ModuleCat.of R (ULift.{u} M)) :
    CostructuredArrow (finiteFreeProperty (R := R)).ι
      (ModuleCat.of R (ULift.{u} M)) := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := finiteFreeProperty (R := R)
  let D : P.FullSubcategory ⥤ ModuleCat.{max u v} R := P.ι
  let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)
  let Y : P.FullSubcategory :=
    { obj := ModuleCat.of R (ULift.{max u v} R)
      property := by exact ⟨inferInstance, inferInstance⟩ }
  let eR : ULift.{max u v} R ≃ₗ[R] R := ULift.moduleEquiv
  exact CostructuredArrow.mk (Y := Y) (ModuleCat.ofHom
    ((LinearMap.toSpanSingleton R X x).comp eR.toLinearMap) : D.obj Y ⟶ X)

private def finiteFreeFactorizationDescLinear
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (t : Cocone (finiteFreeFactorizationDiagram (R := R) (M := M))) :
    ModuleCat.of R (ULift.{u} M) →ₗ[R] t.pt := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := finiteFreeProperty (R := R)
  let D : P.FullSubcategory ⥤ ModuleCat.{max u v} R := P.ι
  let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)
  let I := CostructuredArrow D X
  let Y : P.FullSubcategory :=
    { obj := ModuleCat.of R (ULift.{max u v} R)
      property := by exact ⟨inferInstance, inferInstance⟩ }
  let eR : ULift.{max u v} R ≃ₗ[R] R := ULift.moduleEquiv
  let point (x : X) : I := finiteFreeFactorizationPoint (R := R) (M := M) x
  let g : X →ₗ[R] t.pt := {
    toFun := fun x => (t.ι.app (point x)) (1 : ULift.{max u v} R)
    map_add' := by
      intro x y
      let Z : P.FullSubcategory :=
        { obj := ModuleCat.of R
            ((ULift.{max u v} R) × (ULift.{max u v} R))
          property := by
            exact ⟨Module.Free.prod R _ _, Module.Finite.prod⟩ }
      let q : D.obj Z ⟶ X := ModuleCat.ofHom
        (LinearMap.coprod (point x).hom.hom (point y).hom.hom)
      let z : I := CostructuredArrow.mk (Y := Z) q
      let d : ULift.{max u v} R →ₗ[R]
          (ULift.{max u v} R) × (ULift.{max u v} R) :=
        LinearMap.prod LinearMap.id LinearMap.id
      let k : point (x + y) ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom d)) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          dsimp [point, q, z, finiteFreeFactorizationPoint, d]
          change (eR r) • x + (eR r) • y = (eR r) • (x + y)
          simp [smul_add])
      let kx : point x ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom (LinearMap.inl R _ _))) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          change (LinearMap.coprod (point x).hom.hom (point y).hom.hom)
              (LinearMap.inl R _ _ r) =
            (point x).hom.hom r
          simp [LinearMap.coprod_apply])
      let ky : point y ⟶ z := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom (LinearMap.inr R _ _))) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          change (LinearMap.coprod (point x).hom.hom (point y).hom.hom)
              (LinearMap.inr R _ _ r) =
            (point y).hom.hom r
          simp [LinearMap.coprod_apply])
      have hk := congrArg (fun m => m (1 : ULift.{max u v} R))
        (congrArg ModuleCat.Hom.hom (t.ι.naturality k))
      dsimp [k, point, finiteFreeFactorizationPoint,
        finiteFreeFactorizationDiagram] at hk
      have hkx := congrArg (fun m => m (1 : ULift.{max u v} R))
        (congrArg ModuleCat.Hom.hom (t.ι.naturality kx))
      have hky := congrArg (fun m => m (1 : ULift.{max u v} R))
        (congrArg ModuleCat.Hom.hom (t.ι.naturality ky))
      change (ConcreteCategory.hom (t.ι.app z))
          ((1 : ULift.{max u v} R), (1 : ULift.{max u v} R)) =
        (ConcreteCategory.hom (t.ι.app (point (x + y))))
          (1 : ULift.{max u v} R) at hk
      change (ConcreteCategory.hom (t.ι.app z))
          ((1 : ULift.{max u v} R), (0 : ULift.{max u v} R)) =
        (ConcreteCategory.hom (t.ι.app (point x)))
          (1 : ULift.{max u v} R) at hkx
      change (ConcreteCategory.hom (t.ι.app z))
          ((0 : ULift.{max u v} R), (1 : ULift.{max u v} R)) =
        (ConcreteCategory.hom (t.ι.app (point y)))
          (1 : ULift.{max u v} R) at hky
      have hsum :
          (ConcreteCategory.hom (t.ι.app z))
              ((1 : ULift.{max u v} R), (1 : ULift.{max u v} R)) =
            (ConcreteCategory.hom (t.ι.app z))
                ((1 : ULift.{max u v} R), (0 : ULift.{max u v} R)) +
              (ConcreteCategory.hom (t.ι.app z))
                ((0 : ULift.{max u v} R), (1 : ULift.{max u v} R)) := by
        calc
          (ConcreteCategory.hom (t.ι.app z))
                ((1 : ULift.{max u v} R), (1 : ULift.{max u v} R)) =
              (ConcreteCategory.hom (t.ι.app z))
                (((1 : ULift.{max u v} R), (0 : ULift.{max u v} R)) +
                  ((0 : ULift.{max u v} R), (1 : ULift.{max u v} R))) := by
                congr 1
                apply Prod.ext <;> simp
          _ = (ConcreteCategory.hom (t.ι.app z))
                ((1 : ULift.{max u v} R), (0 : ULift.{max u v} R)) +
              (ConcreteCategory.hom (t.ι.app z))
                ((0 : ULift.{max u v} R), (1 : ULift.{max u v} R)) :=
            (ConcreteCategory.hom (t.ι.app z)).map_add _ _
      rw [← hkx, ← hky]
      exact hk.symm.trans hsum
    map_smul' := by
      intro r x
      let m : ULift.{max u v} R →ₗ[R] ULift.{max u v} R :=
        { toFun := fun a => eR.symm (r * eR a)
          map_add' := by intro a b; simp [mul_add]
          map_smul' := by
            intro s a
            rw [← eR.symm.map_smul, smul_eq_mul]
            simp [mul_assoc, mul_comm, mul_left_comm] }
      let k : point (r • x) ⟶ point x := CostructuredArrow.homMk
        (P.homMk (ModuleCat.ofHom m)) (by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro a
          dsimp [point, finiteFreeFactorizationPoint] at a ⊢
          change (eR (m a)) • x = (eR a) • (r • x)
          rw [smul_smul]
          simp [m, mul_comm])
      have hk := congrArg (fun m => m (1 : ULift.{max u v} R))
        (congrArg ModuleCat.Hom.hom (t.ι.naturality k))
      have hr : eR.symm r = r • (1 : ULift.{max u v} R) := by
        apply eR.injective
        simp [eR]
      have hkm : (ConcreteCategory.hom (finiteFreeFactorizationDiagram.map k))
          (1 : ULift.{max u v} R) = eR.symm r := by
        dsimp [finiteFreeFactorizationDiagram, k]
        change m (1 : ULift.{max u v} R) = eR.symm r
        simp [m, eR]
      simp only [ModuleCat.hom_comp, Functor.const_obj_map] at hk
      change (ConcreteCategory.hom (t.ι.app (point x)))
          ((ConcreteCategory.hom (finiteFreeFactorizationDiagram.map k))
            (1 : ULift.{max u v} R)) =
        (ConcreteCategory.hom (t.ι.app (point (r • x))))
          (1 : ULift.{max u v} R) at hk
      rw [hkm] at hk
      calc
        (ConcreteCategory.hom (t.ι.app (point (r • x))))
              (1 : ULift.{max u v} R) =
            (ConcreteCategory.hom (t.ι.app (point x))) (eR.symm r) := hk.symm
        _ = (ConcreteCategory.hom (t.ι.app (point x)))
              (r • (1 : ULift.{max u v} R)) := by rw [hr]
        _ = r • (ConcreteCategory.hom (t.ι.app (point x)))
              (1 : ULift.{max u v} R) := by
          change (ConcreteCategory.hom
              (t.ι.app (finiteFreeFactorizationPoint (R := R) (M := M) x)))
                (r • (1 : ULift.{max u v} R)) =
            r • (ConcreteCategory.hom
              (t.ι.app (finiteFreeFactorizationPoint (R := R) (M := M) x)))
                (1 : ULift.{max u v} R)
          exact (ConcreteCategory.hom
            (t.ι.app (finiteFreeFactorizationPoint (R := R) (M := M) x))).map_smul
            r (1 : ULift.{max u v} R) }
  exact g

private def finiteFreeFactorization_isColimit
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    IsColimit (finiteFreeFactorizationCocone (R := R) (M := M)) := by
  let P : ObjectProperty (ModuleCat.{max u v} R) := finiteFreeProperty (R := R)
  let D : P.FullSubcategory ⥤ ModuleCat.{max u v} R := P.ι
  let X : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{u} M)
  let I := CostructuredArrow D X
  let c := finiteFreeFactorizationCocone (R := R) (M := M)
  change IsColimit c
  let eR : ULift.{max u v} R ≃ₗ[R] R := ULift.moduleEquiv
  let point (x : X) : I := finiteFreeFactorizationPoint (R := R) (M := M) x
  refine {
    desc := fun t => ?_
    fac := ?_
    uniq := ?_ }
  · exact ModuleCat.ofHom
      (finiteFreeFactorizationDescLinear (R := R) (M := M) t)
  · intro t j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let p : ULift.{max u v} R →ₗ[R] D.obj j.left :=
      (LinearMap.toSpanSingleton R (D.obj j.left) x).comp eR.toLinearMap
    let k : point (j.hom.hom x) ⟶ j := CostructuredArrow.homMk
      (P.homMk (ModuleCat.ofHom p)) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        dsimp [point, finiteFreeFactorizationPoint] at r ⊢
        change (j.hom.hom) (p r) =
          (LinearMap.toSpanSingleton R (ULift.{u} M) (j.hom.hom x)).comp
            eR.toLinearMap r
        change (j.hom.hom) ((eR r) • x) = (eR r) • (j.hom.hom x)
        exact (j.hom.hom).map_smul (eR r) x)
    have hk := congrArg (fun m => m (1 : ULift.{max u v} R))
      (congrArg ModuleCat.Hom.hom (t.ι.naturality k))
    dsimp [finiteFreeFactorizationDiagram, CostructuredArrow.proj, D, P] at x
    have hkp : (ConcreteCategory.hom (finiteFreeFactorizationDiagram.map k))
        (1 : ULift.{max u v} R) = x := by
      dsimp [k, p, point, finiteFreeFactorizationPoint,
        finiteFreeFactorizationDiagram]
      change p (1 : ULift.{max u v} R) = x
      dsimp [p]
      change (eR (1 : ULift.{max u v} R)) • x = x
      simp [eR]
    simp only [ModuleCat.hom_comp, Functor.const_obj_map] at hk
    change (ConcreteCategory.hom (t.ι.app j))
        ((ConcreteCategory.hom (finiteFreeFactorizationDiagram.map k))
          (1 : ULift.{max u v} R)) =
      (ConcreteCategory.hom
        (t.ι.app (point (j.hom.hom x))))
        (1 : ULift.{max u v} R) at hk
    rw [hkp] at hk
    change (ConcreteCategory.hom
        (t.ι.app (point (j.hom.hom x))))
        (1 : ULift.{max u v} R) =
      (ConcreteCategory.hom (t.ι.app j)) x
    exact hk.symm
  · intro t f hf
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let k := point x
    change ULift.{u} M at x
    have hk := congrArg (fun m => m (1 : ULift.{max u v} R))
      (congrArg ModuleCat.Hom.hom (hf k))
    have hcp : (ConcreteCategory.hom (c.ι.app k))
        (1 : ULift.{max u v} R) = x := by
      change (LinearMap.toSpanSingleton R (ULift.{u} M) x).comp
          eR.toLinearMap (1 : ULift.{max u v} R) = x
      change (eR (1 : ULift.{max u v} R)) • x = x
      simp [eR]
    simp only [ModuleCat.hom_comp] at hk
    change (ConcreteCategory.hom f)
        ((ConcreteCategory.hom (c.ι.app k)) (1 : ULift.{max u v} R)) =
      (ConcreteCategory.hom (t.ι.app k)) (1 : ULift.{max u v} R) at hk
    rw [hcp] at hk
    change (ConcreteCategory.hom f) x =
      (ConcreteCategory.hom (t.ι.app (point x))) (1 : ULift.{max u v} R)
    exact hk

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
  sorry
/-
  constructor
  · intro h
    classical
    let J := StandardFiniteFreeFactorization (R := R) (M := M)
    let : IsFiltered J := by
      let : Module.Flat R (ULift.{u} M) := inferInstance
      refine {
        nonempty := ⟨{ rank := 0, factor := 0 }⟩
        cocone_objs := ?_
        cocone_maps := ?_ }
      · intro A B
        let e : (Fin (A.rank + B.rank) →₀ R) ≃ₗ[R]
            (Fin A.rank →₀ R) × (Fin B.rank →₀ R) :=
          (Finsupp.domLCongr (finSumFinEquiv (m := A.rank) (n := B.rank)).symm).trans
            (Finsupp.sumFinsuppLEquivProdFinsupp R)
        let q : (Fin (A.rank + B.rank) →₀ R) →ₗ[R] ULift.{u} M :=
          (LinearMap.coprod A.factor B.factor).comp e.toLinearMap
        let C : J := { rank := A.rank + B.rank, factor := q }
        let l : (Fin A.rank →₀ R) →ₗ[R] (Fin C.rank →₀ R) :=
          e.symm.toLinearMap.comp (LinearMap.inl R _ _)
        let r : (Fin B.rank →₀ R) →ₗ[R] (Fin C.rank →₀ R) :=
          e.symm.toLinearMap.comp (LinearMap.inr R _ _)
        have hl : C.factor.comp l = A.factor := by
          apply LinearMap.ext
          intro x
          change (LinearMap.coprod A.factor B.factor) (e (e.symm (x, 0))) = A.factor x
          simp
        have hr : C.factor.comp r = B.factor := by
          apply LinearMap.ext
          intro x
          change (LinearMap.coprod A.factor B.factor) (e (e.symm (0, x))) = B.factor x
          simp
        exact ⟨C, standardFiniteFreeHomMk l hl, standardFiniteFreeHomMk r hr, trivial⟩
      · intro A B f g
        have hcomp : B.factor.comp (f.hom - g.hom) = 0 := by
          apply LinearMap.ext
          intro x
          have hf := congrArg (fun q => q x) f.comm
          have hg := congrArg (fun q => q x) g.comm
          calc
            B.factor ((f.hom - g.hom) x) =
                B.factor (f.hom x) - B.factor (g.hom x) := by
              rw [LinearMap.sub_apply, map_sub]
            _ = 0 := by
              have hf' : B.factor (f.hom x) = A.factor x := by
                simpa [LinearMap.comp_apply] using hf
              have hg' : B.factor (g.hom x) = A.factor x := by
                simpa [LinearMap.comp_apply] using hg
              rw [hf', hg', sub_self]
            _ = (0 : (Fin A.rank →₀ R) →ₗ[R] ULift.{u} M) x := by simp
        obtain ⟨k, a, b, hab, ha⟩ :=
          Module.Flat.exists_factorization_of_comp_eq_zero_of_free hcomp
        let C : J := { rank := k, factor := b }
        let t : StandardFiniteFreeFactorization.Hom B C :=
          standardFiniteFreeHomMk a hab.symm
        refine ⟨C, t, ?_⟩
        apply StandardFiniteFreeFactorization.Hom.ext
        change a.comp f.hom = a.comp g.hom
        apply LinearMap.ext
        intro x
        apply sub_eq_zero.mp
        have hx := congrArg (fun q => q x) ha
        simpa [LinearMap.comp_apply] using hx
    let K := standardFiniteFreeFactorizationDiagram (R := R) (M := M)
    let cTarget := standardFiniteFreeFactorizationCocone (R := R) (M := M)
    have hType : IsColimit ((forget (ModuleCat.{max u v} R)).mapCocone cTarget) := by
      apply Types.FilteredColimit.isColimitOf
        (K ⋙ forget (ModuleCat.{max u v} R))
        ((forget (ModuleCat.{max u v} R)).mapCocone cTarget)
      · intro x
        let A : J := {
          rank := 1
          factor := standardFiniteFreePointFactor x }
        refine ⟨A, ULift.up (Finsupp.single (0 : Fin 1) (1 : R)), ?_⟩
        change A.factor (Finsupp.single 0 1) = x
        simp [A]
      · intro A B x y hxy
        let e : (Fin (A.rank + B.rank) →₀ R) ≃ₗ[R]
            (Fin A.rank →₀ R) × (Fin B.rank →₀ R) :=
          (Finsupp.domLCongr (finSumFinEquiv (m := A.rank) (n := B.rank)).symm).trans
            (Finsupp.sumFinsuppLEquivProdFinsupp R)
        let q : (Fin (A.rank + B.rank) →₀ R) →ₗ[R] ULift.{u} M :=
          (LinearMap.coprod A.factor B.factor).comp e.toLinearMap
        let C : J := { rank := A.rank + B.rank, factor := q }
        let l : (Fin A.rank →₀ R) →ₗ[R] (Fin C.rank →₀ R) :=
          e.symm.toLinearMap.comp (LinearMap.inl R _ _)
        let r : (Fin B.rank →₀ R) →ₗ[R] (Fin C.rank →₀ R) :=
          e.symm.toLinearMap.comp (LinearMap.inr R _ _)
        have hl : C.factor.comp l = A.factor := by
          apply LinearMap.ext
          intro z
          change (LinearMap.coprod A.factor B.factor) (e (e.symm (z, 0))) = A.factor z
          simp
        have hr : C.factor.comp r = B.factor := by
          apply LinearMap.ext
          intro z
          change (LinearMap.coprod A.factor B.factor) (e (e.symm (0, z))) = B.factor z
          simp
        refine ⟨C, standardFiniteFreeHomMk l hl, standardFiniteFreeHomMk r hr, ?_⟩
        let eA : ULift.{max u v} (Fin A.rank →₀ R) ≃ₗ[R] Fin A.rank →₀ R :=
          ULift.moduleEquiv
        let eB : ULift.{max u v} (Fin B.rank →₀ R) ≃ₗ[R] Fin B.rank →₀ R :=
          ULift.moduleEquiv
        let eC : ULift.{max u v} (Fin C.rank →₀ R) ≃ₗ[R] Fin C.rank →₀ R :=
          ULift.moduleEquiv
        dsimp [K, standardFiniteFreeFactorizationDiagram,
          standardFiniteFreeLiftMap, standardFiniteFreeHomMk]
        change C.factor (eC (eC.symm (l (eA x)))) =
          C.factor (eC (eC.symm (r (eB y))))
        rw [eC.apply_symm_apply, eC.apply_symm_apply]
        calc
          C.factor (l (eA x)) = A.factor (eA x) := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun q => q (eA x)) hl
          _ = B.factor (eB y) := hxy
          _ = C.factor (r (eB y)) := by
            symm
            simpa [LinearMap.comp_apply] using
              congrArg (fun q => q (eB y)) hr
    let c₀ := ModuleCat.FilteredColimits.colimitCocone K
    let hc₀ := ModuleCat.FilteredColimits.colimitCoconeIsColimit K
    let phi : c₀.pt ⟶ cTarget.pt :=
      ModuleCat.FilteredColimits.colimitDesc K cTarget
    have hphi_bij : Function.Bijective phi.hom := by
      constructor
      · intro a b hab
        obtain ⟨i, x, hia⟩ := ModuleCat.FilteredColimits.M.mk_surjective K a
        obtain ⟨j, y, hjb⟩ := ModuleCat.FilteredColimits.M.mk_surjective K b
        have hia' : (c₀.ι.app i).hom x = a := by
          simpa [c₀, ModuleCat.FilteredColimits.coconeMorphism,
            ModuleCat.FilteredColimits.M.mk] using hia
        have hjb' : (c₀.ι.app j).hom y = b := by
          simpa [c₀, ModuleCat.FilteredColimits.coconeMorphism,
            ModuleCat.FilteredColimits.M.mk] using hjb
        have hab' : (cTarget.ι.app i).hom x = (cTarget.ι.app j).hom y := by
          calc
            (cTarget.ι.app i).hom x = phi.hom ((c₀.ι.app i).hom x) := by
              symm
              simpa [phi] using congrArg (fun q => q x)
                (congrArg ModuleCat.Hom.hom (hc₀.fac cTarget i))
            _ = phi.hom ((c₀.ι.app j).hom y) := hab
            _ = (cTarget.ι.app j).hom y := by
              simpa [phi] using congrArg (fun q => q y)
                (congrArg ModuleCat.Hom.hom (hc₀.fac cTarget j))
        obtain ⟨k, f, g, hfg⟩ :=
          (Types.FilteredColimit.isColimit_eq_iff
            (K ⋙ forget (ModuleCat.{max u v} R)) hType).mp hab'
        rw [← hia', ← hjb']
        calc
          (c₀.ι.app i).hom x = (c₀.ι.app k).hom ((K.map f).hom x) := by
            simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
              (congrArg (fun q => q x)
                (congrArg ModuleCat.Hom.hom (c₀.ι.naturality f))).symm
          _ = (c₀.ι.app k).hom ((K.map g).hom y) := by rw [hfg]
          _ = (c₀.ι.app j).hom y := by
            simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
              congrArg (fun q => q y)
                (congrArg ModuleCat.Hom.hom (c₀.ι.naturality g))
      · intro y
        let A : J := {
          rank := 1
          factor := standardFiniteFreePointFactor y }
        refine ⟨(c₀.ι.app A).hom
          (ULift.up (Finsupp.single (0 : Fin 1) (1 : R))), ?_⟩
        simpa [phi, c₀] using congrArg (fun q => q
          (ULift.up (Finsupp.single (0 : Fin 1) (1 : R))))
          (congrArg ModuleCat.Hom.hom (hc₀.fac cTarget A))
    let phiIso : c₀.pt ≃ₗ[R] ULift.{u} M :=
      LinearEquiv.ofBijective phi.hom hphi_bij
    obtain ⟨α, hαorder, hαdirected, hαnonempty, F₀, hF₀⟩ :=
      IsFiltered.exists_directed J
    let : PartialOrder α := hαorder
    let : IsDirectedOrder α := hαdirected
    let : Nonempty α := hαnonempty
    let F : α ⥤ J := F₀
    let : F.Final := hF₀
    let G : α ⥤ ModuleCat.{max u v} R := F ⋙ K
    let stage : α → Type (max u v) := fun i => G.obj i
    let map : ∀ i j, i ≤ j → stage i →ₗ[R] stage j :=
      fun i j hij => (G.map (homOfLE hij)).hom
    let : ∀ i, AddCommGroup (stage i) := fun i => inferInstance
    let : ∀ i, Module R (stage i) := fun i => inferInstance
    let : DirectedSystem stage (map · · ·) := by
      constructor
      · intro i x
        change (G.map (homOfLE (le_refl i))).hom x = x
        simp [G, map]
      · intro i j k hij hjk x
        change (G.map (homOfLE hjk)).hom ((G.map (homOfLE hij)).hom x) =
          (G.map (homOfLE (hij.trans hjk))).hom x
        simpa [G, map, ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun q => q.hom x)
            (G.map_comp (homOfLE hij) (homOfLE hjk)).symm
    let c : Cocone G := {
      pt := c₀.pt
      ι := F.whiskerLeft c₀.ι }
    have hc : IsColimit c := by
      dsimp [c, G]
      exact (Functor.Final.isColimitWhiskerEquiv F c₀).symm hc₀
    let g : ∀ i, stage i →ₗ[R] (c₀.pt : Type (max u v)) :=
      fun i => (c.ι.app i).hom
    have hg : ∀ i j (hij : i ≤ j) (x : stage i),
        g j (map i j hij x) = g i x := by
      intro i j hij x
      have hn := congrArg ModuleCat.Hom.hom (c.ι.naturality (homOfLE hij))
      change (c.ι.app j).hom ((G.map (homOfLE hij)).hom x) = (c.ι.app i).hom x
      simpa [ModuleCat.hom_comp, Functor.const_obj_map] using
        congrArg (fun q => q x) hn
    let desc : DirectLimit stage map →ₗ[R] (c₀.pt : Type (max u v)) :=
      DirectLimit.Module.lift R α stage map g hg
    let d : Cocone G := {
      pt := ModuleCat.of R (DirectLimit stage map)
      ι := {
        app := fun i => ModuleCat.ofHom (DirectLimit.Module.of R α stage map i)
        naturality := by
          intro i j hij
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          have hh : hij = homOfLE hij.le := Subsingleton.elim _ _
          rw [hh]
          change DirectLimit.Module.of R α stage map j ((map i j hij.le) x) =
            DirectLimit.Module.of R α stage map i x
          simpa using
            (DirectLimit.Module.of_f (R := R) (ι := α) (G := stage) (f := map)
              (hij := hij.le) (x := x))
        } }
    let inv : (c₀.pt : Type (max u v)) →ₗ[R] DirectLimit stage map := (hc.desc d).hom
    have hleft : desc.comp inv = LinearMap.id := by
      have hcomp : hc.desc d ≫ ModuleCat.ofHom desc = 𝟙 c.pt := by
        apply hc.hom_ext
        intro i
        rw [← Category.assoc, hc.fac, Category.comp_id]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp [d, desc, g]
      simpa [inv, ModuleCat.hom_comp] using congrArg ModuleCat.Hom.hom hcomp
    have hright : inv.comp desc = LinearMap.id := by
      apply DirectLimit.Module.hom_ext
      intro i
      apply LinearMap.ext
      intro x
      have hi := congrArg ModuleCat.Hom.hom (hc.fac d i)
      change (hc.desc d).hom ((c.ι.app i).hom x) =
        DirectLimit.Module.of R α stage map i x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using congrArg (fun q => q x) hi
    refine ⟨{
      index := α
      stage := stage
      map := map
      free := fun i => by
        dsimp [stage, G, K, standardFiniteFreeFactorizationDiagram]
        exact Module.Free.of_equiv (ULift.moduleEquiv.symm)
      finite := fun i => by
        dsimp [stage, G, K, standardFiniteFreeFactorizationDiagram]
        exact Module.Finite.equiv (ULift.moduleEquiv.symm)
      targetIso := ⟨((LinearEquiv.ofLinear desc inv hleft hright).trans phiIso).trans
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M)⟩ }⟩
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
      s.targetIso.some.symm -/

end Formalization.Books.Algebra.Unit81
