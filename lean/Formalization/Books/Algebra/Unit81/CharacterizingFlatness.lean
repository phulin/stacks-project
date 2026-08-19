import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit11.CharacterizingFinite
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
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
