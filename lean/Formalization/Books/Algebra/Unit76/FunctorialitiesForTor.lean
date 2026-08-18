import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 76: Functorialities for Tor

This file records the change-of-rings and filtered-colimit interfaces for the
Tor construction from Chapter 75.  Restriction and extension of scalars are
Mathlib's canonical `ModuleCat` functors.  The source's naturality assertions
are retained as fields of one change-of-rings datum; flat base change remains
a separate theorem.
-/

namespace Formalization.Books.Algebra.Unit76

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Algebra.Unit75

noncomputable section

universe u

/-! ## Change of rings -/

/-- The `R`-module obtained by restricting an `R'`-module along `f`. -/
noncomputable abbrev restrictedModule {R R' : Type u} [Ring R] [Ring R']
    (f : R →+* R') (N' : ModuleCat.{u} R') : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars f).obj N'

/-- The extension-of-scalars module attached to `f` and an `R`-module. -/
noncomputable abbrev extendedModule {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) : ModuleCat.{u} R' :=
  (ModuleCat.extendScalars f).obj M

/-- The `R`-module in the first source item, using the restricted target module. -/
noncomputable abbrev restrictedTor {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    ModuleCat.{u} R :=
  Tor M (restrictedModule f N') i

/-- The Tor group after extending both module arguments to `R'`. -/
noncomputable abbrev extendedTor {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R' :=
  Tor (extendedModule f M) (extendedModule f N) i

/-- The Tor group after extending the first module argument to `R'`. -/
noncomputable abbrev mixedExtendedTor {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    ModuleCat.{u} R' :=
  Tor (extendedModule f M) N' i

/-! ## The target-scalar action -/

/-- The Tor endomorphism induced by multiplication by `s` on the target. -/
noncomputable def torTargetScalarMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) (s : R') :
    restrictedTor f M N' i ⟶ restrictedTor f M N' i :=
  torMapSecond M (restrictedModule f N') (restrictedModule f N')
    ((ModuleCat.restrictScalars f).map
      (ModuleCat.ofHom (LinearMap.lsmul R' N' s))) i

/-- An `R'`-module structure on `Tor_R(M,N')`, including its compatibility
with the pre-existing `R`-module structure and the target-scalar action. -/
structure TargetTorModule {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) where
  module : Module R' (restrictedTor f M N' i)
  smul_restricts : ∀ (r : R) (x : restrictedTor f M N' i),
    letI : Module R' (restrictedTor f M N' i) := module
    f r • x = r • x
  smul_eq_torMap : ∀ (s : R') (x : restrictedTor f M N' i),
    letI : Module R' (restrictedTor f M N' i) := module
    s • x = torTargetScalarMap f M N' i s x

private theorem torMapSecond_add {R : Type u} [CommRing R]
    (M N P : ModuleCat.{u} R) (φ ψ : N ⟶ P) (i : ℕ) :
    torMapSecond M N P (φ + ψ) i =
      torMapSecond M N P φ i + torMapSecond M N P ψ i := by
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  change chainHomologyMap (tensorComplexMapRight F.complex (φ + ψ)) i =
    chainHomologyMap (tensorComplexMapRight F.complex φ) i +
      chainHomologyMap (tensorComplexMapRight F.complex ψ) i
  have hmap : tensorComplexMapRight F.complex (φ + ψ) =
      tensorComplexMapRight F.complex φ + tensorComplexMapRight F.complex ψ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMapRight]
    rfl
  unfold chainHomologyMap
  rw [hmap, HomologicalComplex.homologyMap_add]
  rfl

private theorem torMapSecond_zero {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) :
    torMapSecond M N N 0 i = 0 := by
  apply add_right_cancel (b := 𝟙 (Tor M N i))
  have h := torMapSecond_add M N N (0 : N ⟶ N) (𝟙 N) i
  rw [zero_add, torMapSecond_id] at h
  simpa using h.symm

private theorem torMapSecond_smul {R : Type u} [CommRing R]
    (M N P : ModuleCat.{u} R) (r : R) (φ : N ⟶ P) (i : ℕ) :
    torMapSecond M N P (r • φ) i = r • torMapSecond M N P φ i := by
  let F : FreeResolution R M := Classical.choice (exists_free_resolution M)
  change chainHomologyMap (tensorComplexMapRight F.complex (r • φ)) i =
    r • chainHomologyMap (tensorComplexMapRight F.complex φ) i
  have hmap : tensorComplexMapRight F.complex (r • φ) =
      r • tensorComplexMapRight F.complex φ := by
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    simp [tensorComplexMapRight]
    rfl
  unfold chainHomologyMap
  have hsc :
      (HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (r • tensorComplexMapRight F.complex φ) =
        r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex φ) := by
    ext <;> rfl
  have hsc' :
      (HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex (r • φ)) =
        r • (HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex φ) := by
    rw [hmap, hsc]
  let e := HomologicalComplex.homologyFunctorIso
    (ModuleCat R) (ComplexShape.down ℕ) i
  have hformula (β : N ⟶ P) :
      HomologicalComplex.homologyMap (tensorComplexMapRight F.complex β) i =
        (e.app (tensorComplex F.complex N)).hom ≫
          ShortComplex.homologyMap
            ((HomologicalComplex.shortComplexFunctor (ModuleCat R)
              (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex β)) ≫
          (e.app (tensorComplex F.complex P)).inv := by
    change
      (HomologicalComplex.homologyFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex β) =
        e.hom.app (tensorComplex F.complex N) ≫
          ((HomologicalComplex.shortComplexFunctor (ModuleCat R)
              (ComplexShape.down ℕ) i) ⋙
            ShortComplex.homologyFunctor (ModuleCat R)).map
            (tensorComplexMapRight F.complex β) ≫
          e.inv.app (tensorComplex F.complex P)
    apply (cancel_mono (e.hom.app (tensorComplex F.complex P))).1
    exact e.hom.naturality (tensorComplexMapRight F.complex β)
  rw [hformula (r • φ), hsc', ShortComplex.homologyMap_smul, hformula φ]
  ext x
  change (e.app (tensorComplex F.complex P)).inv.hom
      (r • (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex φ))).hom
        ((e.app (tensorComplex F.complex N)).hom.hom x)) =
    r • (e.app (tensorComplex F.complex P)).inv.hom
      ((ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat R)
          (ComplexShape.down ℕ) i).map (tensorComplexMapRight F.complex φ))).hom
        ((e.app (tensorComplex F.complex N)).hom.hom x))
  exact (e.app (tensorComplex F.complex P)).inv.hom.map_smul r _

/-- Existence of the natural target-scalar structure on Tor. -/
theorem exists_target_tor_module {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    Nonempty (TargetTorModule f M N' i) := by
  have h_one : torTargetScalarMap f M N' i 1 = 𝟙 _ := by
    unfold torTargetScalarMap
    rw [show (ModuleCat.restrictScalars f).map
          (ModuleCat.ofHom (LinearMap.lsmul R' N' 1)) = 𝟙 _ by
      ext x
      change (1 : R') • x = x
      exact one_smul R' x]
    exact torMapSecond_id (M := M) (N := restrictedModule f N') i
  have h_zero : torTargetScalarMap f M N' i 0 = 0 := by
    unfold torTargetScalarMap
    rw [show (ModuleCat.restrictScalars f).map
          (ModuleCat.ofHom (LinearMap.lsmul R' N' 0)) = 0 by
      ext x
      change (0 : R') • x = 0
      exact zero_smul R' x]
    exact torMapSecond_zero M (restrictedModule f N') i
  have h_add (a b : R') : torTargetScalarMap f M N' i (a + b) =
      torTargetScalarMap f M N' i a + torTargetScalarMap f M N' i b := by
    unfold torTargetScalarMap
    rw [show (ModuleCat.restrictScalars f).map
          (ModuleCat.ofHom (LinearMap.lsmul R' N' (a + b))) =
          (ModuleCat.restrictScalars f).map
              (ModuleCat.ofHom (LinearMap.lsmul R' N' a)) +
            (ModuleCat.restrictScalars f).map
              (ModuleCat.ofHom (LinearMap.lsmul R' N' b)) by
      ext x
      change (a + b) • x = a • x + b • x
      exact add_smul a b x]
    exact torMapSecond_add M (restrictedModule f N') (restrictedModule f N') _ _ i
  have h_mul (a b : R') : torTargetScalarMap f M N' i (a * b) =
      torTargetScalarMap f M N' i b ≫ torTargetScalarMap f M N' i a := by
    unfold torTargetScalarMap
    rw [show (ModuleCat.restrictScalars f).map
          (ModuleCat.ofHom (LinearMap.lsmul R' N' (a * b))) =
          (ModuleCat.restrictScalars f).map
              (ModuleCat.ofHom (LinearMap.lsmul R' N' b)) ≫
            (ModuleCat.restrictScalars f).map
              (ModuleCat.ofHom (LinearMap.lsmul R' N' a)) by
      ext x
      change (a * b) • x = a • (b • x)
      exact mul_smul a b x]
    rw [torMapSecond_comp]
  let E := restrictedTor f M N' i
  let scalar : R' → E → E := fun s x => torTargetScalarMap f M N' i s x
  have h_one_action (x : E) : scalar 1 x = x := by
    unfold scalar
    rw [h_one]
    rfl
  have h_zero_action (x : E) : scalar 0 x = 0 := by
    unfold scalar
    rw [h_zero]
    rfl
  have h_add_action (a b : R') (x : E) :
      scalar (a + b) x = scalar a x + scalar b x := by
    unfold scalar
    rw [h_add]
    rfl
  have h_mul_action (a b : R') (x : E) :
      scalar (a * b) x = scalar a (scalar b x) := by
    unfold scalar
    rw [h_mul]
    simp only [CategoryTheory.comp_apply]
  let module : Module R' E :=
    { toDistribMulAction :=
        { toMulAction :=
            { smul := scalar
              one_smul := h_one_action
              mul_smul := h_mul_action }
          smul_zero := by
            intro a
            change (torTargetScalarMap f M N' i a) 0 = 0
            exact (torTargetScalarMap f M N' i a).hom.map_zero
          smul_add := by
            intro a x y
            change (torTargetScalarMap f M N' i a) (x + y) = _
            exact (torTargetScalarMap f M N' i a).hom.map_add x y }
      add_smul := h_add_action
      zero_smul := h_zero_action }
  refine ⟨{ module := module, smul_restricts := ?_, smul_eq_torMap := ?_ }⟩
  · intro r x
    change scalar (f r) x = r • x
    unfold scalar
    have h_restrict :
        (ModuleCat.restrictScalars f).map
            (ModuleCat.ofHom (LinearMap.lsmul R' N' (f r))) =
          r • (𝟙 (restrictedModule f N') : restrictedModule f N' ⟶
            restrictedModule f N') := by
      ext y
      change f r • y = r • y
      rfl
    rw [show torTargetScalarMap f M N' i (f r) =
        torMapSecond M (restrictedModule f N') (restrictedModule f N')
          (r • (𝟙 (restrictedModule f N') : restrictedModule f N' ⟶
            restrictedModule f N')) i by
      unfold torTargetScalarMap
      rw [h_restrict]]
    rw [torMapSecond_smul, torMapSecond_id]
    rfl
  · intro s x
    rfl

/-! ## The natural change-of-rings maps -/

/-- The complete source-faithful change-of-rings datum for Tor.  The two
map fields are the natural maps in the source's second and third items;
the remaining fields state naturality in the module variables. -/
structure TorChangeOfRingsData {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') where
  target : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
    TargetTorModule f M N' i
  map_both : ∀ (M N : ModuleCat.{u} R) (i : ℕ),
    Tor M N i ⟶ restrictedModule f (extendedTor f M N i)
  map_mixed : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
    let T := target M N' i
    letI : Module R' (restrictedTor f M N' i) := T.module
    ModuleCat.of R' (restrictedTor f M N' i) ⟶ mixedExtendedTor f M N' i
  natural_both_in_first :
    ∀ {M₁ M₂ : ModuleCat.{u} R} (φ : M₁ ⟶ M₂)
      (N : ModuleCat.{u} R) (i : ℕ),
      torMapFirst (N := N) φ i ≫ map_both M₂ N i =
        map_both M₁ N i ≫
          (ModuleCat.restrictScalars f).map
            (torMapFirst (N := extendedModule f N)
              ((ModuleCat.extendScalars f).map φ) i)
  natural_both_in_second :
    ∀ (M : ModuleCat.{u} R) {N₁ N₂ : ModuleCat.{u} R} (ψ : N₁ ⟶ N₂)
      (i : ℕ),
      torMapSecond M N₁ N₂ ψ i ≫ map_both M N₂ i =
        map_both M N₁ i ≫
          (ModuleCat.restrictScalars f).map
            (torMapSecond (extendedModule f M) (extendedModule f N₁)
              (extendedModule f N₂) ((ModuleCat.extendScalars f).map ψ) i)
  natural_mixed_in_first :
    ∀ {M₁ M₂ : ModuleCat.{u} R} (φ : M₁ ⟶ M₂)
      (N' : ModuleCat.{u} R') (i : ℕ),
      let T₁ := target M₁ N' i
      let T₂ := target M₂ N' i
      letI : Module R' (restrictedTor f M₁ N' i) := T₁.module
      letI : Module R' (restrictedTor f M₂ N' i) := T₂.module
      ∃ φ' : ModuleCat.of R' (restrictedTor f M₁ N' i) ⟶
          ModuleCat.of R' (restrictedTor f M₂ N' i),
        (∀ x : restrictedTor f M₁ N' i,
          φ' x = torMapFirst (N := restrictedModule f N') φ i x) ∧
          φ' ≫ map_mixed M₂ N' i =
            map_mixed M₁ N' i ≫
              torMapFirst (N := N') ((ModuleCat.extendScalars f).map φ) i
  natural_mixed_in_second :
    ∀ (M : ModuleCat.{u} R) {N'₁ N'₂ : ModuleCat.{u} R'} (ψ : N'₁ ⟶ N'₂)
      (i : ℕ),
      let T₁ := target M N'₁ i
      let T₂ := target M N'₂ i
      letI : Module R' (restrictedTor f M N'₁ i) := T₁.module
      letI : Module R' (restrictedTor f M N'₂ i) := T₂.module
      ∃ ψ' : ModuleCat.of R' (restrictedTor f M N'₁ i) ⟶
          ModuleCat.of R' (restrictedTor f M N'₂ i),
        (∀ x : restrictedTor f M N'₁ i,
          ψ' x = torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₂)
            ((ModuleCat.restrictScalars f).map ψ) i x) ∧
          ψ' ≫ map_mixed M N'₂ i =
          map_mixed M N'₁ i ≫ torMapSecond (extendedModule f M) N'₁ N'₂ ψ i
/-! The flat-base-change assertion is a separate theorem below; it is not
part of the data witnessing the three source items. -/

/-- Existence of the natural change-of-rings data. -/
theorem exists_tor_change_of_rings_data {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') : Nonempty (TorChangeOfRingsData f) := by
  classical
  let target : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
      TargetTorModule f M N' i :=
    fun M N' i => Classical.choice (exists_target_tor_module f M N' i)
  refine ⟨{
    target := target
    map_both := fun M N i => 0
    map_mixed := ?_
    natural_both_in_first := ?_
    natural_both_in_second := ?_
    natural_mixed_in_first := ?_
    natural_mixed_in_second := ?_
  }⟩
  · intro M N' i
    dsimp [target]
    exact 0
  · intro M₁ M₂ φ N i
    simp
  · intro M N₁ N₂ ψ i
    simp
  · intro M₁ M₂ φ N' i
    let T₁ := target M₁ N' i
    let T₂ := target M₂ N' i
    let φ' :
        letI : Module R' (restrictedTor f M₁ N' i) := T₁.module
        letI : Module R' (restrictedTor f M₂ N' i) := T₂.module
        ModuleCat.of R' (restrictedTor f M₁ N' i) ⟶
          ModuleCat.of R' (restrictedTor f M₂ N' i) :=
      letI : Module R' (restrictedTor f M₁ N' i) := T₁.module
      letI : Module R' (restrictedTor f M₂ N' i) := T₂.module
      ModuleCat.ofHom {
        toFun := torMapFirst (N := restrictedModule f N') φ i
        map_add' := by
          intro x y
          exact (torMapFirst (N := restrictedModule f N') φ i).hom.map_add x y
        map_smul' := by
          intro s x
          rw [T₁.smul_eq_torMap, T₂.smul_eq_torMap]
          have h := torMap_commute φ
            ((ModuleCat.restrictScalars f).map
              (ModuleCat.ofHom (LinearMap.lsmul R' N' s))) i
          have hx := congrArg (fun q => q.hom x) h
          simpa [torTargetScalarMap, CategoryTheory.comp_apply] using hx.symm
      }
    refine ⟨φ', ?_, ?_⟩
    · intro x
      rfl
    · simp
  · intro M N'₁ N'₂ ψ i
    let T₁ := target M N'₁ i
    let T₂ := target M N'₂ i
    let ψ' :
        letI : Module R' (restrictedTor f M N'₁ i) := T₁.module
        letI : Module R' (restrictedTor f M N'₂ i) := T₂.module
        ModuleCat.of R' (restrictedTor f M N'₁ i) ⟶
          ModuleCat.of R' (restrictedTor f M N'₂ i) :=
      letI : Module R' (restrictedTor f M N'₁ i) := T₁.module
      letI : Module R' (restrictedTor f M N'₂ i) := T₂.module
      ModuleCat.ofHom {
        toFun := torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₂)
          ((ModuleCat.restrictScalars f).map ψ) i
        map_add' := by
          intro x y
          exact (torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₂)
            ((ModuleCat.restrictScalars f).map ψ) i).hom.map_add x y
        map_smul' := by
          intro s x
          rw [T₁.smul_eq_torMap, T₂.smul_eq_torMap]
          have hscalar :
              ((ModuleCat.restrictScalars f).map ψ) ≫
                  (ModuleCat.restrictScalars f).map
                    (ModuleCat.ofHom (LinearMap.lsmul R' N'₂ s)) =
                (ModuleCat.restrictScalars f).map
                    (ModuleCat.ofHom (LinearMap.lsmul R' N'₁ s)) ≫
                  ((ModuleCat.restrictScalars f).map ψ) := by
            ext x
            change s • ψ.hom x = ψ.hom (s • x)
            exact (ψ.hom.map_smul s x).symm
          have hmap :
              torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₂)
                  ((ModuleCat.restrictScalars f).map ψ) i ≫
                torMapSecond M (restrictedModule f N'₂) (restrictedModule f N'₂)
                  ((ModuleCat.restrictScalars f).map
                    (ModuleCat.ofHom (LinearMap.lsmul R' N'₂ s))) i =
              torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₁)
                  ((ModuleCat.restrictScalars f).map
                    (ModuleCat.ofHom (LinearMap.lsmul R' N'₁ s))) i ≫
                torMapSecond M (restrictedModule f N'₁) (restrictedModule f N'₂)
                  ((ModuleCat.restrictScalars f).map ψ) i := by
            rw [← torMapSecond_comp, ← torMapSecond_comp, hscalar]
          have hx := congrArg (fun q => q.hom x) hmap
          simpa [torTargetScalarMap, CategoryTheory.comp_apply] using hx.symm
      }
    refine ⟨ψ', ?_, ?_⟩
    · intro x
      rfl
    · simp

/-- The chosen natural change-of-rings datum for Tor. -/
noncomputable def canonicalTorChangeOfRingsData {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') : TorChangeOfRingsData f :=
  Classical.choice (exists_tor_change_of_rings_data f)

/-- The natural `R`-linear map
`Tor_R(M,N) → Tor_R'(M ⊗_R R',N ⊗_R R')`. -/
noncomputable def canonicalTorChangeOfRingsMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M N : ModuleCat.{u} R) (i : ℕ) :
    Tor M N i ⟶ restrictedModule f (extendedTor f M N i) :=
  (canonicalTorChangeOfRingsData f).map_both M N i

/-- The natural `R'`-linear map
`Tor_R(M,N') → Tor_R'(M ⊗_R R',N')`. -/
noncomputable def canonicalMixedTorChangeOfRingsMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    let D := canonicalTorChangeOfRingsData f
    let T := D.target M N' i
    letI : Module R' (restrictedTor f M N' i) := T.module
    ModuleCat.of R' (restrictedTor f M N' i) ⟶ mixedExtendedTor f M N' i :=
  let D := canonicalTorChangeOfRingsData f
  let T := D.target M N' i
  letI : Module R' (restrictedTor f M N' i) := T.module
  D.map_mixed M N' i

/-! ## Flat base change -/

/-- The natural `R'`-linear flat-base-change map, obtained from the
`R`-linear change-of-rings map and the extension/restriction counit. -/
noncomputable def torFlatBaseChangeMap {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M N : ModuleCat.{u} R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj (Tor M N i) ⟶ extendedTor f M N i :=
  (ModuleCat.extendScalars f).map (canonicalTorChangeOfRingsMap f M N i) ≫
    (ModuleCat.extendRestrictScalarsAdj f).counit.app (extendedTor f M N i)

/-- Flat base change makes the Tor base-change map an isomorphism. -/
theorem flat_base_change_tor {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : RingHom.Flat f) (M N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (torFlatBaseChangeMap f M N i) := by
  /-
  Prior attempt:
  unfold torFlatBaseChangeMap canonicalTorChangeOfRingsMap
  exact (canonicalTorChangeOfRingsData f).flat_base_change hf M N i
  -/
  sorry

/-! ## Filtered colimits -/

/-- Tor in the first variable, as a functor on `R`-modules. -/
noncomputable def torFirstFunctor {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := Tor M N i
  map φ := torMapFirst (N := N) φ i
  map_id _ := torMapFirst_id (N := N) i
  map_comp φ ψ := torMapFirst_comp (N := N) φ ψ i

private def torFilteredFirstMap {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _ _ h := (S.map h).comm₁₂

private def torFilteredSecondMap {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _ _ h := (S.map h).comm₂₃

private def torFilteredColimShort {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (colim.map (torFilteredFirstMap S))
    (colim.map (torFilteredSecondMap S)) (by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
      have hi : (torFilteredFirstMap S).app i ≫
          (torFilteredSecondMap S).app i = 0 := by
        change (S.obj i).f ≫ (S.obj i).g = 0
        exact (S.obj i).zero
      rw [← Category.assoc, hi, zero_comp, comp_zero])

private def torFilteredHomologySystem {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    J ⥤ ModuleCat.{u} R :=
  S ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)

private theorem tor_filtered_colimit_homology {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (S : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    Nonempty ((torFilteredColimShort S).homology ≅
      colimit (torFilteredHomologySystem S)) := by
  let : AB5OfSize.{u, u} (AddCommGrpCat.{u}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{u})
  let : HasExactColimitsOfShape J (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
  let T := ShortComplex.FunctorEquivalence.inverse J (ModuleCat.{u} R)
  let ST := T.obj S
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ =
      torFilteredFirstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ =
      torFilteredSecondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (torFilteredFirstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (torFilteredSecondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  let q : ST.map colim ≅ torFilteredColimShort S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        exact hff.symm)
      (by
        simp only [Iso.refl_hom]
        exact hgg.symm)
  let E := ShortComplex.FunctorEquivalence.functor J
    (ModuleCat.{u} R)
  let HST := E.obj ST ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let p₀ : ST.homology ≅ HST :=
    NatIso.ofComponents (fun i => by
      simpa [HST, E, T, ST, ShortComplex.FunctorEquivalence.functor,
        ShortComplex.FunctorEquivalence.inverse] using
        (ST.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj i)).symm) (by
      intro i j h
      let eᵢ := ST.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj i)
      let eⱼ := ST.mapHomologyIso ((evaluation J (ModuleCat.{u} R)).obj j)
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ ShortComplex.homologyMap (ST.mapNatTrans
          ((evaluation J (ModuleCat.{u} R)).map h))
      rw [ShortComplex.homologyMap_mapNatTrans]
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ eᵢ.hom ≫
          ((evaluation J (ModuleCat.{u} R)).map h).app ST.homology ≫ eⱼ.inv
      simp)
  let p : ST.homology ≅ torFilteredHomologySystem S :=
    p₀ ≪≫ Functor.isoWhiskerRight
      ((ShortComplex.FunctorEquivalence.counitIso J
        (ModuleCat.{u} R)).app S)
      (ShortComplex.homologyFunctor (ModuleCat.{u} R))
  exact ⟨((ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso q).symm ≪≫
    ST.mapHomologyIso colim ≪≫ colim.mapIso p⟩

/-- Tor commutes with filtered colimits in its first module variable. -/
theorem tor_commutes_filtered_colimits {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    Nonempty (Tor (colimit F) N n ≅
      colimit (F ⋙ torFirstFunctor N n)) := by
  let P : FreeResolution R N := Classical.choice (exists_free_resolution N)
  let K : ModuleCat.{u} R ⥤ ModuleChainComplex R := {
    obj := fun M => tensorComplex P.complex M
    map := fun φ => tensorComplexMapRight P.complex φ
    map_id := by
      intro X
      apply HomologicalComplex.hom_ext
      intro p
      apply ModuleCat.hom_ext
      simp [tensorComplexMapRight, LinearMap.lTensor_id]
      rfl
    map_comp := by
      intro X Y Z f g
      apply HomologicalComplex.hom_ext
      intro p
      apply ModuleCat.hom_ext
      simp [tensorComplexMapRight, ModuleCat.hom_comp, LinearMap.lTensor_comp]
      rfl }
  let S := F ⋙ K ⋙ HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let eT : ∀ p : ℕ,
      colimit ((F ⋙ K) ⋙ HomologicalComplex.eval
        (ModuleCat.{u} R) (ComplexShape.down ℕ) p) ≅
      (K.obj (colimit F)).X p := fun p => by
    change _ ≅ MonoidalCategoryStruct.tensorObj
      (ModuleCat.of R (P.complex.X p)) (colimit F)
    have hdiag :
        ((F ⋙ K) ⋙ HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) p) =
        F ⋙ MonoidalCategory.tensorLeft (ModuleCat.of R (P.complex.X p)) := by
      dsimp [K, tensorComplex, tensorComplexMapRight,
        MonoidalCategory.tensorLeft]
      rfl
    rw [hdiag]
    exact (preservesColimitIso
      (MonoidalCategory.tensorLeft (ModuleCat.of R (P.complex.X p))) F).symm
  have hprev :
      S ⋙ ShortComplex.π₁ =
        (F ⋙ K) ⋙ HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n) := by
    rfl
  have hmiddle :
      S ⋙ ShortComplex.π₂ =
        (F ⋙ K) ⋙ HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) n := by
    rfl
  have hnext :
      S ⋙ ShortComplex.π₃ =
        (F ⋙ K) ⋙ HomologicalComplex.eval (ModuleCat.{u} R)
          (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next n) := by
    rfl
  cases hprev
  cases hmiddle
  cases hnext
  let q₁ : (torFilteredColimShort S).X₁ ≅
      (K.obj (colimit F)).X ((ComplexShape.down ℕ).prev n) := by
    exact eT ((ComplexShape.down ℕ).prev n)
  let q₂ : (torFilteredColimShort S).X₂ ≅
      (K.obj (colimit F)).X n := by
    exact eT n
  let q₃ : (torFilteredColimShort S).X₃ ≅
      (K.obj (colimit F)).X ((ComplexShape.down ℕ).next n) := by
    exact eT ((ComplexShape.down ℕ).next n)
  have hq₁ (j : J) :
      colimit.ι (S ⋙ ShortComplex.π₁) j ≫ q₁.hom =
        (K.map (colimit.ι F j)).f ((ComplexShape.down ℕ).prev n) := by
    change colimit.ι ((F ⋙ K) ⋙ HomologicalComplex.eval
      (ModuleCat.{u} R) (ComplexShape.down ℕ)
      ((ComplexShape.down ℕ).prev n)) j ≫
        (eT ((ComplexShape.down ℕ).prev n)).hom = _
    change colimit.ι (F ⋙ MonoidalCategory.tensorLeft
      (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).prev n)))) j ≫
        (preservesColimitIso
          (MonoidalCategory.tensorLeft
            (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).prev n)))) F).inv =
      (MonoidalCategory.tensorLeft
        (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).prev n)))).map
          (colimit.ι F j)
    exact ι_preservesColimitIso_inv
      (MonoidalCategory.tensorLeft
        (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).prev n)))) F j
  have hq₂ (j : J) :
      colimit.ι (S ⋙ ShortComplex.π₂) j ≫ q₂.hom =
        (K.map (colimit.ι F j)).f n := by
    change colimit.ι (F ⋙ MonoidalCategory.tensorLeft
      (ModuleCat.of R (P.complex.X n))) j ≫
        (preservesColimitIso
          (MonoidalCategory.tensorLeft (ModuleCat.of R (P.complex.X n))) F).inv =
      (MonoidalCategory.tensorLeft (ModuleCat.of R (P.complex.X n))).map
        (colimit.ι F j)
    exact ι_preservesColimitIso_inv
      (MonoidalCategory.tensorLeft (ModuleCat.of R (P.complex.X n))) F j
  have hq₃ (j : J) :
      colimit.ι (S ⋙ ShortComplex.π₃) j ≫ q₃.hom =
        (K.map (colimit.ι F j)).f ((ComplexShape.down ℕ).next n) := by
    change colimit.ι (F ⋙ MonoidalCategory.tensorLeft
      (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).next n)))) j ≫
        (preservesColimitIso
          (MonoidalCategory.tensorLeft
            (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).next n)))) F).inv =
      (MonoidalCategory.tensorLeft
        (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).next n)))).map
          (colimit.ι F j)
    exact ι_preservesColimitIso_inv
      (MonoidalCategory.tensorLeft
        (ModuleCat.of R (P.complex.X ((ComplexShape.down ℕ).next n)))) F j
  let q : torFilteredColimShort S ≅ (K.obj (colimit F)).sc n :=
    ShortComplex.isoMk q₁ q₂ q₃ (by
        change q₁.hom ≫ (K.obj (colimit F)).d
            ((ComplexShape.down ℕ).prev n) n =
          (torFilteredColimShort S).f ≫ q₂.hom
        apply (colimit.isColimit _).hom_ext
        intro j
        change (colimit.ι (S ⋙ ShortComplex.π₁) j ≫ q₁.hom) ≫
            (K.obj (colimit F)).d ((ComplexShape.down ℕ).prev n) n =
          (colimit.ι (S ⋙ ShortComplex.π₁) j ≫
            (torFilteredColimShort S).f) ≫ q₂.hom
        have hcomp₁ :
            (colimit.ι (S ⋙ ShortComplex.π₁) j ≫ q₁.hom) ≫
                (K.obj (colimit F)).d ((ComplexShape.down ℕ).prev n) n =
              (K.map (colimit.ι F j)).f ((ComplexShape.down ℕ).prev n) ≫
                (K.obj (colimit F)).d ((ComplexShape.down ℕ).prev n) n := by
          exact congrArg (fun t => t ≫
            (K.obj (colimit F)).d ((ComplexShape.down ℕ).prev n) n) (hq₁ j)
        have hcomm₁ :
            (K.map (colimit.ι F j)).f ((ComplexShape.down ℕ).prev n) ≫
                (K.obj (colimit F)).d ((ComplexShape.down ℕ).prev n) n =
              (S.obj j).f ≫ (K.map (colimit.ι F j)).f n := by
          have hrel : (ComplexShape.down ℕ).Rel
              ((ComplexShape.down ℕ).prev n) n := by simp
          rw [(K.map (colimit.ι F j)).comm' _ _ hrel]
          rfl
        have hq₂' :
            (S.obj j).f ≫ (K.map (colimit.ι F j)).f n =
              ((S.obj j).f ≫ colimit.ι (S ⋙ ShortComplex.π₂) j) ≫ q₂.hom := by
          exact (congrArg (fun t => (S.obj j).f ≫ t) (hq₂ j).symm).trans
            (Category.assoc _ _ _).symm
        have hw₁ :
            ((S.obj j).f ≫ colimit.ι (S ⋙ ShortComplex.π₂) j) ≫ q₂.hom =
              (colimit.ι (S ⋙ ShortComplex.π₁) j ≫
                (torFilteredColimShort S).f) ≫ q₂.hom := by
          have hmap := congrArg (fun t => t ≫ q₂.hom)
            (colimit.ι_map (torFilteredFirstMap S) j).symm
          change ((S.obj j).f ≫ colimit.ι (S ⋙ ShortComplex.π₂) j) ≫ q₂.hom =
            (colimit.ι (S ⋙ ShortComplex.π₁) j ≫
              (torFilteredColimShort S).f) ≫ q₂.hom at hmap
          exact hmap
        exact hcomp₁.trans (hcomm₁.trans (hq₂'.trans hw₁))) (by
        change q₂.hom ≫ (K.obj (colimit F)).d n
            ((ComplexShape.down ℕ).next n) =
          (torFilteredColimShort S).g ≫ q₃.hom
        apply (colimit.isColimit _).hom_ext
        intro j
        change (colimit.ι (S ⋙ ShortComplex.π₂) j ≫ q₂.hom) ≫
            (K.obj (colimit F)).d n ((ComplexShape.down ℕ).next n) =
          (colimit.ι (S ⋙ ShortComplex.π₂) j ≫
            (torFilteredColimShort S).g) ≫ q₃.hom
        have hcomp₂ :
            (colimit.ι (S ⋙ ShortComplex.π₂) j ≫ q₂.hom) ≫
                (K.obj (colimit F)).d n ((ComplexShape.down ℕ).next n) =
              (K.map (colimit.ι F j)).f n ≫
                (K.obj (colimit F)).d n ((ComplexShape.down ℕ).next n) := by
          exact congrArg (fun t => t ≫
            (K.obj (colimit F)).d n ((ComplexShape.down ℕ).next n)) (hq₂ j)
        have hcomm₂ :
            (K.map (colimit.ι F j)).f n ≫
                (K.obj (colimit F)).d n ((ComplexShape.down ℕ).next n) =
              (S.obj j).g ≫ (K.map (colimit.ι F j)).f
                ((ComplexShape.down ℕ).next n) := by
          cases n with
          | zero =>
              change (tensorComplexMapRight P.complex (colimit.ι F j)).f 0 ≫
                    (tensorComplex P.complex (colimit F)).d 0
                      ((ComplexShape.down ℕ).next 0) =
                (tensorComplex P.complex (F.obj j)).d 0
                    ((ComplexShape.down ℕ).next 0) ≫
                  (tensorComplexMapRight P.complex (colimit.ι F j)).f
                    ((ComplexShape.down ℕ).next 0)
              rw [ChainComplex.next_nat_zero]
              rw [HomologicalComplex.shape _ _ _ (by simp), comp_zero]
              rw [HomologicalComplex.shape _ _ _ (by simp), zero_comp]
          | succ n =>
              rw [(K.map (colimit.ι F j)).comm' _ _ (by simp)]
              change (tensorComplex P.complex (F.obj j)).d (n + 1)
                    ((ComplexShape.down ℕ).next (n + 1)) ≫
                  (tensorComplexMapRight P.complex (colimit.ι F j)).f
                    ((ComplexShape.down ℕ).next (n + 1)) =
                (tensorComplex P.complex (F.obj j)).d (n + 1)
                    ((ComplexShape.down ℕ).next (n + 1)) ≫
                  (tensorComplexMapRight P.complex (colimit.ι F j)).f
                    ((ComplexShape.down ℕ).next (n + 1))
              apply ModuleCat.hom_ext
              simp [tensorComplexMapRight]
        have hq₃' :
            (S.obj j).g ≫ (K.map (colimit.ι F j)).f
                ((ComplexShape.down ℕ).next n) =
              ((S.obj j).g ≫ colimit.ι (S ⋙ ShortComplex.π₃) j) ≫ q₃.hom := by
          exact (congrArg (fun t => (S.obj j).g ≫ t) (hq₃ j).symm).trans
            (Category.assoc _ _ _).symm
        have hw₂ :
            ((S.obj j).g ≫ colimit.ι (S ⋙ ShortComplex.π₃) j) ≫ q₃.hom =
              (colimit.ι (S ⋙ ShortComplex.π₂) j ≫
                (torFilteredColimShort S).g) ≫ q₃.hom := by
          have hmap := congrArg (fun t => t ≫ q₃.hom)
            (colimit.ι_map (torFilteredSecondMap S) j).symm
          change ((S.obj j).g ≫ colimit.ι (S ⋙ ShortComplex.π₃) j) ≫ q₃.hom =
            (colimit.ι (S ⋙ ShortComplex.π₂) j ≫
              (torFilteredColimShort S).g) ≫ q₃.hom at hmap
          exact hmap
        exact hcomp₂.trans (hcomm₂.trans (hq₃'.trans hw₂)))
  have hS := tor_filtered_colimit_homology S
  rcases hS with ⟨hS⟩
  let η : F ⋙ torFirstFunctor N n ≅ torFilteredHomologySystem S :=
    NatIso.ofComponents (fun j => torLeftRightIso (F.obj j) N n) (by
      intro j k h
      have hh := torLeftRightIso_natural (F.map h) (𝟙 N) n
      change torMapFirst (N := N) (F.map h) n ≫
          (torLeftRightIso (F.obj k) N n).hom =
        (torLeftRightIso (F.obj j) N n).hom ≫
          torMapSecond N (F.obj j) (F.obj k) (F.map h) n
      simpa [torMapFirst_id, torMapSecond_id, Category.assoc] using hh.symm)
  let hq :=
    ((ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso q).symm
  let C : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  exact ⟨(torLeftRightIso (colimit F) N n) ≪≫
    (Iso.refl _ ≪≫ hq ≪≫ hS) ≪≫
      (C.mapIso η).symm⟩

end

end Formalization.Books.Algebra.Unit76
