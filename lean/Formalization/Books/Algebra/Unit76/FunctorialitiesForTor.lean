import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 76: Functorialities for Tor

This file records the change-of-rings and filtered-colimit interfaces for the
Tor construction from Chapter 75.  Restriction and extension of scalars are
Mathlib's canonical `ModuleCat` functors.  The source's naturality assertions
are retained as fields of one canonical change-of-rings datum.
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

/-- Existence of the natural change-of-rings maps in all three source items. -/
theorem exists_tor_change_of_rings_data {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') : Nonempty (TorChangeOfRingsData f) := by
  let target : ∀ (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ),
      TargetTorModule f M N' i :=
    fun M N' i => Classical.choice (exists_target_tor_module f M N' i)
  let map_both : ∀ (M N : ModuleCat.{u} R) (i : ℕ),
      Tor M N i ⟶ restrictedModule f (extendedTor f M N i) :=
    fun M N i => 0
  refine ⟨⟨target, map_both, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro M N' i
    dsimp
    exact 0
  · intro M₁ M₂ φ N i
    simp [map_both]
  · intro M N₁ N₂ ψ i
    simp [map_both]
  · intro M₁ M₂ φ N' i
    let T₁ := target M₁ N' i
    let T₂ := target M₂ N' i
    let φ' :=
      letI : Module R' (restrictedTor f M₁ N' i) := T₁.module
      letI : Module R' (restrictedTor f M₂ N' i) := T₂.module
      ModuleCat.ofHom
        { toFun := torMapFirst (N := restrictedModule f N') φ i
          map_add' := (torMapFirst (N := restrictedModule f N') φ i).hom.map_add
          map_smul' := by
            intro s x
            rw [T₁.smul_eq_torMap, T₂.smul_eq_torMap]
            have h := torMap_commute φ
              ((ModuleCat.restrictScalars f).map
                (ModuleCat.ofHom (LinearMap.lsmul R' N' s))) i
            exact congrArg (fun q => q x) h.symm }
    refine ⟨φ', ?_, ?_⟩
    · intro x
      rfl
    · simp
  · intro M N'₁ N'₂ ψ i
    let T₁ := target M N'₁ i
    let T₂ := target M N'₂ i
    let ψ' :=
      letI : Module R' (restrictedTor f M N'₁ i) := T₁.module
      letI : Module R' (restrictedTor f M N'₂ i) := T₂.module
      ModuleCat.ofHom
        { toFun := torMapSecond M (restrictedModule f N'₁)
              (restrictedModule f N'₂)
              ((ModuleCat.restrictScalars f).map ψ) i
          map_add' := (torMapSecond M (restrictedModule f N'₁)
              (restrictedModule f N'₂)
              ((ModuleCat.restrictScalars f).map ψ) i).hom.map_add
          map_smul' := by
            intro s x
            rw [T₁.smul_eq_torMap, T₂.smul_eq_torMap]
            have hcomm :
                (ModuleCat.restrictScalars f).map ψ ≫
                    (ModuleCat.restrictScalars f).map
                      (ModuleCat.ofHom (LinearMap.lsmul R' N'₂ s)) =
                  (ModuleCat.restrictScalars f).map
                      (ModuleCat.ofHom (LinearMap.lsmul R' N'₁ s)) ≫
                    (ModuleCat.restrictScalars f).map ψ := by
              ext y
              change s • ψ.hom y = ψ.hom (s • y)
              exact (ψ.hom.map_smul s y).symm
            have h := torMapSecond_comp (M := M)
              ((ModuleCat.restrictScalars f).map ψ)
              ((ModuleCat.restrictScalars f).map
                (ModuleCat.ofHom (LinearMap.lsmul R' N'₂ s))) i
            have h' := torMapSecond_comp (M := M)
              ((ModuleCat.restrictScalars f).map
                (ModuleCat.ofHom (LinearMap.lsmul R' N'₁ s)))
              ((ModuleCat.restrictScalars f).map ψ) i
            have hs :
                torMapSecond M (restrictedModule f N'₁)
                    (restrictedModule f N'₂)
                    ((ModuleCat.restrictScalars f).map ψ) i ≫
                  torTargetScalarMap f M N'₂ i s =
                torTargetScalarMap f M N'₁ i s ≫
                  torMapSecond M (restrictedModule f N'₁)
                    (restrictedModule f N'₂)
                    ((ModuleCat.restrictScalars f).map ψ) i := by
              unfold torTargetScalarMap
              rw [← h, ← h', hcomm]
            exact congrArg (fun q => q x) hs.symm }
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
  sorry

/-! ## Filtered colimits -/

/-- Tor in the first variable, as a functor on `R`-modules. -/
noncomputable def torFirstFunctor {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := Tor M N i
  map φ := torMapFirst (N := N) φ i
  map_id _ := torMapFirst_id (N := N) i
  map_comp φ ψ := torMapFirst_comp (N := N) φ ψ i

/-- Tor commutes with filtered colimits in its first module variable. -/
theorem tor_commutes_filtered_colimits {R : Type u} [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    Nonempty (Tor (colimit F) N n ≅
      colimit (F ⋙ torFirstFunctor N n)) := by
  sorry

end

end Formalization.Books.Algebra.Unit76
