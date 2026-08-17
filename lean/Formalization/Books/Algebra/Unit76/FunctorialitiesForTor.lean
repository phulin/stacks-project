import Formalization.Books.Algebra.Unit75.TorGroups
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

/-- Existence of the natural target-scalar structure on Tor. -/
theorem exists_target_tor_module {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R') (i : ℕ) :
    Nonempty (TargetTorModule f M N' i) := by
  sorry

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
  sorry

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
