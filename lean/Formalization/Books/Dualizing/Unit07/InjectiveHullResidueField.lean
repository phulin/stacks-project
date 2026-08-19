import Formalization.Books.Dualizing.Unit06
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Flat

/-!
# Dualizing Complexes, Chapter 7: Injective hull of the residue field

This file records the definitions and theorem interfaces in the section on
injective hulls of residue fields.  The proofs are deferred to the proving
stage; the canonical module constructions are implemented here.
-/

namespace Formalization.Books.Dualizing.Unit07

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dualizing.Unit02
open Formalization.Books.Dualizing.Unit05

universe u

noncomputable section

/-! ## Residue-field injective hulls and quotient rings -/

/-- An injective hull of the residue field of a local ring. -/
def IsResidueFieldInjectiveHull {R : Type u} [CommRing R] [IsLocalRing R]
    (E : ModuleCat.{u} R) : Prop :=
  ∃ f : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ E,
    InjectiveHull f

/-- The submodule `M[I]` annihilated by an ideal `I`.

This is the canonical `Submodule.torsionBySet` construction from Mathlib. -/
def annihilatorSubmodule {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) : Submodule R M :=
  Submodule.torsionBySet R M (I : Set R)

instance annihilatorSubmodule.moduleQuotient
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) :
    Module (R ⧸ I) (annihilatorSubmodule I M) := by
  exact Module.IsTorsionBySet.module
    (Submodule.torsionBySet_isTorsionBySet
      (R := R) (M := (M : Type u)) (I : Set R))

/-- The `S`-module underlying `E[I]` for a surjection `R → S`.

The quotient action on `E[I]` is supplied by Mathlib, and is transported
along the canonical quotient-kernel equivalence `R / ker(f) ≃+* S`. -/
noncomputable def quotientAnnihilatorModule
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    ModuleCat.{u} S := by
  let e : R ⧸ RingHom.ker f ≃+* S :=
    f.quotientKerEquivOfSurjective hf
  letI : Module S (annihilatorSubmodule (RingHom.ker f) M) :=
    Module.compHom _ e.symm.toRingHom
  exact ModuleCat.of S (annihilatorSubmodule (RingHom.ker f) M)

/-- A surjective local map carries the injective hull of the source residue
field to the injective hull of the target residue field by `E ↦ E[ker(f)]`. -/
theorem quotient_injective_hull
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f)
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    IsResidueFieldInjectiveHull (quotientAnnihilatorModule f hf E) := by
  sorry

/-! ## Powers of the maximal ideal -/

/-- The submodule annihilated by the `n`-th power of the maximal ideal. -/
def maximalIdealPowerTorsionSubmodule
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M
    (↑((IsLocalRing.maximalIdeal R) ^ n) : Set R)

instance maximalIdealPowerTorsionSubmodule.moduleQuotient
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    Module (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)
      (maximalIdealPowerTorsionSubmodule M n) := by
  exact annihilatorSubmodule.moduleQuotient
    ((IsLocalRing.maximalIdeal R) ^ n) M

/-- Every element is annihilated by some power of the maximal ideal. -/
def IsMaximalIdealPowerTorsion
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ∀ x : M, ∃ n : ℕ, x ∈ maximalIdealPowerTorsionSubmodule M n

/-- The socle `M[𝔪]` of a module over a local ring. -/
def socleSubmodule
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : Submodule R M :=
  Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R)

instance socleSubmodule.moduleResidueField
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) :
    Module (IsLocalRing.ResidueField R) (socleSubmodule M) := by
  exact annihilatorSubmodule.moduleQuotient
    (IsLocalRing.maximalIdeal R) M

/-- The canonical `R / 𝔪^(n+1)`-module used as the `n`-th Artinian stage. -/
def artinianStage
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    ModuleCat.{u} (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) :=
  ModuleCat.of _ (maximalIdealPowerTorsionSubmodule M (n + 1))

/-- The underlying module of an Artinian stage is, by construction, `M[𝔪^(n+1)]`. -/
theorem artinianStage_underlying_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    (artinianStage M n : Type u) =
      maximalIdealPowerTorsionSubmodule M (n + 1) := by
  simp [artinianStage]

/-- The quotient by a positive power of the maximal ideal is local. -/
theorem maximalIdeal_power_quotient_is_local
    {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ) :
    IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := by
  sorry

/-- A maximal-ideal-power-torsion module embeds in a finite sum of copies of
an injective hull when its socle is finite-dimensional. -/
theorem torsion_submodule_sum_injective_hulls
    {R : Type u} [CommRing R] [IsLocalRing R]
    (E M : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E)
    (hM : IsMaximalIdealPowerTorsion M)
    (hsocle : Module.Finite (IsLocalRing.ResidueField R)
      (socleSubmodule M : Type u)) :
    ∃ n : ℕ, ∃ f : (M : Type u) →ₗ[R] (Fin n → (E : Type u)),
      Function.Injective f := by
  sorry

/-- The injective hull is the union of its Artinian stages, and each stage is
the corresponding injective hull over the quotient ring. -/
theorem injective_hull_union_artinian
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    (∀ n : ℕ,
      @IsResidueFieldInjectiveHull
        (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
        _ (maximalIdeal_power_quotient_is_local n) (artinianStage E n)) ∧
      (⊤ : Submodule R E) =
        ⨆ n : ℕ, maximalIdealPowerTorsionSubmodule E (n + 1) := by
  sorry

/-! ## Comparison and endomorphisms -/

/-- A flat local map with unchanged residue field identifies the two residue
field injective hulls after restricting scalars. -/
theorem compare_injective_hulls
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f] (hflat : RingHom.Flat f)
    (hκ : Nonempty
      (IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S))
    (E_R : ModuleCat.{u} R) (E_S : ModuleCat.{u} S)
    (hR : IsResidueFieldInjectiveHull E_R)
    (hS : IsResidueFieldInjectiveHull E_S) :
    Nonempty (E_R ≅ (ModuleCat.restrictScalars f).obj E_S) := by
  sorry

/-- The endomorphism ring of the residue-field injective hull is the adic
completion of the local ring. -/
theorem injective_hull_endomorphism_ring_equiv
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    Nonempty
      (Module.End R (E : Type u) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

/-- The residue-field injective hull satisfies the descending chain condition. -/
theorem injective_hull_is_artinian
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    IsArtinian R (E : Type u) := by
  sorry

/-! ## The two module categories -/

/-- An exact finite free presentation `R^m → R^n → M → 0`. -/
def HasFiniteFreePresentation
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) : Prop :=
  ∃ (m n : ℕ)
    (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (g : (Fin n → R) →ₗ[R] (M : Type u)),
    Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g

/-- A short exact presentation `0 → M → E^n → E^m`. -/
def HasInjectiveHullPresentation
    {R : Type u} [CommRing R] (E M : ModuleCat.{u} R) : Prop :=
  ∃ (n m : ℕ)
    (f : (M : Type u) →ₗ[R] (Fin n → (E : Type u)))
    (g : (Fin n → (E : Type u)) →ₗ[R] (Fin m → (E : Type u))),
    Function.Injective f ∧ LinearMap.range f = LinearMap.ker g

/-- The three equivalent finiteness descriptions for modules over a
Noetherian local ring. -/
theorem noetherian_module_tfae
    {R : Type u} [CommRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R) :
    List.TFAE
      [IsNoetherian R (M : Type u),
       Module.Finite R (M : Type u),
       HasFiniteFreePresentation M] := by
  sorry

/-- The three equivalent descriptions of modules satisfying DCC over a
Noetherian local ring. -/
theorem artinian_module_tfae
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E M : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    List.TFAE
      [IsArtinian R (M : Type u),
       IsMaximalIdealPowerTorsion M ∧
         Module.Finite (IsLocalRing.ResidueField R)
           (socleSubmodule M : Type u),
       HasInjectiveHullPresentation E M] := by
  sorry

/-! ## Matlis duality -/

/-- The Matlis dual `Hom_R(M, E)`. -/
def matlisDual
    {R : Type u} [CommRing R]
    (E M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (M ⟶ E)

/-- Precomposition gives the contravariant action on module morphisms. -/
def matlisDualMap
    {R : Type u} [CommRing R]
    (E : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    matlisDual E N ⟶ matlisDual E M :=
  ModuleCat.ofHom
    { toFun := fun φ => f ≫ φ
      map_add' := by
        intro φ ψ
        simp
      map_smul' := by
        intro r φ
        simp }

/-- The canonical evaluation map into the double Matlis dual. -/
def matlisEvaluation
    {R : Type u} [CommRing R]
    (E M : ModuleCat.{u} R) :
    M ⟶ ModuleCat.of R ((ModuleCat.of R (M ⟶ E)) ⟶ E) :=
  ModuleCat.ofHom
    { toFun := fun x =>
        ModuleCat.ofHom (X := ModuleCat.of R (M ⟶ E)) (Y := E)
          { toFun := fun φ => φ x
            map_add' := by
              intro φ ψ
              change φ x + ψ x = φ x + ψ x
              rfl
            map_smul' := by
              intro r φ
              change (r • (φ : M ⟶ E)) x = r • (φ : M ⟶ E) x
              rfl }
      map_add' := by
        intro x y
        apply ModuleCat.hom_ext
        ext φ
        rw [ModuleCat.hom_add]
        exact φ.hom.map_add x y
      map_smul' := by
        intro r x
        apply ModuleCat.hom_ext
        ext φ
        rw [ModuleCat.hom_smul]
        exact φ.hom.map_smul r x }

/-- A DCC module has finite Matlis dual over a Noetherian local ring. -/
theorem matlis_dual_finite_of_artinian
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E)
    (hM : IsArtinian R (M : Type u)) :
    Module.Finite R (matlisDual E M : Type u) := by
  sorry

/-- A finite module has Artinian Matlis dual over a complete local ring. -/
theorem matlis_dual_artinian_of_finite
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E)
    (hM : Module.Finite R (M : Type u)) :
    IsArtinian R (matlisDual E M : Type u) := by
  sorry

/-- The full subcategory of Artinian (DCC) `R`-modules. -/
abbrev ArtinianModuleCat
    (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} R => IsArtinian R (M : Type u))

/-- The full subcategory of finite (ACC) `R`-modules. -/
abbrev NoetherianModuleCat
    (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} R => Module.Finite R (M : Type u))

/-- The Matlis dual functor, viewed as a functor to the opposite category. -/
noncomputable def matlisDualFunctor
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    ArtinianModuleCat R ⥤ (NoetherianModuleCat R)ᵒᵖ where
  obj M := Opposite.op
    ⟨matlisDual E M.obj, matlis_dual_finite_of_artinian E M.obj hE M.property⟩
  map f := Opposite.op
    (ObjectProperty.homMk (matlisDualMap E f.hom))
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext φ
    change X.obj ⟶ E at φ
    change (𝟙 X.obj : X.obj ⟶ X.obj) ≫ φ = φ
    simp
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext φ
    change Z.obj ⟶ E at φ
    change (f.hom ≫ g.hom) ≫ φ = f.hom ≫ (g.hom ≫ φ)
    simp

/-- Matlis duality is an anti-equivalence between DCC and ACC modules. -/
theorem matlis_duality
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E) :
    ∃ e : ArtinianModuleCat R ≌ (NoetherianModuleCat R)ᵒᵖ,
      e.functor = matlisDualFunctor E hE := by
  sorry

/-- The canonical evaluation map is an isomorphism on either side of Matlis
duality. -/
theorem matlis_evaluation_is_iso
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E)
    (hM : IsArtinian R (M : Type u) ∨ Module.Finite R (M : Type u)) :
    IsIso (matlisEvaluation E M) := by
  sorry

/-! ## The addendum to Matlis duality -/

/-- Finite-module data for the completion acting on a Matlis dual.

The structure records the completion module structure explicitly, so the
chapter statement does not depend on a noncanonical typeclass search. -/
def IsFiniteOverCompletion
    {R : Type u} [CommRing R] [IsLocalRing R]
    (E N : ModuleCat.{u} R) : Prop :=
  ∃ h : Module (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (matlisDual E N : Type u),
    @Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (matlisDual E N : Type u) inferInstance inferInstance h

/-- If `N` is maximal-ideal-power torsion and its Matlis dual is finite over
the completion, then `N` satisfies DCC. -/
theorem matlis_addendum
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E N : ModuleCat.{u} R) (hE : IsResidueFieldInjectiveHull E)
    (hN : IsMaximalIdealPowerTorsion N)
    (hfinite : IsFiniteOverCompletion E N) :
    IsArtinian R (N : Type u) := by
  sorry

end

end Formalization.Books.Dualizing.Unit07
