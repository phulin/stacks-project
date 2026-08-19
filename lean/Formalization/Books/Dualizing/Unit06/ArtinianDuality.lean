import Formalization.Books.Dualizing.Unit05
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Dualizing Complexes, Chapter 6: Duality over Artinian local rings

This file records the definitions and theorem interfaces in the section on
duality over an Artinian local ring.  The proofs are deferred to the proving
stage; the constructions which are canonical at the statement stage are
implemented here.
-/

namespace Formalization.Books.Dualizing.Unit06

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dualizing.Unit05

universe u

noncomputable section

/-! ## Artinian local rings and finite-length modules -/

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/- The following recalled facts are already supplied by Mathlib's
`HopkinsLevitzki` API.  These named wrappers keep the hypotheses from the
source visible at the chapter boundary. -/

/-- An Artinian ring is Noetherian. -/
theorem artinian_local_is_noetherian : IsNoetherianRing R := by
  infer_instance

/-- An Artinian ring has finite length as a module over itself. -/
theorem artinian_local_has_finite_length : IsFiniteLength R R := by
  exact (isArtinianRing_iff_isFiniteLength R).mp (inferInstance : IsArtinianRing R)

/-- Over an Artinian ring, finite modules are exactly the finite-length modules. -/
theorem finite_iff_finite_length
    {M : Type u} [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔ IsFiniteLength R M := by
  sorry

variable [IsLocalRing R]

/-! ## Injective hulls and Matlis duality -/

/-- An `R`-module which is an injective hull of the residue field. -/
def IsInjectiveHull (E : ModuleCat.{u} R) : Prop :=
  ∃ f : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ E,
    Formalization.Books.Dualizing.Unit05.InjectiveHull f

/-- The Matlis dual with respect to an `R`-module `E`. -/
def dual (E M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (M ⟶ E)

/-- Precomposition gives the contravariant action on module morphisms. -/
def dualMap (E : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    dual E N ⟶ dual E M :=
  ModuleCat.ofHom
    { toFun := fun φ => f ≫ φ
      map_add' := by
        intro φ ψ
        simp
      map_smul' := by
        intro r φ
        simp }

/-- The evaluation morphism into the double Matlis dual. -/
def evaluation (E M : ModuleCat.{u} R) :
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
              change (r • φ) x = r • φ x
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

/-- A finite module and its Matlis dual have the same module length. -/
theorem length_dual_eq (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) :
    Module.length R (M : Type u) = Module.length R (dual E M : Type u) := by
  sorry

/-- The injective hull of the residue field is finite over an Artinian local ring. -/
theorem injective_hull_finite (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) : Module.Finite R (E : Type u) := by
  sorry

/-- Dualizing a finite module preserves finite generation. -/
theorem dual_finite (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) :
    Module.Finite R (dual E M : Type u) := by
  sorry

/-- The evaluation morphism is an isomorphism for finite modules. -/
theorem evaluation_is_iso (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) :
    IsIso (evaluation E M) := by
  sorry

/-- The finite module is canonically isomorphic to its double Matlis dual. -/
theorem double_dual_iso (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) :
    Nonempty (M ≅ dual E (dual E M)) := by
  sorry

/-- In particular, the regular module is isomorphic to the endomorphism module of `E`. -/
theorem ring_endomorphism_iso (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) :
    Nonempty (ModuleCat.of R R ≅ dual E E) := by
  sorry

/-! ## The exact anti-equivalence on finite modules -/

/-- The full subcategory of finite `R`-modules. -/
abbrev FiniteModuleCat (R : Type u) [Ring R] :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} R => Module.Finite R (M : Type u))

/-- The duality functor, viewed as a functor to the opposite category. -/
noncomputable def dualFunctor (E : ModuleCat.{u} R) (hE : IsInjectiveHull E) :
    FiniteModuleCat R ⥤ (FiniteModuleCat R)ᵒᵖ where
  obj M := Opposite.op
    ⟨dual E M.obj, dual_finite E M.obj hE M.property⟩
  map f := Opposite.op
    (CategoryTheory.ObjectProperty.homMk (dualMap E f.hom))
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext φ
    change X.obj ⟶ E at φ
    change (𝟙 X.obj : X.obj ⟶ X.obj) ≫ φ = φ
    simp
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext φ
    change Z.obj ⟶ E at φ
    change (f.hom ≫ g.hom) ≫ φ = f.hom ≫ (g.hom ≫ φ)
    simp

/-- The duality functor is an anti-equivalence of finite modules. -/
theorem dualFunctor_is_antiequivalence (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) :
    ∃ e : FiniteModuleCat R ≌ (FiniteModuleCat R)ᵒᵖ,
      e.functor = dualFunctor E hE := by
  sorry

/-- The duality functor is exact, with exactness understood in the opposite category. -/
theorem dualFunctor_is_exact (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) :
    PreservesFiniteLimits (dualFunctor E hE) ∧
      PreservesFiniteColimits (dualFunctor E hE) := by
  sorry

/-- The double dual functor is naturally isomorphic to the identity. -/
theorem dualFunctor_double_is_identity (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) :
    Nonempty
      (𝟭 (FiniteModuleCat R) ≅
        dualFunctor E hE ⋙ (dualFunctor E hE).leftOp) := by
  sorry

/-! ## Torsion and cotorsion -/

/-- The submodule `M[I]` annihilated by an ideal `I`. -/
def idealTorsion (I : Ideal R) (M : ModuleCat.{u} R) : Submodule R M :=
  Submodule.torsionBySet R M (I : Set R)

/-- The submodule `IM` of a module. -/
def idealMultiple (I : Ideal R) (M : ModuleCat.{u} R) : Submodule R M :=
  I • (⊤ : Submodule R M)

/-- The quotient module `M/IM`. -/
def idealQuotient (I : Ideal R) (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R ((M : Type u) ⧸ idealMultiple I M)

/-- Duality exchanges ideal torsion with quotient by the ideal multiple. -/
theorem dual_idealTorsion_iso (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) (I : Ideal R) :
    Nonempty
      (dual E (ModuleCat.of R (idealTorsion I M)) ≅
        idealQuotient I (dual E M)) := by
  sorry

/-- Duality exchanges quotient by an ideal multiple with ideal torsion. -/
theorem dual_idealQuotient_iso (E M : ModuleCat.{u} R)
    (hE : IsInjectiveHull E) (hM : Module.Finite R (M : Type u)) (I : Ideal R) :
    Nonempty
      (dual E (idealQuotient I M) ≅
        ModuleCat.of R (idealTorsion I (dual E M))) := by
  sorry

/-- The dual of a short exact sequence is short exact in the reverse direction. -/
theorem dual_preserves_short_exact (E : ModuleCat.{u} R)
    (hE : IsInjectiveHull E)
    {M N P : ModuleCat.{u} R}
    (hM : Module.Finite R (M : Type u))
    (hN : Module.Finite R (N : Type u))
    (hP : Module.Finite R (P : Type u))
    (f : M ⟶ N) (g : N ⟶ P)
    (hf : Function.Injective f.hom)
    (hg : Function.Surjective g.hom)
    (hfg : Function.Exact f.hom g.hom) :
    Function.Injective (dualMap E g).hom ∧
      Function.Exact (dualMap E g).hom (dualMap E f).hom ∧
        Function.Surjective (dualMap E f).hom := by
  sorry

end

end Formalization.Books.Dualizing.Unit06
