import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Prod
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products

import Formalization.Books.Exercises.Unit04.Core

/-!
# Exercises, Chapter 4: Tensor product

This file contains the declarations for the four numbered parts of
`exercise-characterize-tensor-functor`.  Proposition proofs are intentionally
left for the prove stage; the functors and examples themselves are defined
explicitly.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace Formalization.Books.Exercises.Unit04

/-! ## (1) An additive functor which is not `R`-linear -/

/-- The product ring used for the non-`R`-linear additive example. -/
abbrev exampleRing : Type := ℤ × ℤ

/-- The ring automorphism which swaps the two components of `exampleRing`. -/
def exampleRingSwap : exampleRing ≃+* exampleRing :=
  RingEquiv.prodComm (R := ℤ) (S := ℤ)

/-- Restriction of scalars along the component swap. -/
def exampleAdditiveFunctor :
    ModuleCat exampleRing ⥤ ModuleCat exampleRing :=
  ModuleCat.restrictScalars exampleRingSwap.toRingHom

/-- The restriction-of-scalars example is additive but not linear over the
original product ring. -/
theorem additive_not_R_linear_example :
    exampleAdditiveFunctor.Additive ∧
      ¬ Functor.Linear exampleRing exampleAdditiveFunctor := by
  refine ⟨{ map_add := by intros; rfl }, ?_⟩
  intro h
  have h' := (Functor.linear_iff exampleRing exampleAdditiveFunctor).mp h
  let X := ModuleCat.of exampleRing (ULift exampleRing)
  have hx := h' X ((1, 0) : exampleRing)
  have hx' := congrArg (fun f => f (ULift.up ((1, 0) : exampleRing))) hx
  change ULift.up ((1, 0) : exampleRing) = ULift.up ((0, 0) : exampleRing) at hx'
  exact (by norm_num : ((1, 0) : exampleRing) ≠ (0, 0)) (ULift.up.inj hx')

/-! ## (2) Tensoring with a fixed module -/

/-- The canonical functor `M ↦ M ⊗_R N`, namely right tensoring in the
monoidal category of `R`-modules. -/
noncomputable def tensorProductFunctor
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  CategoryTheory.MonoidalCategory.tensorRight N

/-- Tensoring with `N` is `R`-linear in the source's bundled sense. -/
theorem tensorProductFunctor_is_R_linear
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    IsRLinearFunctor (tensorProductFunctor N) := by
  unfold IsRLinearFunctor tensorProductFunctor
  exact ⟨CategoryTheory.tensorRight_additive N, CategoryTheory.tensorRight_linear R N⟩

/-- Tensoring with `N` is right exact. -/
theorem tensorProductFunctor_is_right_exact
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    PreservesFiniteColimits (tensorProductFunctor N) := by
  unfold tensorProductFunctor
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  exact CategoryTheory.MonoidalCategory.Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left K N

/-- Tensoring with `N` commutes with arbitrary direct sums. -/
theorem tensorProductFunctor_commutes_with_direct_sums
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    CommutesWithDirectSums (tensorProductFunctor N) := by
  unfold CommutesWithDirectSums tensorProductFunctor
  intro ι M
  infer_instance

/-! ## (3) The converse characterization -/

/-- A source-faithful formulation of the Eilenberg--Watts characterization.
The phrase “is of the form” is represented by a natural isomorphism of
functors, since categorical functors are determined only up to isomorphism. -/
theorem exists_tensorProductFunctor_iso
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (hF : IsRLinearFunctor F)
    (hRight : PreservesFiniteColimits F)
    (hSums : CommutesWithDirectSums F) :
    ∃ N : ModuleCat.{u} R, Nonempty (F ≅ tensorProductFunctor N) := by
  sorry

/-! ## (4) Why direct sums cannot be omitted -/

/-- The countable product endofunctor on abelian groups, written directly on
objects and morphisms. -/
def infiniteProductFunctor :
    ModuleCat ℤ ⥤ ModuleCat ℤ where
  obj M := ModuleCat.of ℤ (ℕ → M)
  map {M N} f :=
    ModuleCat.ofHom (X := ModuleCat.of ℤ (ℕ → M))
      (Y := ModuleCat.of ℤ (ℕ → N))
      { toFun := fun x n => f.hom (x n)
        map_add' := by
          intro x y
          funext n
          exact f.hom.map_add (x n) (y n)
        map_smul' := by
          intro r x
          funext n
          simp }
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext x n
    rfl
  map_comp := by
    intro M N P f g
    apply ModuleCat.hom_ext
    ext x n
    rfl

/-- The product functor supplies the requested counterexample after the
direct-sum hypothesis is removed. -/
theorem exists_right_exact_R_linear_not_tensorProductFunctor :
    ∃ F : ModuleCat ℤ ⥤ ModuleCat ℤ,
      IsRLinearFunctor F ∧
        PreservesFiniteColimits F ∧
          ¬ CommutesWithDirectSums F ∧
            ¬ ∃ N : ModuleCat ℤ, Nonempty (F ≅ tensorProductFunctor N) := by
  refine ⟨infiniteProductFunctor, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · refine { map_add := ?_ }
      intro X Y f g
      apply ModuleCat.hom_ext
      ext x n
      rfl
    · letI lin : CategoryTheory.Linear ℤ (ModuleCat ℤ) := ModuleCat.instLinear
      refine { map_smul := ?_ }
      intro X Y f r
      letI : Module ℤ (X ⟶ Y) := lin.homModule X Y
      letI : SMul ℤ (X ⟶ Y) :=
        (lin.homModule X Y).toDistribMulAction.toDistribSMul.toSMul
      let zf : X ⟶ Y :=
        @SMul.smul ℤ (X ⟶ Y) ModuleCat.instSMulIntHom r f
      have hscalar :
          (@SMul.smul ℤ (X ⟶ Y) this r f) = zf := by
        exact int_smul_eq_zsmul (lin.homModule X Y) r f
      have hmap (g : X ⟶ Y) (x : infiniteProductFunctor.obj X) (n : ℕ) :
          (infiniteProductFunctor.map g).hom x n = g.hom (x n) := by
        rfl
      apply ModuleCat.hom_ext
      ext x
      funext n
      have hleft := hmap zf x n
      have hright := congrArg (fun q => r • q) (hmap f x n)
      have h₁ := congrArg (fun q => q (x n)) (ModuleCat.hom_zsmul r f)
      have h₂ := congrArg (fun q => q x n)
        (ModuleCat.hom_zsmul r (infiniteProductFunctor.map f))
      have htransport := congrArg
        (fun g : X ⟶ Y => (infiniteProductFunctor.map g).hom x n) hscalar
      exact htransport.trans (hleft.trans (h₁.trans (hright.trans h₂.symm)))
  · let G : ModuleCat ℤ ⥤ ModuleCat ℤ :=
      Functor.const (Discrete ℕ) ⋙ lim
    let H : ModuleCat ℤ ⥤ ModuleCat ℤ :=
      { obj := fun M => ∏ᶜ fun _ : ℕ => M
        map := fun {M N} f => CategoryTheory.Limits.Pi.map (fun _ => f)
        map_id := by
          intro M
          apply ModuleCat.hom_ext
          ext x n
          simp
        map_comp := by
          intro M N P f g
          apply CategoryTheory.Limits.Pi.hom_ext
          intro n
          simp [CategoryTheory.Limits.Pi.map_comp_map] }
    let e : G ≅ H :=
      NatIso.ofComponents (fun M =>
        (piEquivalenceFunctorDiscreteCompLim (C := ModuleCat ℤ) ℕ).app (fun _ => M))
    have hGH : PreservesFiniteColimits G := by infer_instance
    have hH : PreservesFiniteColimits H := by
      exact preservesFiniteColimits_of_natIso e
    have hobj : ∀ M : ModuleCat ℤ,
        @ModuleCat.of ℤ Int.instRing (ℕ → (M : Type)) Pi.addCommGroup
            (Pi.module ℕ (fun _ => (M : Type)) ℤ) = infiniteProductFunctor.obj M := by
      intro M
      congr 1
      apply Subsingleton.elim
    have eqToHom_apply {A B : ModuleCat ℤ} (h : A = B) (x : A) :
        (eqToHom h).hom x = cast (congrArg ModuleCat.carrier h) x := by
      cases h
      rfl
    let q : H ≅ infiniteProductFunctor :=
      NatIso.ofComponents (fun M =>
        (ModuleCat.piIsoPi (fun _ : ℕ => M)).trans (eqToIso (hobj M)))
        (by
          intro X Y f
          letI : Module ℤ (ℕ → (X : Type)) :=
            Pi.module ℕ (fun _ => (X : Type)) ℤ
          letI : Module ℤ (ℕ → (Y : Type)) :=
            Pi.module ℕ (fun _ => (Y : Type)) ℤ
          let k :
              @ModuleCat.of ℤ Int.instRing (ℕ → (X : Type)) Pi.addCommGroup
                  (Pi.module ℕ (fun _ => (X : Type)) ℤ) ⟶
                @ModuleCat.of ℤ Int.instRing (ℕ → (Y : Type)) Pi.addCommGroup
                  (Pi.module ℕ (fun _ => (Y : Type)) ℤ) :=
            ModuleCat.ofHom (LinearMap.piMap (fun _ => f.hom))
          have hp :
              H.map f ≫ (ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom =
                (ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫ k := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            funext n
            have hy := congrArg
              (fun a : (H.obj Y ⟶ Y) => a.hom ((H.map f).hom x))
              (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : ℕ => Y) n)
            have hm := congrArg
              (fun a : (H.obj X ⟶ Y) => a.hom x)
              (CategoryTheory.Limits.Pi.map_π (fun _ : ℕ => f) n)
            have hx := congrArg
              (fun a : (H.obj X ⟶ X) => a.hom x)
              (ModuleCat.piIsoPi_hom_ker_subtype (fun _ : ℕ => X) n)
            have hxf := congrArg (fun z : X => f.hom z) hx.symm
            have hy' :
                ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom.hom
                    ((H.map f).hom x)) n =
                  (Pi.π (fun _ : ℕ => Y) n).hom ((H.map f).hom x) := by
              change ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom ≫
                  ModuleCat.ofHom (LinearMap.proj n)).hom ((H.map f).hom x) = _
              exact hy
            have hx' :
                (Pi.π (fun _ : ℕ => X) n).hom x =
                  ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x) n := by
              change _ = ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫
                  ModuleCat.ofHom (LinearMap.proj n)).hom x
              exact hx.symm
            calc
              ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom.hom
                    ((H.map f).hom x)) n =
                  (Pi.π (fun _ : ℕ => Y) n).hom ((H.map f).hom x) := hy'
              _ = (f.hom ((Pi.π (fun _ : ℕ => X) n).hom x)) := by
                change ((H.map f ≫
                    Pi.π (fun _ : ℕ => Y) n).hom x) =
                  ((Pi.π (fun _ : ℕ => X) n ≫ f).hom x)
                simpa only [H] using hm
              _ = f.hom (((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x) n) := by
                rw [hx']
              _ = (k.hom ((ModuleCat.piIsoPi (fun _ : ℕ => X)).hom.hom x)) n := by
                rfl
          have hk : k = eqToHom (hobj X) ≫ infiniteProductFunctor.map f ≫
              eqToHom (hobj Y).symm := by
            have hcX : congrArg ModuleCat.carrier (hobj X) = rfl :=
              Subsingleton.elim _ _
            have hcY : congrArg ModuleCat.carrier (hobj Y).symm = rfl :=
              Subsingleton.elim _ _
            apply ModuleCat.hom_ext
            ext x n
            simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
            rw [eqToHom_apply, eqToHom_apply, hcX, hcY]
            rfl
          calc
            H.map f ≫ ((ModuleCat.piIsoPi (fun _ : ℕ => Y)).trans
                (eqToIso (hobj Y))).hom =
                H.map f ≫ (ModuleCat.piIsoPi (fun _ : ℕ => Y)).hom ≫
                  eqToHom (hobj Y) := by simp [Iso.trans_hom, Category.assoc]
            _ = (ModuleCat.piIsoPi (fun _ : ℕ => X)).hom ≫ k ≫
                eqToHom (hobj Y) := by
              rw [← Category.assoc, hp]
              simp only [Category.assoc]
            _ = ((ModuleCat.piIsoPi (fun _ : ℕ => X)).trans
                (eqToIso (hobj X))).hom ≫ infiniteProductFunctor.map f := by
              rw [Iso.trans_hom, hk]
              simp only [Category.assoc, eqToIso.hom, eqToHom_trans,
                eqToHom_refl, Category.comp_id]
          )
    letI := hH
    exact preservesFiniteColimits_of_natIso q
  · sorry
  · sorry

end Formalization.Books.Exercises.Unit04
