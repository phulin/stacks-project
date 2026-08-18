import Formalization.Books.Simplicial.Unit05.CosimplicialObjects
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Crystalline Cohomology, Chapter 16: Cosimplicial algebra

This file uses Mathlib's covariant functors out of `SimplexCategory` for
cosimplicial objects.  The module-valued part is recorded explicitly because
the base ring changes with the simplicial degree.
-/

namespace Formalization.Books.Crystalline.Unit16

open CategoryTheory
open scoped _root_.Simplicial TensorProduct

universe u

/-- A cosimplicial commutative ring. -/
abbrev CosimplicialRing := CosimplicialObject CommRingCat

/-- A cosimplicial algebra over a fixed commutative ring. -/
abbrev CosimplicialAlgebra (R : Type u) [CommRing R] :=
  CosimplicialObject (CommAlgCat R)

/-- An ideal in every degree of a cosimplicial ring, stable under all structure maps. -/
structure CosimplicialIdeal (A : CosimplicialRing.{u}) where
  carrier : ∀ n : ℕ, Ideal (A.obj (SimplexCategory.mk n))
  map_mem : ∀ {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    {x : A.obj (SimplexCategory.mk n)}, x ∈ carrier n → A.map f x ∈ carrier m

/-- The source's category of pairs consisting of a commutative ring and a module. -/
structure RingModulePair where
  ring : Type u
  commRing : CommRing ring
  module : Type u
  addCommGroup : AddCommGroup module
  module_structure : Module ring module

attribute [instance] RingModulePair.commRing RingModulePair.addCommGroup
  RingModulePair.module_structure

/-- A morphism of ring-module pairs: the module map is semilinear for the ring map. -/
structure RingModulePairHom (P Q : RingModulePair.{u}) where
  ringHom : P.ring →+* Q.ring
  moduleHom : P.module →+ Q.module
  map_smul' : ∀ (r : P.ring) (x : P.module),
    moduleHom (r • x) = ringHom r • moduleHom x

namespace RingModulePairHom

@[ext]
theorem ext {P Q : RingModulePair.{u}} (f g : RingModulePairHom P Q)
    (hr : f.ringHom = g.ringHom) (hm : f.moduleHom = g.moduleHom) : f = g := by
  cases f
  cases g
  simp only at hr hm ⊢
  cases hr
  cases hm
  rfl

/-- The identity morphism of a ring-module pair. -/
def id (P : RingModulePair.{u}) : RingModulePairHom P P where
  ringHom := RingHom.id P.ring
  moduleHom := AddMonoidHom.id P.module
  map_smul' := by simp

/-- Composition of morphisms of ring-module pairs. -/
def comp {P Q R : RingModulePair.{u}}
    (f : RingModulePairHom P Q) (g : RingModulePairHom Q R) :
    RingModulePairHom P R where
  ringHom := g.ringHom.comp f.ringHom
  moduleHom := g.moduleHom.comp f.moduleHom
  map_smul' := by
    intro r x
    change g.moduleHom (f.moduleHom (r • x)) = _
    rw [f.map_smul', g.map_smul']
    rfl

end RingModulePairHom

instance : Category RingModulePair.{u} where
  Hom := RingModulePairHom
  id := RingModulePairHom.id
  comp f g := RingModulePairHom.comp f g
  id_comp := by
    intro P Q f
    apply RingModulePairHom.ext _ _
    · ext r
      simp [RingModulePairHom.comp, RingModulePairHom.id]
    · ext x
      simp [RingModulePairHom.comp, RingModulePairHom.id]
  comp_id := by
    intro P Q f
    apply RingModulePairHom.ext _ _
    · ext r
      simp [RingModulePairHom.comp, RingModulePairHom.id]
    · ext x
      simp [RingModulePairHom.comp, RingModulePairHom.id]
  assoc := by
    intro P Q R S f g h
    apply RingModulePairHom.ext _ _
    · ext r
      simp [RingModulePairHom.comp]
    · ext x
      simp [RingModulePairHom.comp]

/-- Forget a ring-module pair to its ring. -/
def ringProjection : RingModulePair.{u} ⥤ CommRingCat.{u} where
  obj P := CommRingCat.of P.ring
  map f := CommRingCat.ofHom f.ringHom

/-- A cosimplicial module over `A`, written degreewise with its semilinear maps. -/
structure CosimplicialModule (A : CosimplicialRing.{u}) where
  obj : ℕ → Type u
  addCommGroup : ∀ n, AddCommGroup (obj n)
  module_structure : ∀ n, Module (A.obj (SimplexCategory.mk n)) (obj n)
  map : ∀ {n m : ℕ}, (SimplexCategory.mk n ⟶ SimplexCategory.mk m) →
    (obj n →+ obj m)
  map_smul' : ∀ {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (r : A.obj (SimplexCategory.mk n)) (x : obj n),
    map f (r • x) = A.map f r • map f x
  map_id' : ∀ n, map (𝟙 (SimplexCategory.mk n)) = AddMonoidHom.id (obj n)
  map_comp' : ∀ {n m k : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (g : SimplexCategory.mk m ⟶ SimplexCategory.mk k),
    map (f ≫ g) = (map g).comp (map f)

attribute [instance] CosimplicialModule.addCommGroup CosimplicialModule.module_structure

/-- A homomorphism of cosimplicial modules over the same cosimplicial ring. -/
structure CosimplicialModuleHom {A : CosimplicialRing.{u}}
    (M N : CosimplicialModule.{u} A) where
  app : ∀ n, M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n
  naturality : ∀ {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (x : M.obj n), app m (M.map f x) = N.map f (app n x)

/-- The identity homomorphism, exposed with the source-facing name. -/
def cosimplicialModuleHomId {A : CosimplicialRing.{u}}
    (M : CosimplicialModule.{u} A) : CosimplicialModuleHom M M where
  app := fun n => LinearMap.id
  naturality := by
    intro n m f x
    rfl

/-- Composition of cosimplicial module homomorphisms. -/
def cosimplicialModuleHomComp {A : CosimplicialRing.{u}}
    {M N P : CosimplicialModule.{u} A} (f : CosimplicialModuleHom M N)
    (g : CosimplicialModuleHom N P) : CosimplicialModuleHom M P where
  app := fun n => (g.app n).comp (f.app n)
  naturality := by
    intro n m h x
    change g.app m (f.app m (M.map h x)) = P.map h (g.app n (f.app n x))
    rw [f.naturality, g.naturality]

/-- A homotopy between two homomorphisms of cosimplicial modules.

The component indexed by `α : [n] ⟶ [1]` is the corresponding `A_n`-linear
map `M_n ⟶ N_n`.  The endpoint convention follows the source: `0` gives
`ψ` and `1` gives `φ`.
-/
structure CosimplicialModuleHomotopy {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (φ ψ : CosimplicialModuleHom M N) where
  app : ∀ (n : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1),
    M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n
  at_zero : ∀ n,
    app n (SimplexCategory.const (SimplexCategory.mk n)
      (SimplexCategory.mk 1) 0) = ψ.app n
  at_one : ∀ n,
    app n (SimplexCategory.const (SimplexCategory.mk n)
      (SimplexCategory.mk 1) 1) = φ.app n
  naturality : ∀ {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk 1) (x : M.obj n),
    app m α (M.map f x) = N.map f (app n (f ≫ α) x)

/-- The degree-`n` component of a homotopy, viewed as one linear map into the
product indexed by the `n`-simplices of `Δ[1]`. -/
def CosimplicialModuleHomotopy.degreeMap {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A}
    {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopy φ ψ) (n : ℕ) :
    M.obj n →ₗ[A.obj (SimplexCategory.mk n)]
      (∀ α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1, N.obj n) where
  toFun x α := h.app n α x
  map_add' x y := by
    funext α
    exact (h.app n α).map_add x y
  map_smul' r x := by
    funext α
    exact (h.app n α).map_smul r x

/-- Homotopy of cosimplicial module homomorphisms. -/
def CosimplicialModuleHomotopic {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (φ ψ : CosimplicialModuleHom M N) : Prop :=
  Nonempty (CosimplicialModuleHomotopy φ ψ)

/-!
The remaining source assertions are recorded through functorial operation
interfaces.  This keeps the theorem statements independent of choices of
models for tensor products, exterior powers, base change, and completions.
-/

/-- A tensor-product operation on cosimplicial modules, with its degreewise
description.  The degreewise description is the source's `⊗_{A_n}`. -/
structure CosimplicialTensorProductOperation (A : CosimplicialRing.{u}) where
  obj : CosimplicialModule.{u} A → CosimplicialModule.{u} A →
    CosimplicialModule.{u} A
  map : ∀ {M N L : CosimplicialModule.{u} A},
    CosimplicialModuleHom M N →
      CosimplicialModuleHom (obj M L) (obj N L)
  degreeIso : ∀ (M L : CosimplicialModule.{u} A) (n : ℕ),
    (obj M L).obj n ≃ₗ[A.obj (SimplexCategory.mk n)]
      TensorProduct (A.obj (SimplexCategory.mk n)) (M.obj n) (L.obj n)

  map_component : ∀ {M N L : CosimplicialModule.{u} A}
    (φ : CosimplicialModuleHom M N) (n : ℕ),
    (map φ).app n =
      (degreeIso N L n).symm.toLinearMap.comp
        ((TensorProduct.map (φ.app n) LinearMap.id).comp
          (degreeIso M L n).toLinearMap)

/-- The degreewise tensor map induced by a homomorphism. -/
def tensorHomotopyComponent {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopy φ ψ) (L : CosimplicialModule.{u} A)
    (n : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :
    TensorProduct (A.obj (SimplexCategory.mk n)) (M.obj n) (L.obj n) →ₗ[
      A.obj (SimplexCategory.mk n)]
      TensorProduct (A.obj (SimplexCategory.mk n)) (N.obj n) (L.obj n) :=
  TensorProduct.map (h.app n α) LinearMap.id

/-- A homotopy is preserved by tensoring with a cosimplicial module. -/
theorem homotopy_tensor
    {A : CosimplicialRing.{u}} {M N : CosimplicialModule.{u} A}
    {φ ψ : CosimplicialModuleHom M N} (h : CosimplicialModuleHomotopic φ ψ)
    (L : CosimplicialModule.{u} A)
    (T : CosimplicialTensorProductOperation A)
    :
    CosimplicialModuleHomotopic
      (T.map (L := L) φ) (T.map (L := L) ψ) := by
  sorry

/-- An exterior-power operation on cosimplicial modules. -/
structure CosimplicialExteriorPowerOperation (A : CosimplicialRing.{u})
    where
  obj : ℕ → CosimplicialModule.{u} A → CosimplicialModule.{u} A
  map : ∀ {M N : CosimplicialModule.{u} A} (i : ℕ),
    CosimplicialModuleHom M N → CosimplicialModuleHom (obj i M) (obj i N)
  componentMap : ∀ {M N : CosimplicialModule.{u} A} (i n : ℕ),
    (M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) →
      ((obj i M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (obj i N).obj n)
  degreeIso : ∀ (M : CosimplicialModule.{u} A) (i n : ℕ),
    (obj i M).obj n ≃ₗ[A.obj (SimplexCategory.mk n)]
      (⋀[A.obj (SimplexCategory.mk n)]^i (M.obj n))

/-- Homotopy is preserved by an exterior-power operation. -/
theorem homotopy_exterior_power
    {A : CosimplicialRing.{u}} {M N : CosimplicialModule.{u} A}
    {φ ψ : CosimplicialModuleHom M N} (h : CosimplicialModuleHomotopic φ ψ)
    (W : CosimplicialExteriorPowerOperation A) (i : ℕ) :
    CosimplicialModuleHomotopic (W.map i φ) (W.map i ψ) := by
  sorry

/-- The degreewise `∧^i h` component in the source's proof. -/
def exteriorPowerHomotopyComponent {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (W : CosimplicialExteriorPowerOperation A)
    (i n : ℕ) (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (W.obj i M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (W.obj i N).obj n :=
  W.componentMap i n h

/-- A homomorphism of cosimplicial rings. -/
abbrev CosimplicialRingHom (A B : CosimplicialRing.{u}) := A ⟶ B

/-- The degreewise module used by base change. -/
def cosimplicialBaseChangeDegree {A B : CosimplicialRing.{u}}
    (f : CosimplicialRingHom A B) (M : CosimplicialModule.{u} A) (n : ℕ) : Type u :=
  letI : Module (A.obj (SimplexCategory.mk n)) (B.obj (SimplexCategory.mk n)) :=
    Module.compHom (B.obj (SimplexCategory.mk n))
      (f.app (SimplexCategory.mk n)).hom
  TensorProduct (A.obj (SimplexCategory.mk n)) (M.obj n)
    (B.obj (SimplexCategory.mk n))

/-- Base change of a cosimplicial module along a cosimplicial ring map. -/
structure CosimplicialBaseChangeOperation {A B : CosimplicialRing.{u}}
    (f : CosimplicialRingHom A B) where
  obj : CosimplicialModule.{u} A → CosimplicialModule.{u} B
  map : ∀ {M N : CosimplicialModule.{u} A} (φ : CosimplicialModuleHom M N),
    CosimplicialModuleHom (obj M) (obj N)
  degreeEquiv : ∀ (M : CosimplicialModule.{u} A) (n : ℕ),
    (obj M).obj n ≃ cosimplicialBaseChangeDegree f M n
  componentMap : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ),
    (M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) →
      ((obj M).obj n →ₗ[B.obj (SimplexCategory.mk n)] (obj N).obj n)

/-- Homotopy is preserved by base change. -/
theorem homotopy_base_change
    {A B : CosimplicialRing.{u}} (f : CosimplicialRingHom A B)
    {M N : CosimplicialModule.{u} A} {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopic φ ψ)
    (F : CosimplicialBaseChangeOperation f) :
    CosimplicialModuleHomotopic (F.map φ) (F.map ψ) := by
  sorry

/-- The degreewise `h ⊗ 1` component for base change. -/
def baseChangeHomotopyComponent {A B : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} {f : CosimplicialRingHom A B}
    (F : CosimplicialBaseChangeOperation f) (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (F.obj M).obj n →ₗ[B.obj (SimplexCategory.mk n)] (F.obj N).obj n :=
  F.componentMap n h

/-- A chosen completion operation for a cosimplicial ring and ideal. -/
structure CosimplicialCompletionOperation {A : CosimplicialRing.{u}}
    (I : CosimplicialIdeal A) where
  obj : CosimplicialModule.{u} A → CosimplicialModule.{u} A
  map : ∀ {M N : CosimplicialModule.{u} A} (φ : CosimplicialModuleHom M N),
    CosimplicialModuleHom (obj M) (obj N)
  componentMap : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ),
    (M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) →
      ((obj M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (obj N).obj n)

/-- Homotopy is preserved by completion. -/
theorem homotopy_completion
    {A : CosimplicialRing.{u}} (I : CosimplicialIdeal A)
    {M N : CosimplicialModule.{u} A} {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopic φ ψ)
    (F : CosimplicialCompletionOperation I) :
    CosimplicialModuleHomotopic (F.map φ) (F.map ψ) := by
  sorry

/-- The degreewise `h^` component for completion. -/
def completionHomotopyComponent {A : CosimplicialRing.{u}}
    {I : CosimplicialIdeal A} {M N : CosimplicialModule.{u} A}
    (F : CosimplicialCompletionOperation I) (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (F.obj M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (F.obj N).obj n :=
  F.componentMap n h

end Formalization.Books.Crystalline.Unit16
