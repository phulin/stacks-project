import Formalization.Books.Simplicial.Unit05.CosimplicialObjects
import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Logic.Relation

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
map `M_n ⟶ N_n`.  The endpoint convention follows this chapter's proof:
`0` gives `ψ` and `1` gives `φ`.
-/
structure CosimplicialModuleHomotopy {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (φ ψ : CosimplicialModuleHom M N) where
  app : ∀ (n : ℕ) (_α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1),
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
      (∀ (_α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1), N.obj n) where
  toFun x _α := h.app n _α x
  map_add' x y := by
    funext α
    exact (h.app n α).map_add x y
  map_smul' r x := by
    funext α
    exact (h.app n α).map_smul r x

/-- The one-step homotopy relation between cosimplicial module homomorphisms. -/
def CosimplicialModuleOneStepHomotopy {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (φ ψ : CosimplicialModuleHom M N) : Prop :=
  Nonempty (CosimplicialModuleHomotopy φ ψ)

/-- The homotopy relation generated by one-step cosimplicial module homotopies. -/
def CosimplicialModuleHomotopic {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (φ ψ : CosimplicialModuleHom M N) : Prop :=
  Relation.EqvGen (fun φ ψ : CosimplicialModuleHom M N =>
    CosimplicialModuleOneStepHomotopy φ ψ) φ ψ

theorem cosimplicialModuleHomotopic_of_homotopy
    {A : CosimplicialRing.{u}} {M N : CosimplicialModule.{u} A}
    {φ ψ : CosimplicialModuleHom M N} (h : CosimplicialModuleHomotopy φ ψ) :
    CosimplicialModuleHomotopic φ ψ :=
  Relation.EqvGen.rel φ ψ ⟨h⟩

/-- Two degreewise linear maps form a square over a cosimplicial structure map. -/
def CosimplicialModuleDegreeSquare {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} {n m : ℕ}
    (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (u : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (v : M.obj m →ₗ[A.obj (SimplexCategory.mk m)] N.obj m) : Prop :=
  ∀ x, v (M.map f x) = N.map f (u x)

/-!
The remaining source assertions are recorded through functorial operation
interfaces.  This keeps the theorem statements independent of choices of
models for tensor products, exterior powers, base change, and completions.
The interfaces record the degreewise operation and its compatibility with
the induced maps; homotopy preservation remains the content of the chapter's
lemmas rather than an assumption on the operation.

Interface audit for the four homotopy lemmas below: the operation structures
already contain enough data.  A one-step homotopy supplies commuting degree
squares via `CosimplicialModuleHomotopy.naturality`; `map_component` identifies
the endpoints after applying the operation, and `degreewise_naturality` or
`componentMap_naturality` turns those squares into the naturality equation for
the new homotopy.  No preservation-of-homotopy field should be added, since
that would assume the conclusion of the lemmas.

The local declarations cited in the roadmaps are all in
`Formalization/Books/Crystalline/Unit16/CosimplicialAlgebra.lean`;
`Relation.EqvGen` and its constructors are in `Mathlib/Logic/Relation.lean`.
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

  degreewise_naturality : ∀ {M N L : CosimplicialModule.{u} A}
    {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (u : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (v : M.obj m →ₗ[A.obj (SimplexCategory.mk m)] N.obj m),
    CosimplicialModuleDegreeSquare f u v →
      ∀ x, (degreeIso N L m).symm
          (TensorProduct.map v LinearMap.id
            (degreeIso M L m ((obj M L).map f x))) =
        (obj N L).map f ((degreeIso N L n).symm
          (TensorProduct.map u LinearMap.id (degreeIso M L n x)))

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
  /-
  Proof roadmap (trial-checked against this declaration):

  1. Induct on `h`, which is `Relation.EqvGen` from
     `Mathlib/Logic/Relation.lean`.  Use `Relation.EqvGen.refl`, `.symm`, and
     `.trans` directly for those three induction cases; no identity or
     composition law for `T.map` is required.
  2. In the `.rel` case, unpack
     `CosimplicialModuleOneStepHomotopy φ₀ ψ₀` to a witness `h₀`.
     Build a `CosimplicialModuleHomotopy (T.map φ₀) (T.map ψ₀)` whose
     `(n, α)` component is

       `(T.degreeIso _ L n).symm.toLinearMap.comp
          ((tensorHomotopyComponent h₀ L n α).comp
            (T.degreeIso _ L n).toLinearMap)`.

     Here all modules and rings live in universe `u`, and this is an
     `A.obj (SimplexCategory.mk n)`-linear map from `(T.obj _ L).obj n` to
     `(T.obj _ L).obj n` with the source and target inferred from `h₀`.
  3. Prove the endpoint fields with
     `simp only [tensorHomotopyComponent, h₀.at_zero, T.map_component]` and
     the analogous `at_one` statement.
  4. For `f : mk n ⟶ mk m`, `α : mk m ⟶ mk 1`, and `x`, apply
     `T.degreewise_naturality f (h₀.app n (f ≫ α)) (h₀.app m α)`.
     Its square premise is exactly `h₀.naturality f α`, and evaluating
     the result at `x` is definitionally the required naturality field.
  5. Wrap the constructed homotopy in `Nonempty`, then in
     `Relation.EqvGen.rel`.  The other induction cases finish the generated
     equivalence relation as described in step 1.

  All local declarations named here are in this file.  In particular, trying
  to handle only the one-step witness is insufficient: the input relation is
  the reflexive, symmetric, transitive closure and must be eliminated by the
  `EqvGen` induction.
  -/
  induction h with
  | rel φ₀ ψ₀ h₀ =>
      rcases h₀ with ⟨h₀⟩
      apply Relation.EqvGen.rel
      refine ⟨{
        app := fun n α =>
          (T.degreeIso N L n).symm.toLinearMap.comp
            ((tensorHomotopyComponent h₀ L n α).comp
              (T.degreeIso M L n).toLinearMap)
        at_zero := ?_
        at_one := ?_
        naturality := ?_
      }⟩
      · intro n
        simp only [tensorHomotopyComponent, h₀.at_zero, T.map_component]
      · intro n
        simp only [tensorHomotopyComponent, h₀.at_one, T.map_component]
      · intro n m f α x
        exact T.degreewise_naturality f (h₀.app n (f ≫ α)) (h₀.app m α)
          (h₀.naturality f α) x
  | refl φ₀ =>
      exact Relation.EqvGen.refl _
  | symm φ₀ ψ₀ h₀ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans φ₀ ψ₀ χ₀ h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- An exterior-power operation on cosimplicial modules. -/
structure CosimplicialExteriorPowerOperation (A : CosimplicialRing.{u})
    where
  obj : ℕ → CosimplicialModule.{u} A → CosimplicialModule.{u} A
  map : ∀ {M N : CosimplicialModule.{u} A} (i : ℕ),
    CosimplicialModuleHom M N → CosimplicialModuleHom (obj i M) (obj i N)
  degreeIso : ∀ (M : CosimplicialModule.{u} A) (i n : ℕ),
    (obj i M).obj n ≃ₗ[A.obj (SimplexCategory.mk n)]
      (⋀[A.obj (SimplexCategory.mk n)]^i (M.obj n))
  map_component : ∀ {M N : CosimplicialModule.{u} A} (i : ℕ)
    (φ : CosimplicialModuleHom M N) (n : ℕ),
    (map i φ).app n =
      (degreeIso N i n).symm.toLinearMap.comp
        ((exteriorPower.map i (φ.app n)).comp
          (degreeIso M i n).toLinearMap)

  degreewise_naturality : ∀ {M N : CosimplicialModule.{u} A}
    (i : ℕ) {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (u : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (v : M.obj m →ₗ[A.obj (SimplexCategory.mk m)] N.obj m),
    CosimplicialModuleDegreeSquare f u v →
      ∀ x, (degreeIso N i m).symm
          (exteriorPower.map i v
            (degreeIso M i m ((obj i M).map f x))) =
        (obj i N).map f ((degreeIso N i n).symm
          (exteriorPower.map i u (degreeIso M i n x)))

/-- Homotopy is preserved by an exterior-power operation. -/
theorem homotopy_exterior_power
    {A : CosimplicialRing.{u}} {M N : CosimplicialModule.{u} A}
    {φ ψ : CosimplicialModuleHom M N} (h : CosimplicialModuleHomotopic φ ψ)
    (W : CosimplicialExteriorPowerOperation A) (i : ℕ) :
    CosimplicialModuleHomotopic (W.map i φ) (W.map i ψ) := by
  /-
  Proof roadmap (trial-checked against this declaration):

  1. Induct on the `Relation.EqvGen` witness `h` exactly as for
     `homotopy_tensor`, using the constructors from
     `Mathlib/Logic/Relation.lean` for the reflexive, symmetric, and transitive
     cases.
  2. In the `.rel` case, unpack the `Nonempty` one-step witness to `h₀` and
     define a `CosimplicialModuleHomotopy (W.map i φ₀) (W.map i ψ₀)`.
     Its component in degree `n` at `α` is the
     `A.obj (SimplexCategory.mk n)`-linear map

       `(W.degreeIso _ i n).symm.toLinearMap.comp
          ((exteriorPower.map i (h₀.app n α)).comp
            (W.degreeIso _ i n).toLinearMap)`.

     This is the body of `exteriorPowerHomotopyComponent` below, but that
     declaration occurs after this theorem and is therefore unavailable here;
     inline the displayed term rather than referring forward to it.
  3. The endpoints close with
     `simp only [h₀.at_zero, W.map_component]` and the corresponding
     `at_one` simplification.
  4. The naturality field is exactly
     `W.degreewise_naturality i f (h₀.app n (f ≫ α)) (h₀.app m α)
       (h₀.naturality f α) x`.
     The universe remains `u`, and both exterior-power degrees are modules
     over `A.obj (SimplexCategory.mk n)` or `A.obj (SimplexCategory.mk m)` as
     dictated by the indices.
  5. Package the homotopy into the one-step `Nonempty`, introduce it with
     `Relation.EqvGen.rel`, and assemble the remaining three induction cases
     with `.refl`, `.symm`, and `.trans`.
  -/
  induction h with
  | rel φ₀ ψ₀ h₀ =>
      rcases h₀ with ⟨h₀⟩
      apply Relation.EqvGen.rel
      refine ⟨{
        app := fun n α =>
          (W.degreeIso N i n).symm.toLinearMap.comp
            ((exteriorPower.map i (h₀.app n α)).comp
              (W.degreeIso M i n).toLinearMap)
        at_zero := ?_
        at_one := ?_
        naturality := ?_
      }⟩
      · intro n
        simp only [h₀.at_zero, W.map_component]
      · intro n
        simp only [h₀.at_one, W.map_component]
      · intro n m f α x
        exact W.degreewise_naturality i f (h₀.app n (f ≫ α)) (h₀.app m α)
          (h₀.naturality f α) x
  | refl φ₀ =>
      exact Relation.EqvGen.refl _
  | symm φ₀ ψ₀ h₀ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans φ₀ ψ₀ χ₀ h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The degreewise `∧^i h` component in the source's proof. -/
noncomputable def exteriorPowerHomotopyComponent {A : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} (W : CosimplicialExteriorPowerOperation A)
    (i n : ℕ) (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (W.obj i M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (W.obj i N).obj n :=
  (W.degreeIso N i n).symm.toLinearMap.comp
    ((exteriorPower.map i h).comp (W.degreeIso M i n).toLinearMap)

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
  map : ∀ {M N : CosimplicialModule.{u} A} (_φ : CosimplicialModuleHom M N),
    CosimplicialModuleHom (obj M) (obj N)
  degreeEquiv : ∀ (M : CosimplicialModule.{u} A) (n : ℕ),
    (obj M).obj n ≃
      cosimplicialBaseChangeDegree f M n
  componentMap : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ),
    (M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) →
      ((obj M).obj n →ₗ[B.obj (SimplexCategory.mk n)] (obj N).obj n)
  map_component : ∀ {M N : CosimplicialModule.{u} A}
    (φ : CosimplicialModuleHom M N) (n : ℕ),
    (map φ).app n = componentMap n (φ.app n)
  componentMap_formula : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (x : (obj M).obj n),
    letI : Module (A.obj (SimplexCategory.mk n)) (B.obj (SimplexCategory.mk n)) :=
      Module.compHom (B.obj (SimplexCategory.mk n))
        (f.app (SimplexCategory.mk n)).hom
    degreeEquiv N n (componentMap n h x) =
      TensorProduct.map h LinearMap.id (degreeEquiv M n x)

  componentMap_naturality : ∀ {M N : CosimplicialModule.{u} A}
    {n m : ℕ} (g : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (u : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (v : M.obj m →ₗ[A.obj (SimplexCategory.mk m)] N.obj m),
    CosimplicialModuleDegreeSquare g u v →
      ∀ x, componentMap m v ((obj M).map g x) =
        (obj N).map g (componentMap n u x)

/-- Homotopy is preserved by base change. -/
theorem homotopy_base_change
    {A B : CosimplicialRing.{u}} (f : CosimplicialRingHom A B)
    {M N : CosimplicialModule.{u} A} {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopic φ ψ)
    (F : CosimplicialBaseChangeOperation f) :
    CosimplicialModuleHomotopic (F.map φ) (F.map ψ) := by
  /-
  Proof roadmap (trial-checked against this declaration):

  1. Induct on `h : Relation.EqvGen _ φ ψ`.  The `.refl`, `.symm`, and
     `.trans` branches map directly to the same constructors of the target
     `CosimplicialModuleHomotopic` relation.
  2. In the `.rel` branch, unpack the one-step witness to `h₀` and construct
     `CosimplicialModuleHomotopy (F.map φ₀) (F.map ψ₀)` with

       `app := fun n α => F.componentMap n (h₀.app n α)`.

     Although `h₀.app n α` is linear over
     `A.obj (SimplexCategory.mk n)`, `F.componentMap` returns precisely the
     required map linear over `B.obj (SimplexCategory.mk n)` between the
     degree-`n` objects of `F.obj`; both rings and modules are in universe `u`.
  3. Establish the endpoints using
     `simp only [h₀.at_zero, F.map_component]` and its `at_one` analogue.
  4. For the naturality field use
     `F.componentMap_naturality g (h₀.app n (g ≫ α)) (h₀.app m α)
       (h₀.naturality g α) x`.
     This is exactly the target equality after unfolding the chosen `app`.
     Neither `degreeEquiv` nor `componentMap_formula` is needed: those fields
     identify the concrete tensor-product model, while naturality is already
     exposed by `componentMap_naturality`.
  5. Wrap the result in `Nonempty` and `Relation.EqvGen.rel`, then finish the
     generated-relation induction with the constructors from
     `Mathlib/Logic/Relation.lean`.
  -/
  induction h with
  | rel φ₀ ψ₀ h₀ =>
      rcases h₀ with ⟨h₀⟩
      apply Relation.EqvGen.rel
      refine ⟨{
        app := fun n α => F.componentMap n (h₀.app n α)
        at_zero := ?_
        at_one := ?_
        naturality := ?_
      }⟩
      · intro n
        simp only [F.map_component, h₀.at_zero]
      · intro n
        simp only [F.map_component, h₀.at_one]
      · intro n m g α x
        exact F.componentMap_naturality g (h₀.app n (g ≫ α)) (h₀.app m α)
          (h₀.naturality g α) x
  | refl φ₀ =>
      exact Relation.EqvGen.refl _
  | symm φ₀ ψ₀ h₀ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans φ₀ ψ₀ χ₀ h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The degreewise `h ⊗ 1` component for base change. -/
def baseChangeHomotopyComponent {A B : CosimplicialRing.{u}}
    {M N : CosimplicialModule.{u} A} {f : CosimplicialRingHom A B}
    (F : CosimplicialBaseChangeOperation f) (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (F.obj M).obj n →ₗ[B.obj (SimplexCategory.mk n)] (F.obj N).obj n :=
  F.componentMap n h

/-- A chosen completion operation for a cosimplicial ring and ideal. -/
abbrev cosimplicialCompletionDegree {A : CosimplicialRing.{u}}
    (I : CosimplicialIdeal A) (M : CosimplicialModule.{u} A) (n : ℕ) : Type u :=
  Formalization.Books.Algebra.Unit96.completion (I.carrier n) (M.obj n)

/-- A completion operation whose degreewise models are the established adic
completion and whose maps are the corresponding induced maps. -/
structure CosimplicialCompletionOperation {A : CosimplicialRing.{u}}
    (I : CosimplicialIdeal A) where
  obj : CosimplicialModule.{u} A → CosimplicialModule.{u} A
  map : ∀ {M N : CosimplicialModule.{u} A} (_φ : CosimplicialModuleHom M N),
    CosimplicialModuleHom (obj M) (obj N)
  degreeEquiv : ∀ (M : CosimplicialModule.{u} A) (n : ℕ),
    (obj M).obj n ≃ₗ[A.obj (SimplexCategory.mk n)]
      cosimplicialCompletionDegree I M n
  componentMap : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ),
    (M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) →
      ((obj M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (obj N).obj n)
  map_component : ∀ {M N : CosimplicialModule.{u} A}
    (φ : CosimplicialModuleHom M N) (n : ℕ),
    (map φ).app n = componentMap n (φ.app n)
  componentMap_formula : ∀ {M N : CosimplicialModule.{u} A} (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (x : (obj M).obj n),
    degreeEquiv N n (componentMap n h x) =
      Formalization.Books.Algebra.Unit96.completionMap (I.carrier n) h
        (degreeEquiv M n x)

  componentMap_naturality : ∀ {M N : CosimplicialModule.{u} A}
    {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (u : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n)
    (v : M.obj m →ₗ[A.obj (SimplexCategory.mk m)] N.obj m),
    CosimplicialModuleDegreeSquare f u v →
      ∀ x, componentMap m v ((obj M).map f x) =
        (obj N).map f (componentMap n u x)

/-- Homotopy is preserved by completion. -/
theorem homotopy_completion
    {A : CosimplicialRing.{u}} (I : CosimplicialIdeal A)
    {M N : CosimplicialModule.{u} A} {φ ψ : CosimplicialModuleHom M N}
    (h : CosimplicialModuleHomotopic φ ψ)
    (F : CosimplicialCompletionOperation I) :
    CosimplicialModuleHomotopic (F.map φ) (F.map ψ) := by
  /-
  Proof roadmap (trial-checked against this declaration):

  1. Eliminate `h` by induction on `Relation.EqvGen` (defined in
     `Mathlib/Logic/Relation.lean`).  Transport `.refl`, `.symm`, and `.trans`
     with the corresponding target constructors.
  2. In the `.rel` case, unpack the `Nonempty` homotopy witness to `h₀` and
     build `CosimplicialModuleHomotopy (F.map φ₀) (F.map ψ₀)` using

       `app := fun n α => F.componentMap n (h₀.app n α)`.

     At universe `u`, `F.componentMap` has exactly the required
     `A.obj (SimplexCategory.mk n)`-linear source and target; no coercion
     through the underlying completion type is needed.
  3. The zero and one endpoint fields follow from
     `simp only [h₀.at_zero, F.map_component]` and
     `simp only [h₀.at_one, F.map_component]`.
  4. Supply naturality with
     `F.componentMap_naturality g (h₀.app n (g ≫ α)) (h₀.app m α)
       (h₀.naturality g α) x`.
     As for base change, `degreeEquiv` and `componentMap_formula` only describe
     the concrete completion model and are unnecessary for this square.
  5. Package the new homotopy as a one-step relation, apply
     `Relation.EqvGen.rel`, and complete the outer induction using `.refl`,
     `.symm`, and `.trans`.

  `completionHomotopyComponent` below is merely the same `componentMap`
  wrapper and is declared too late to use here; the displayed `app` avoids a
  forward reference.
  -/
  induction h with
  | rel φ₀ ψ₀ h₀ =>
      rcases h₀ with ⟨h₀⟩
      apply Relation.EqvGen.rel
      refine ⟨{
        app := fun n α => F.componentMap n (h₀.app n α)
        at_zero := ?_
        at_one := ?_
        naturality := ?_
      }⟩
      · intro n
        simp only [F.map_component, h₀.at_zero]
      · intro n
        simp only [F.map_component, h₀.at_one]
      · intro n m g α x
        exact F.componentMap_naturality g (h₀.app n (g ≫ α)) (h₀.app m α)
          (h₀.naturality g α) x
  | refl φ₀ =>
      exact Relation.EqvGen.refl _
  | symm φ₀ ψ₀ h₀ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans φ₀ ψ₀ χ₀ h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The degreewise `h^` component for completion. -/
def completionHomotopyComponent {A : CosimplicialRing.{u}}
    {I : CosimplicialIdeal A} {M N : CosimplicialModule.{u} A}
    (F : CosimplicialCompletionOperation I) (n : ℕ)
    (h : M.obj n →ₗ[A.obj (SimplexCategory.mk n)] N.obj n) :
    (F.obj M).obj n →ₗ[A.obj (SimplexCategory.mk n)] (F.obj N).obj n :=
  F.componentMap n h

end Formalization.Books.Crystalline.Unit16
