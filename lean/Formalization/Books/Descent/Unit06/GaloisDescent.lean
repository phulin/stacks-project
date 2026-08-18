import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent, §6: Galois descent for quasi-coherent sheaves

This file formalizes the precise constructions and theorem interfaces in the
source section.  Proofs of the descent equivalences are deferred to the
proof stage.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

open scoped AlgebraicGeometry TensorProduct

universe u

namespace Scheme

/-- The morphism of affine schemes induced by a `k`-algebra `A`. -/
noncomputable def spectrumMapOfAlgebra {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] :
    Spec (.of A) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- Base change of a scheme over `k` along the `k`-algebra `A`. -/
noncomputable def baseChange {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) : Scheme :=
  pullback x (spectrumMapOfAlgebra (k := k) (A := A))

/-- The projection from a base change to the original scheme. -/
noncomputable def baseChangeProjection {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) :
    baseChange (A := A) x ⟶ X :=
  pullback.fst x (spectrumMapOfAlgebra (k := k) (A := A))

/-- The two-fold Čech intersection of the base change. -/
noncomputable def baseChangeSelfIntersection {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) : Scheme :=
  pullback (baseChangeProjection (A := A) x) (baseChangeProjection (A := A) x)

/-- The three-fold Čech intersection of the base change. -/
noncomputable def baseChangeTripleIntersection {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) : Scheme :=
  let p := baseChangeProjection (A := A) x
  pullback (pullback.fst p p ≫ p) p

/-- The standard affine base-change calculation for the two-fold intersection. -/
theorem exists_baseChangeSelfIntersectionIso {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) :
    Nonempty (baseChangeSelfIntersection (A := A) x ≅
      baseChange x (A := TensorProduct k A A)) := by
  sorry

/-- The standard affine base-change calculation for the three-fold intersection. -/
theorem exists_baseChangeTripleIntersectionIso {X : Scheme.{u}} {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : X ⟶ Spec (.of k)) :
    Nonempty (baseChangeTripleIntersection (A := A) x ≅
      baseChange x (A := TensorProduct k (TensorProduct k A A) A)) := by
  sorry

/-- A field extension gives an fpqc singleton cover of the base affine scheme. -/
theorem fieldExtension_mem_fpqcPrecoverage {k k' : Type u}
    [Field k] [Field k'] [Algebra k k'] :
    Presieve.singleton (spectrumMapOfAlgebra (k := k) (A := k')) ∈
      fpqcPrecoverage.coverings (Spec (.of k)) := by
  sorry

/-- Pulling the field-extension cover back to a scheme remains fpqc. -/
theorem fieldBaseChange_mem_fpqcPrecoverage {X : Scheme.{u}} {k k' : Type u}
    [Field k] [Field k'] [Algebra k k'] (x : X ⟶ Spec (.of k)) :
    Presieve.singleton (baseChangeProjection (A := k') x) ∈
      fpqcPrecoverage.coverings X := by
  sorry

end Scheme

/-- The Galois group of a finite Galois extension, in the form used by Lean. -/
abbrev galoisGroup (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :=
  k' ≃ₐ[k] k'

/-- Evaluation of the second tensor factor at every Galois automorphism. -/
def galoisEvaluationAlgHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] (galoisGroup k k' → k') where
  toFun b σ := σ b
  map_one' := by
    ext σ
    simp
  map_mul' a b := by
    ext σ
    simp
  map_zero' := by
    ext σ
    simp
  map_add' a b := by
    ext σ
    simp
  commutes' a := by
    ext σ
    exact σ.commutes a

def galoisConstantAlgHomSingle {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] (galoisGroup k k' → k') where
  toFun a _ := a
  map_one' := by
    ext σ
    simp
  map_mul' a b := by
    ext σ
    simp
  map_zero' := by
    ext σ
    simp
  map_add' a b := by
    ext σ
    simp
  commutes' a := by
    ext σ
    simp

/-- The tensor-product map `a ⊗ b ↦ (σ ↦ a * σ(b))`. -/
def galoisTensorProductHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    TensorProduct k k' k' →ₐ[k] (galoisGroup k k' → k') :=
  Algebra.TensorProduct.lift
    (galoisConstantAlgHomSingle (k := k) (k' := k'))
    (galoisEvaluationAlgHom (k := k) (k' := k'))
    (by
      intro a b
      ext σ
      simp [mul_comm])

@[simp]
theorem galoisTensorProductHom_tmul {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] (a b : k') :
    galoisTensorProductHom (k := k) (k' := k') (a ⊗ₜ[k] b) =
      fun σ => a * σ b := by
  ext σ
  simp [galoisTensorProductHom, Algebra.TensorProduct.lift_tmul,
    galoisConstantAlgHomSingle, galoisEvaluationAlgHom]

/-- The constant map from the first tensor factor to functions on `G × G`. -/
def galoisConstantAlgHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] ((galoisGroup k k' × galoisGroup k k') → k') where
  toFun a _ := a
  map_one' := by
    ext p
    simp
  map_mul' a b := by
    ext p
    simp
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp
  commutes' a := by
    ext p
    simp

/-- Evaluation of the middle tensor factor at the first Galois index. -/
def galoisSecondAlgHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] ((galoisGroup k k' × galoisGroup k k') → k') where
  toFun b p := p.1 b
  map_one' := by
    ext p
    simp
  map_mul' a b := by
    ext p
    simp
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp
  commutes' a := by
    ext p
    exact p.1.commutes a

/-- Evaluation of the last tensor factor at the composite Galois index. -/
def galoisThirdAlgHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] ((galoisGroup k k' × galoisGroup k k') → k') where
  toFun c p := p.1 (p.2 c)
  map_one' := by
    ext p
    simp
  map_mul' a b := by
    ext p
    simp
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp
  commutes' a := by
    ext p
    simp

def galoisInnerTensorProductHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    TensorProduct k k' k' →ₐ[k] ((galoisGroup k k' × galoisGroup k k') → k') :=
  Algebra.TensorProduct.lift
    (galoisConstantAlgHom (k := k) (k' := k'))
    (galoisSecondAlgHom (k := k) (k' := k'))
    (by
      intro a b
      ext p
      simp [mul_comm])

/-- The three-fold tensor-product map with the iterated Galois action. -/
def galoisTripleTensorProductHom {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    TensorProduct k (TensorProduct k k' k') k' →ₐ[k]
      ((galoisGroup k k' × galoisGroup k k') → k') :=
  Algebra.TensorProduct.lift
    (galoisInnerTensorProductHom (k := k) (k' := k'))
    (galoisThirdAlgHom (k := k) (k' := k'))
    (by
      intro a b
      ext p
      simp [mul_comm])

@[simp]
theorem galoisTripleTensorProductHom_tmul {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] (a b c : k') :
    galoisTripleTensorProductHom (k := k) (k' := k') ((a ⊗ₜ[k] b) ⊗ₜ[k] c) =
      fun p => a * p.1 b * p.1 (p.2 c) := by
  ext p
  simp [galoisTripleTensorProductHom, galoisInnerTensorProductHom,
    Algebra.TensorProduct.lift_tmul, galoisConstantAlgHom,
    galoisSecondAlgHom, galoisThirdAlgHom]

/-- The tensor-product maps are the finite Galois decompositions. -/
theorem galoisTensorProductHom_bijective {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    Function.Bijective (galoisTensorProductHom (k := k) (k' := k')) := by
  sorry

theorem galoisTripleTensorProductHom_bijective {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    Function.Bijective (galoisTripleTensorProductHom (k := k) (k' := k')) := by
  sorry

theorem exists_galoisTensorProductAlgEquiv {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    Nonempty (TensorProduct k k' k' ≃ₐ[k] (galoisGroup k k' → k')) := by
  exact ⟨AlgEquiv.ofBijective _ (galoisTensorProductHom_bijective (k := k) (k' := k'))⟩

theorem exists_galoisTripleTensorProductAlgEquiv {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k'] :
    Nonempty (TensorProduct k (TensorProduct k k' k') k' ≃ₐ[k]
      (galoisGroup k k' × galoisGroup k k' → k')) := by
  exact ⟨AlgEquiv.ofBijective _
    (galoisTripleTensorProductHom_bijective (k := k) (k' := k'))⟩

end AlgebraicGeometry
