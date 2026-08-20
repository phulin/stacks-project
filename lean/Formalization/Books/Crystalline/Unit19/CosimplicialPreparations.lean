import Formalization.Books.Crystalline.Unit16.CosimplicialAlgebra
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Crystalline Cohomology, Chapter 19: Cosimplicial preparations

This file records the explicit contractible cosimplicial module used in the
chapter and the source-facing vanishing statements that use it.  The
cosimplicial algebra operations are the interfaces established in Chapter 16.
-/

namespace Formalization.Books.Crystalline.Unit19

open CategoryTheory
open scoped _root_.Simplicial TensorProduct

open Formalization.Books.Crystalline.Unit16

universe u

/-! ## The explicit cosimplicial module -/

/-- The degree-`n` finite direct sum of `A.obj [n]` indexed by the vertices
of `[n]`.  Finitely supported functions are the canonical direct-sum model. -/
abbrev exampleCosimplicialModuleDegree (A : CosimplicialRing.{u}) (n : ℕ) :=
  Fin (n + 1) →₀ A.obj (SimplexCategory.mk n)

/-- The coefficient map associated to a ring homomorphism, regarded as a
semilinear map. -/
def ringHomSemilinear {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) : R →ₛₗ[σ] S where
  toFun := σ
  map_add' := σ.map_add
  map_smul' := by
    intro r x
    exact σ.map_mul r x

/-- The map on the direct-sum model associated to a simplex-category map.
It sends the basis vector in slot `i` to the basis vector in slot `f i`,
and applies the induced ring map to its coefficient. -/
noncomputable def exampleCosimplicialModuleMap {A : CosimplicialRing.{u}}
    {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    exampleCosimplicialModuleDegree A n →ₛₗ[(A.map f).hom]
      exampleCosimplicialModuleDegree A m := by
  letI : Module (A.obj (SimplexCategory.mk n)) (A.obj (SimplexCategory.mk m)) :=
    Module.compHom (A.obj (SimplexCategory.mk m)) (A.map f).hom
  exact
    (Finsupp.mapRange.linearMap (ringHomSemilinear (A.map f).hom)).comp
      (Finsupp.lmapDomain (A.obj (SimplexCategory.mk n))
        (A.obj (SimplexCategory.mk n)) f.toOrderHom)

/-- The cosimplicial module from the chapter's explicit example. -/
noncomputable def exampleCosimplicialModule (A : CosimplicialRing.{u}) :
    CosimplicialModule A where
  obj n := exampleCosimplicialModuleDegree A n
  addCommGroup n := inferInstance
  module_structure n := inferInstance
  map f := (exampleCosimplicialModuleMap f).toAddMonoidHom
  map_smul' f r x := (exampleCosimplicialModuleMap f).map_smulₛₗ r x
  map_id' n := by
    ext x i
    simp [exampleCosimplicialModuleMap, ringHomSemilinear]
    rw [A.map_id]
    rfl
  map_comp' f g := by
    ext x i
    simp [exampleCosimplicialModuleMap, ringHomSemilinear, Function.comp_def]
    rw [A.map_comp]
    rfl

/-- The monotone map `α_j^n : [n] ⟶ [1]` from the source example. -/
def exampleIntervalSimplex (n : ℕ) (j : Fin (n + 2)) :
    SimplexCategory.mk n ⟶ SimplexCategory.mk 1 :=
    SimplexCategory.Hom.mk
    ⟨fun i => if i.val < j.val then 0 else 1, by
      intro i k hik
      change (if i.val < j.val then 0 else 1) ≤
        (if k.val < j.val then 0 else 1)
      split_ifs with hi hk
      · simp
      · simp
      · exfalso
        omega
      · simp⟩

/-- Every simplex of `Δ[1]` is one of the threshold maps `α_j^n`. -/
theorem exampleIntervalSimplex_unique (n : ℕ)
    (α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :
    ∃! j : Fin (n + 2), α = exampleIntervalSimplex n j := by
  sorry

/-- The zero homomorphism between two cosimplicial modules over the same ring. -/
def cosimplicialModuleHomZero {A : CosimplicialRing.{u}}
    (M N : CosimplicialModule.{u} A) : CosimplicialModuleHom M N where
  app n := 0
  naturality := by simp

/-- The degreewise threshold map used for the homotopy in the example. -/
noncomputable def exampleThresholdComponent {A : CosimplicialRing.{u}}
    (n : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :
    exampleCosimplicialModuleDegree A n →ₗ[A.obj (SimplexCategory.mk n)]
      exampleCosimplicialModuleDegree A n := by
  classical
  let p : Fin (n + 1) → Prop := fun i => α.toOrderHom i = 0
  exact
    { toFun := fun x => x.filter p
      map_add' := by
        intro x y
        ext i
        simp [Finsupp.filter_apply]
      map_smul' := by
        intro r x
        ext i
        simp [Finsupp.filter_apply]
        }

/- The formula in the source is recovered on the standard direct-sum basis. -/
theorem exampleThresholdComponent_single {A : CosimplicialRing.{u}} (n : ℕ)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    exampleThresholdComponent (A := A) n (exampleIntervalSimplex n j)
        (Finsupp.single i 1) =
      if i.val < j.val then Finsupp.single i 1 else 0 := by
  classical
  ext k
  change (Finsupp.filter
      (fun x : Fin (n + 1) => (exampleIntervalSimplex n j).toOrderHom x = 0)
      (Finsupp.single i 1)) k = _
  rw [Finsupp.filter_apply]
  by_cases hk : k = i
  · subst k
    have hmap : (exampleIntervalSimplex n j).toOrderHom i =
        (if i.val < j.val then (0 : Fin 2) else 1) := by
      rfl
    rw [hmap]
    by_cases h : i.val < j.val <;>
      simp [Finsupp.single_eq_same, h]
  · by_cases h : i.val < j.val <;>
      simp [Finsupp.single_eq_of_ne hk,
        Finsupp.single_eq_of_ne' (Ne.symm hk), exampleIntervalSimplex, h]

/-- In the explicit homotopy, evaluation at the zero vertex is the identity. -/
theorem exampleThresholdComponent_at_zero {A : CosimplicialRing.{u}} (n : ℕ) :
    exampleThresholdComponent (A := A) n
        (SimplexCategory.const (SimplexCategory.mk n)
          (SimplexCategory.mk 1) 0) = LinearMap.id := by
  classical
  ext x i
  simp [exampleThresholdComponent]

/-- In the explicit homotopy, evaluation at the one vertex is the zero map. -/
theorem exampleThresholdComponent_at_one {A : CosimplicialRing.{u}} (n : ℕ) :
    exampleThresholdComponent (A := A) n
        (SimplexCategory.const (SimplexCategory.mk n)
          (SimplexCategory.mk 1) 1) = 0 := by
  classical
  ext x i
  simp [exampleThresholdComponent]

/-- The naturality square displayed in the source for the threshold maps. -/
theorem exampleThresholdComponent_naturality {A : CosimplicialRing.{u}}
    {n m : ℕ} (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk 1)
    (x : exampleCosimplicialModuleDegree A n) :
    exampleThresholdComponent m α ((exampleCosimplicialModule A).map f x) =
      (exampleCosimplicialModule A).map f
        (exampleThresholdComponent n (f ≫ α) x) := by
  sorry

/-- The displayed map `h : M_* → Hom(Δ[1], M_*)` in the source example.
The naturality equation is the only part of this explicit calculation left
to the proof stage. -/
theorem example_cosimplicial_module_homotopy (A : CosimplicialRing.{u}) :
    Nonempty (CosimplicialModuleHomotopy
      (cosimplicialModuleHomZero (exampleCosimplicialModule A)
        (exampleCosimplicialModule A))
      (cosimplicialModuleHomId (exampleCosimplicialModule A))) := by
  classical
  refine ⟨{ app := fun n α => exampleThresholdComponent (A := A) n α
            at_zero := fun n => exampleThresholdComponent_at_zero (A := A) n
            at_one := fun n => exampleThresholdComponent_at_one (A := A) n
            naturality := fun f α x => exampleThresholdComponent_naturality f α x }⟩

/-- The identity of the explicit cosimplicial module is homotopic to zero. -/
theorem example_cosimplicial_module_contractible (A : CosimplicialRing.{u}) :
    CosimplicialModuleHomotopic
      (cosimplicialModuleHomId (exampleCosimplicialModule A))
      (cosimplicialModuleHomZero (exampleCosimplicialModule A)
        (exampleCosimplicialModule A)) := by
  exact Relation.EqvGen.symm _ _
    (cosimplicialModuleHomotopic_of_homotopy
      (Classical.choice (example_cosimplicial_module_homotopy A)))

/-! ### Direct sums over the polynomial generators -/

/-- The degreewise direct sum of copies of the explicit example, indexed by
the chosen set of polynomial generators. -/
abbrev exampleFamilyCosimplicialModuleDegree (I : Type u)
    (A : CosimplicialRing.{u}) (n : ℕ) :=
  I →₀ exampleCosimplicialModuleDegree A n

/-- The structure map on the direct sum over the generator index. -/
noncomputable def exampleFamilyCosimplicialModuleMap {I : Type u}
    {A : CosimplicialRing.{u}} {n m : ℕ}
    (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    exampleFamilyCosimplicialModuleDegree I A n →ₛₗ[(A.map f).hom]
      exampleFamilyCosimplicialModuleDegree I A m :=
  Finsupp.mapRange.linearMap (exampleCosimplicialModuleMap f)

/-- The direct sum of copies of the example is again a cosimplicial module. -/
noncomputable def exampleFamilyCosimplicialModule (I : Type u)
    (A : CosimplicialRing.{u}) : CosimplicialModule A where
  obj n := exampleFamilyCosimplicialModuleDegree I A n
  addCommGroup n := inferInstance
  module_structure n := inferInstance
  map f := (exampleFamilyCosimplicialModuleMap f).toAddMonoidHom
  map_smul' f r x := (exampleFamilyCosimplicialModuleMap f).map_smulₛₗ r x
  map_id' n := by
    ext x i j
    simp [exampleFamilyCosimplicialModuleMap, exampleCosimplicialModuleMap,
      ringHomSemilinear]
    rw [A.map_id]
    rfl
  map_comp' f g := by
    ext x i j
    simp [exampleFamilyCosimplicialModuleMap, exampleCosimplicialModuleMap,
      ringHomSemilinear, Function.comp_def]
    rw [A.map_comp]
    rfl

/-- The direct-sum version of the threshold component. -/
noncomputable def exampleFamilyThresholdComponent {I : Type u}
    {A : CosimplicialRing.{u}} (n : ℕ)
    (α : SimplexCategory.mk n ⟶ SimplexCategory.mk 1) :
    exampleFamilyCosimplicialModuleDegree I A n →ₗ[A.obj (SimplexCategory.mk n)]
      exampleFamilyCosimplicialModuleDegree I A n :=
  Finsupp.mapRange.linearMap (exampleThresholdComponent (A := A) n α)

/-- The direct sum of copies of the explicit example is contractible. -/
theorem example_family_cosimplicial_module_contractible (I : Type u)
    (A : CosimplicialRing.{u}) :
    CosimplicialModuleHomotopic
      (cosimplicialModuleHomId (exampleFamilyCosimplicialModule I A))
      (cosimplicialModuleHomZero (exampleFamilyCosimplicialModule I A)
        (exampleFamilyCosimplicialModule I A)) := by
  classical
  have h : Nonempty (CosimplicialModuleHomotopy
      (cosimplicialModuleHomZero (exampleFamilyCosimplicialModule I A)
        (exampleFamilyCosimplicialModule I A))
      (cosimplicialModuleHomId (exampleFamilyCosimplicialModule I A))) := by
    refine ⟨{ app := fun n α => exampleFamilyThresholdComponent n α
              at_zero := by
                intro n
                ext x i j
                simp [exampleFamilyThresholdComponent,
                  exampleThresholdComponent_at_zero]
                rfl
              at_one := by
                intro n
                ext x i j
                simp [exampleFamilyThresholdComponent,
                  exampleThresholdComponent_at_one]
                rfl
              naturality := by sorry }⟩
  exact Relation.EqvGen.symm _ _
    (cosimplicialModuleHomotopic_of_homotopy (Classical.choice h))

/-! ## The differential-module interface -/

/-- Data expressing the comparison of the completed differential module in
the source with the base change and completion of the explicit polynomial
model.  The map identities are the functoriality needed to expose the
identity and zero endpoints after applying the two operations. -/
structure CompletedDifferentialModel where
  P : CosimplicialRing.{u}
  D : CosimplicialRing.{u}
  index : Type u
  comparison : P ⟶ D
  ideal : CosimplicialIdeal D
  baseChange : CosimplicialBaseChangeOperation (A := P) (B := D) comparison
  completion : CosimplicialCompletionOperation (A := D) ideal
  baseChange_map_id :
    baseChange.map
        (cosimplicialModuleHomId (exampleFamilyCosimplicialModule index P)) =
      cosimplicialModuleHomId
        (baseChange.obj (exampleFamilyCosimplicialModule index P))
  baseChange_map_zero :
    baseChange.map
        (cosimplicialModuleHomZero
          (exampleFamilyCosimplicialModule index P)
          (exampleFamilyCosimplicialModule index P)) =
      cosimplicialModuleHomZero
        (baseChange.obj (exampleFamilyCosimplicialModule index P))
        (baseChange.obj (exampleFamilyCosimplicialModule index P))
  completion_map_id :
    completion.map
        (cosimplicialModuleHomId
          (baseChange.obj (exampleFamilyCosimplicialModule index P))) =
      cosimplicialModuleHomId
        (completion.obj
          (baseChange.obj (exampleFamilyCosimplicialModule index P)))
  completion_map_zero :
    completion.map
        (cosimplicialModuleHomZero
          (baseChange.obj (exampleFamilyCosimplicialModule index P))
          (baseChange.obj (exampleFamilyCosimplicialModule index P))) =
      cosimplicialModuleHomZero
        (completion.obj
          (baseChange.obj (exampleFamilyCosimplicialModule index P)))
        (completion.obj
          (baseChange.obj (exampleFamilyCosimplicialModule index P)))

/-- The completed module denoted by `Ω_{D(*)}` in the source. -/
noncomputable abbrev completedDifferentialModule (C : CompletedDifferentialModel) :=
  C.completion.obj
    (C.baseChange.obj (exampleFamilyCosimplicialModule C.index C.P))

/-- The completed differential-module cosimplicial object is contractible. -/
theorem vanishing_omega_one (C : CompletedDifferentialModel) :
    CosimplicialModuleHomotopic
      (cosimplicialModuleHomId (completedDifferentialModule C))
      (cosimplicialModuleHomZero (completedDifferentialModule C)
        (completedDifferentialModule C)) := by
  rw [← C.completion_map_id, ← C.completion_map_zero,
    ← C.baseChange_map_id, ← C.baseChange_map_zero]
  exact homotopy_completion C.ideal
    (homotopy_base_change C.comparison
      (example_family_cosimplicial_module_contractible C.index C.P) C.baseChange)
    C.completion

/-! ## Exterior powers, completion, and tensoring -/

/-- The completed `i`th exterior power of a cosimplicial differential module. -/
abbrev completedExteriorPower {D : CosimplicialRing.{u}}
    (ideal : CosimplicialIdeal D)
    (completion : CosimplicialCompletionOperation ideal)
    (W : CosimplicialExteriorPowerOperation D)
    (Ω : CosimplicialModule D) (i : ℕ) :=
  completion.obj (W.obj i Ω)

/-- The source's second vanishing lemma: tensoring an arbitrary cosimplicial
module with a completed positive exterior power of the differential module is
homotopic to zero. -/
theorem vanishing_tensor_completed_exterior
    {D : CosimplicialRing.{u}}
    (ideal : CosimplicialIdeal D)
    (completion : CosimplicialCompletionOperation ideal)
    (W : CosimplicialExteriorPowerOperation D)
    (Ω : CosimplicialModule D)
    (hΩ : CosimplicialModuleHomotopic
      (cosimplicialModuleHomId Ω) (cosimplicialModuleHomZero Ω Ω))
    (M : CosimplicialModule D)
    (T : CosimplicialTensorProductOperation D)
    {i : ℕ} (_hi : 0 < i)
    (exterior_map_id :
      W.map i (cosimplicialModuleHomId Ω) =
        cosimplicialModuleHomId (W.obj i Ω))
    (exterior_map_zero :
      W.map i (cosimplicialModuleHomZero Ω Ω) =
        cosimplicialModuleHomZero (W.obj i Ω) (W.obj i Ω))
    (completion_map_id :
      completion.map (cosimplicialModuleHomId (W.obj i Ω)) =
        cosimplicialModuleHomId (completedExteriorPower ideal completion W Ω i))
    (completion_map_zero :
      completion.map (cosimplicialModuleHomZero (W.obj i Ω) (W.obj i Ω)) =
        cosimplicialModuleHomZero
          (completedExteriorPower ideal completion W Ω i)
          (completedExteriorPower ideal completion W Ω i))
    (tensor_map_id :
      T.map (L := M)
          (cosimplicialModuleHomId
            (completedExteriorPower ideal completion W Ω i)) =
        cosimplicialModuleHomId
          (T.obj (completedExteriorPower ideal completion W Ω i) M))
    (tensor_map_zero :
      T.map (L := M)
          (cosimplicialModuleHomZero
            (completedExteriorPower ideal completion W Ω i)
            (completedExteriorPower ideal completion W Ω i)) =
        cosimplicialModuleHomZero
          (T.obj (completedExteriorPower ideal completion W Ω i) M)
          (T.obj (completedExteriorPower ideal completion W Ω i) M)) :
    CosimplicialModuleHomotopic
      (cosimplicialModuleHomId
        (T.obj (completedExteriorPower ideal completion W Ω i) M))
      (cosimplicialModuleHomZero
        (T.obj (completedExteriorPower ideal completion W Ω i) M)
        (T.obj (completedExteriorPower ideal completion W Ω i) M)) := by
  have hW := homotopy_exterior_power hΩ W i
  have hC := homotopy_completion ideal hW completion
  have hT := homotopy_tensor hC M T
  simpa [exterior_map_id, exterior_map_zero, completion_map_id,
    completion_map_zero, tensor_map_id, tensor_map_zero] using hT

end Formalization.Books.Crystalline.Unit19
