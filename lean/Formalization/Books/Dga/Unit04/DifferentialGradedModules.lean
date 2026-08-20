import Formalization.Books.Dga.Unit03.Definitions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Differential Graded Algebra, Chapter 4: Differential graded modules

The source uses right modules.  The preceding chapter represents a
differential graded algebra by a monoid object in integer-indexed cochain
complexes of `R`-modules.  Accordingly, a differential graded module is
represented by a right module object: its action is a morphism of cochain
complexes
`Tot(M ⊗ A) ⟶ M`, with the usual unit and associativity diagrams.

This categorical presentation simultaneously records the grading and the
Leibniz rule, while the homogeneous action and Leibniz predicate below expose
the elementwise form used by the book.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open ComplexShape
open Formalization.Books.Dga.Unit03

universe u v

namespace Formalization.Books.Dga.Unit04

/-! ## Differential graded modules -/

/-- A right differential graded module over a cochain differential graded
`R`-algebra.  The action is a chain map, and the two displayed equations are
the right-module unit and associativity laws in the tensor category of
cochain complexes. -/
structure DifferentialGradedModule {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) where
  complex : CochainComplexOver R
  action : tensorProductComplex R complex A.complex ⟶ complex
  one_action :
    tensorHomComplex (𝟙 complex) A.unit ≫ action =
      (HomologicalComplex.rightUnitor complex).hom
  assoc_action :
    tensorHomComplex action (𝟙 A.complex) ≫ action =
      (HomologicalComplex.associator complex A.complex A.complex).hom ≫
        tensorHomComplex (𝟙 complex) A.multiplication ≫ action

/-! The complex representation keeps the grading degreewise.  This carrier is
the source's corresponding direct sum of homogeneous pieces. -/

/-- The total graded carrier of a differential graded module. -/
def DifferentialGradedModule.gradedCarrier
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : Type u :=
  DirectSum ℤ (fun n => (M.complex.X n : Type u))

/-- The homogeneous component of the action of a differential graded module.
The source and target degrees are made explicit by the total-complex
inclusion. -/
noncomputable def DifferentialGradedModule.homogeneousAction
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (p q : ℤ) :
    M.complex.X p ⊗ A.complex.X q ⟶ M.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj M.complex A.complex p q (p + q) rfl ≫
    M.action.f (p + q)

/-- Evaluation of the homogeneous action on a pure tensor. -/
def DifferentialGradedModule.actionOnHomogeneous
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (p q : ℤ)
    (x : M.complex.X p) (a : A.complex.X q) : M.complex.X (p + q) :=
  (M.homogeneousAction p q).hom (x ⊗ₜ[R] a)

/-- The elementwise Leibniz rule for a differential graded module.  The
transports only reconcile the two associative parenthesizations of integer
addition. -/
def DifferentialGradedModule.SatisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : Prop :=
  ∀ (n m : ℤ) (x : M.complex.X n) (a : A.complex.X m),
    (M.complex.d (n + m) (n + m + 1)).hom
        (M.actionOnHomogeneous n m x a) =
      transportComponent (C := M.complex) (by omega)
          (M.actionOnHomogeneous (n + 1) m
            ((M.complex.d n (n + 1)).hom x) a) +
        ((n.negOnePow : ℤ) : R) •
          transportComponent (C := M.complex)
            (by omega : n + (m + 1) = n + m + 1)
            (M.actionOnHomogeneous n (m + 1) x
              ((A.complex.d m (m + 1)).hom a))

/-- The chain-map condition on the action is the Leibniz rule. -/
theorem DifferentialGradedModule.satisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : M.SatisfiesLeibniz := by
  intro n m x a
  have h := congrArg (fun f => f.hom
      ((HomologicalComplex.ιTensorObj M.complex A.complex n m (n + m) rfl).hom
        (x ⊗ₜ[R] a)))
    (M.action.comm (n + m) (n + m + 1))
  have ht := tensorProductComplex_differential_formula R M.complex A.complex n m
  have ht' := congrArg (fun f => (M.action.f (n + m + 1)).hom
      (f.hom (x ⊗ₜ[R] a))) ht
  have hAction (p q r : ℤ) (h : p + q = r)
      (u : M.complex.X p) (v : A.complex.X q) :
      transportComponent (C := M.complex) h
          (M.actionOnHomogeneous p q u v) =
        (M.action.f r).hom
          ((HomologicalComplex.ιTensorObj M.complex A.complex p q r h).hom
            (u ⊗ₜ[R] v)) := by
    subst r
    rfl
  have h₁ := hAction (n + 1) m (n + m + 1) (by omega)
    ((M.complex.d n (n + 1)).hom x) a
  have h₂ := hAction n (m + 1) (n + m + 1) (by omega)
    x ((A.complex.d m (m + 1)).hom a)
  calc
    _ = (M.action.f (n + m + 1)).hom
        (((tensorProductComplex R M.complex A.complex).d (n + m) (n + m + 1)).hom
          ((HomologicalComplex.ιTensorObj M.complex A.complex n m (n + m) rfl).hom
            (x ⊗ₜ[R] a))) := by
      simpa only [ModuleCat.comp_apply,
        DifferentialGradedModule.actionOnHomogeneous,
        DifferentialGradedModule.homogeneousAction] using h
    _ = (M.action.f (n + m + 1)).hom
        (((((M.complex.d n (n + 1) ⊗ₘ 𝟙 (A.complex.X m)) ≫
          HomologicalComplex.ιTensorObj M.complex A.complex (n + 1) m (n + m + 1) (by omega)) +
          n.negOnePow •
            ((𝟙 (M.complex.X n) ⊗ₘ A.complex.d m (m + 1)) ≫
              HomologicalComplex.ιTensorObj M.complex A.complex n (m + 1)
                (n + m + 1) (by omega))).hom (x ⊗ₜ[R] a))) := by
      simpa only [ModuleCat.comp_apply] using ht'
    _ = (M.action.f (n + m + 1)).hom
          ((HomologicalComplex.ιTensorObj M.complex A.complex (n + 1) m
              (n + m + 1) (by omega)).hom
            ((M.complex.d n (n + 1)).hom x ⊗ₜ[R] a)) +
        n.negOnePow •
          (M.action.f (n + m + 1)).hom
            ((HomologicalComplex.ιTensorObj M.complex A.complex n (m + 1)
                (n + m + 1) (by omega)).hom
              (x ⊗ₜ[R] (A.complex.d m (m + 1)).hom a)) := by
      simp
    _ = _ := by
      rw [← h₁, ← h₂]
      simp only [Units.smul_def]
      congr 1
      rw [Int.cast_smul_eq_zsmul]

/-- A homomorphism of differential graded modules.  Its underlying map is a
map of cochain complexes and the second field is compatibility with the
right `A`-action. -/
def DifferentialGradedModuleHomSubgroup
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) :
    AddSubgroup (M.complex ⟶ N.complex) where
  carrier := {f |
    M.action ≫ f = tensorHomComplex f (𝟙 A.complex) ≫ N.action}
  zero_mem' := by
    have hz : tensorHomComplex (0 : M.complex ⟶ N.complex) (𝟙 A.complex) = 0 := by
      apply HomologicalComplex.hom_ext
      intro j
      apply ModuleCat.hom_ext
      let φ := HomologicalComplex₂.toGradedObjectMap
        (((((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
          (up ℤ) (up ℤ)).map (0 : M.complex ⟶ N.complex)).app A.complex) ≫
          (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
            (up ℤ) (up ℤ)).obj N.complex).map (𝟙 A.complex))
      change ModuleCat.Hom.hom
        (GradedObject.mapMap φ ((up ℤ).π (up ℤ) (up ℤ)) j) = 0
      have hm : GradedObject.mapMap φ ((up ℤ).π (up ℤ) (up ℤ)) j = 0 := by
        apply GradedObject.mapObj_ext
        rintro ⟨i₁, i₂⟩ hij
        simp only [GradedObject.mapMap, GradedObject.ι_descMapObj]
        simp [φ, Functor.map_zero, zero_app]
        all_goals
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              simp only [zero_comp, comp_zero]
      rw [hm]
      rfl
    change M.action ≫ (0 : M.complex ⟶ N.complex) =
      tensorHomComplex 0 (𝟙 A.complex) ≫ N.action
    rw [hz]
    simp
  add_mem' := by
    intro f g hf hg
    change M.action ≫ (f + g) =
      tensorHomComplex (f + g) (𝟙 A.complex) ≫ N.action
    change M.action ≫ f = tensorHomComplex f (𝟙 A.complex) ≫ N.action at hf
    change M.action ≫ g = tensorHomComplex g (𝟙 A.complex) ≫ N.action at hg
    have htensor : tensorHomComplex (f + g) (𝟙 A.complex) =
        tensorHomComplex f (𝟙 A.complex) + tensorHomComplex g (𝟙 A.complex) := by
      apply HomologicalComplex.hom_ext
      intro j
      change GradedObject.mapMap _ ((up ℤ).π (up ℤ) (up ℤ)) j =
        GradedObject.mapMap _ ((up ℤ).π (up ℤ) (up ℤ)) j +
          GradedObject.mapMap _ ((up ℤ).π (up ℤ) (up ℤ)) j
      apply GradedObject.mapObj_ext
      rintro ⟨i₁, i₂⟩ hij
      simp [GradedObject.mapMap, HomologicalComplex₂.toGradedObjectMap]
      calc
        _ = (f.f i₁ ▷ A.complex.X i₂ + g.f i₁ ▷ A.complex.X i₂) ≫
              (((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj
                N.complex.X).obj A.complex.X).ιMapObj
                ((up ℤ).π (up ℤ) (up ℤ)) (i₁, i₂) j hij := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              rw [GradedObject.ι_descMapObj]
        _ = (f.f i₁ ▷ A.complex.X i₂ ≫
              (((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj
                N.complex.X).obj A.complex.X).ιMapObj
                ((up ℤ).π (up ℤ) (up ℤ)) (i₁, i₂) j hij) +
            (g.f i₁ ▷ A.complex.X i₂ ≫
              (((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj
                N.complex.X).obj A.complex.X).ιMapObj
                ((up ℤ).π (up ℤ) (up ℤ)) (i₁, i₂) j hij) := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              apply Preadditive.add_comp
        _ = _ := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              rw [Preadditive.comp_add _ _ _ _ _ _]
          set_option backward.isDefEq.respectTransparency.types false in
            simp only [GradedObject.ι_descMapObj]
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              rfl
    rw [htensor]
    simp [Preadditive.comp_add, hf, hg]
  neg_mem' := by
    intro f hf
    change M.action ≫ (-f) =
      tensorHomComplex (-f) (𝟙 A.complex) ≫ N.action
    change M.action ≫ f = tensorHomComplex f (𝟙 A.complex) ≫ N.action at hf
    have htensor : tensorHomComplex (-f) (𝟙 A.complex) =
        -(tensorHomComplex f (𝟙 A.complex)) := by
      apply HomologicalComplex.hom_ext
      intro j
      change GradedObject.mapMap _ ((up ℤ).π (up ℤ) (up ℤ)) j =
        -GradedObject.mapMap _ ((up ℤ).π (up ℤ) (up ℤ)) j
      apply GradedObject.mapObj_ext
      rintro ⟨i₁, i₂⟩ hij
      have hneg : (-f.f i₁) ▷ A.complex.X i₂ =
          -(f.f i₁ ▷ A.complex.X i₂) := by
        apply eq_neg_of_add_eq_zero_left
        rw [add_comm]
        rw [← MonoidalPreadditive.add_whiskerRight (f.f i₁) (-f.f i₁)]
        simp
      have hnegPair : (-f.f (i₁, i₂).1) ▷ A.complex.X (i₁, i₂).2 =
          -(f.f (i₁, i₂).1 ▷ A.complex.X (i₁, i₂).2) := by
        apply eq_neg_of_add_eq_zero_left
        rw [add_comm]
        rw [← MonoidalPreadditive.add_whiskerRight
          (f.f (i₁, i₂).1) (-f.f (i₁, i₂).1)]
        simp
      simp [GradedObject.mapMap, HomologicalComplex₂.toGradedObjectMap,
        Functor.map_neg]
      calc
        _ = (-(f.f (i₁, i₂).1 ▷ A.complex.X (i₁, i₂).2)) ≫
              (((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj
                N.complex.X).obj A.complex.X).ιMapObj
                ((up ℤ).π (up ℤ) (up ℤ)) (i₁, i₂) j hij := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              rw [GradedObject.ι_descMapObj]
        _ = -((f.f (i₁, i₂).1 ▷ A.complex.X (i₁, i₂).2) ≫
              (((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj
                N.complex.X).obj A.complex.X).ιMapObj
                ((up ℤ).π (up ℤ) (up ℤ)) (i₁, i₂) j hij) := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              simp only [Preadditive.neg_comp]
        _ = _ := by
          set_option backward.isDefEq.respectTransparency false in
            set_option backward.isDefEq.respectTransparency.types false in
              simp only [Preadditive.comp_neg, GradedObject.ι_descMapObj]
    rw [htensor]
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
      congrArg (fun h => -h) hf

/-- The morphism type in the category of differential graded modules. -/
abbrev DifferentialGradedModuleHom
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) : Type _ :=
  DifferentialGradedModuleHomSubgroup M N

namespace DifferentialGradedModuleHom

/-- Forget the module structure of a differential graded module morphism. -/
def underlying
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) : M.complex ⟶ N.complex :=
  f.1

@[simp]
theorem underlying_mem
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) :
    M.action ≫ f.underlying =
      tensorHomComplex f.underlying (𝟙 A.complex) ≫ N.action :=
  f.2

end DifferentialGradedModuleHom

/-! The underlying cochain differential is `R`-linear, which is the source's
observation that scalars from the degree-zero base commute with the
differential. -/

theorem DifferentialGradedModule.differential_smul
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (n : ℤ) (r : R)
    (x : M.complex.X n) :
    (M.complex.d n (n + 1)).hom (r • x) =
      r • (M.complex.d n (n + 1)).hom x := by
  exact (M.complex.d n (n + 1)).hom.map_smul r x

/-! ## The category and its limits -/

/-- The category denoted by `Mod_(A,d)` in the source. -/
abbrev DifferentialGradedModuleCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) := DifferentialGradedModule A

instance differentialGradedModuleCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    Category (DifferentialGradedModuleCategory A) where
  Hom M N := DifferentialGradedModuleHom M N
  id M := ⟨𝟙 M.complex, by sorry⟩
  comp f g := ⟨f.underlying ≫ g.underlying, by sorry⟩
  id_comp f := by sorry
  comp_id f := by sorry
  assoc f g h := by sorry

instance differentialGradedModuleHomAddCommGroup
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) :
    AddCommGroup (DifferentialGradedModuleHom M N) :=
  AddSubgroupClass.toAddCommGroup _

instance differentialGradedModulePreadditive
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Preadditive (DifferentialGradedModuleCategory A) where
  homGroup M N := differentialGradedModuleHomAddCommGroup M N
  add_comp := by sorry
  comp_add := by sorry

/-- The category of differential graded modules is abelian. -/
noncomputable instance differentialGradedModuleAbelian
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Abelian (DifferentialGradedModuleCategory A) := by
  sorry

/-- The abelian structure makes the category of differential graded modules
balanced.  Mathlib does not register this consequence of `Abelian` as a
global instance, but the exact lifting API uses it explicitly. -/
instance differentialGradedModuleBalanced
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    Balanced (DifferentialGradedModuleCategory A) where
  isIso_of_mono_of_epi f := by
    let : Preadditive (DifferentialGradedModuleCategory A) :=
      (differentialGradedModuleAbelian A).toPreadditive
    let : IsNormalMonoCategory (DifferentialGradedModuleCategory A) :=
      (differentialGradedModuleAbelian A).toIsNormalMonoCategory
    intro _ _
    let : NormalMono f := normalMonoOfMono f
    have hg : NormalMono.g (f := f) = 0 := by
      apply (cancel_epi f).1
      rw [NormalMono.w (f := f), comp_zero]
    have hk : (𝟙 _) ≫ NormalMono.g (f := f) = 0 := by
      rw [Category.id_comp, hg]
    let l := NormalMono.lift' f (𝟙 _) hk
    refine ⟨⟨l.1, ?_, l.2⟩⟩
    apply (cancel_mono f).1
    rw [Category.assoc, l.2, Category.id_comp, Category.comp_id]

/-- The category of differential graded modules has arbitrary limits. -/
noncomputable instance differentialGradedModuleHasLimits
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    HasLimits (DifferentialGradedModuleCategory A) := by
  sorry

/-- The category of differential graded modules has arbitrary colimits. -/
noncomputable instance differentialGradedModuleHasColimits
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    HasColimits (DifferentialGradedModuleCategory A) := by
  sorry

theorem differentialGradedModule_category_has_limits
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    HasLimits (DifferentialGradedModuleCategory A) := inferInstance

theorem differentialGradedModule_category_has_colimits
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) :
    HasColimits (DifferentialGradedModuleCategory A) := inferInstance

/-! The source describes products degreewise and then takes the direct sum of
the graded pieces.  These carriers record that construction explicitly; the
`HasLimits` instance above supplies the corresponding module object and its
universal property.  In particular, this is not the product in the category
of all graded objects: the direct sum in the degree index is part of the
definition of a cochain complex. -/

abbrev dgmProductComponent {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type v}
    (F : ι → DifferentialGradedModuleCategory A) (n : ℤ) : Type _ :=
  ∀ i, ((F i).complex.X n : Type u)

def dgmProductGradedCarrier {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type v}
    (F : ι → DifferentialGradedModuleCategory A) : Type _ :=
  DirectSum ℤ (dgmProductComponent F)

/-- The product of a family of differential graded modules, supplied by the
categorical limit. -/
noncomputable abbrev dgmProduct {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type u}
    (F : ι → DifferentialGradedModuleCategory A) :
    DifferentialGradedModuleCategory A :=
  limit (Discrete.functor F)

/-- The projection from the product to one family member. -/
abbrev dgmProductProjection {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type u}
    (F : ι → DifferentialGradedModuleCategory A) (i : ι) :
    dgmProduct F ⟶ F i :=
  limit.π (Discrete.functor F) ⟨i⟩

/-- The product cone is universal. -/
theorem dgmProduct_isLimit {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type u}
    (F : ι → DifferentialGradedModuleCategory A) :
    Nonempty (IsLimit (limit.cone (Discrete.functor F))) := by
  exact ⟨limit.isLimit _⟩

/-- The degreewise product formula from the source.  The chosen limit object
has the module in degree `n` obtained by taking the product of the degree-`n`
components. -/
theorem dgmProduct_component_formula {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} {ι : Type u}
    (F : ι → DifferentialGradedModuleCategory A) (n : ℤ) :
    Nonempty ((dgmProduct F).complex.X n ≅
      ModuleCat.of R (dgmProductComponent F n)) := by
  sorry

/-! ## The underlying cochain complex and cohomology -/

/-- The forgetful functor to the category of cochain complexes of `R`-modules. -/
def dgmForgetful {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :
    DifferentialGradedModuleCategory A ⥤ CochainComplexOver R where
  obj M := M.complex
  map f := f.underlying
  map_id := by
    intro M
    rfl
  map_comp := by
    intro M N P f g
    rfl

/-! The source calls this an exact functor of abelian categories.  We retain
the canonical Mathlib property in addition to the short-exact formulation
used below for the homology sequence. -/

/-- Exactness of the forgetful functor in Mathlib's canonical interface. -/
def dgmForgetfulIsExactFunctor {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} : Prop :=
  exactFunctor (DifferentialGradedModuleCategory A) (CochainComplexOver R)
    (dgmForgetful (A := A))

theorem dgmForgetful_isExactFunctor {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :
    dgmForgetfulIsExactFunctor (A := A) := by
  sorry

noncomputable instance dgmForgetfulAdditive
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R} :
    (dgmForgetful (A := A)).Additive := by
  sorry

/-- Exactness of the forgetful functor, stated in the source-facing form. -/
def dgmForgetfulIsExact {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} : Prop :=
  ∀ (S : ShortComplex (DifferentialGradedModuleCategory A)),
    S.ShortExact → (S.map (dgmForgetful (A := A))).ShortExact

theorem dgmForgetful_isExact {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :
    dgmForgetfulIsExact (A := A) := by
  sorry

/-- The forgetful functor preserves homology, so the usual homology sequence
API applies to short exact sequences of differential graded modules. -/
noncomputable instance dgmForgetfulPreservesHomology
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R} :
    (dgmForgetful (A := A)).PreservesHomology := by
  sorry

/-- The cohomology module `H^n(M)` of a differential graded module. -/
abbrev dgmCohomology {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (n : ℤ) : ModuleCat.{u} R :=
  M.complex.homology n

/-- The degree-`n` cohomology functor on differential graded modules. -/
noncomputable def dgmCohomologyFunctor {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} (n : ℤ) :
    DifferentialGradedModuleCategory A ⥤ ModuleCat.{u} R :=
  dgmForgetful (A := A) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n

/-- The map on cohomology induced by a differential graded module morphism. -/
noncomputable def dgmCohomologyMap {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) (n : ℤ) :
    dgmCohomology M n ⟶ dgmCohomology N n :=
  HomologicalComplex.homologyMap f.underlying n

@[simp]
theorem dgmCohomologyFunctor_map {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) (n : ℤ) :
    (dgmCohomologyFunctor (A := A) n).map f = dgmCohomologyMap f n := by
  rfl

/-- A differential graded module is acyclic when all its cohomology modules
are zero. -/
def IsAcyclic {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : Prop :=
  ∀ n : ℤ, IsZero (dgmCohomology M n)

/-- A differential graded module morphism is a quasi-isomorphism when it
induces an isomorphism on every cohomology module. -/
def IsQuasiIsomorphism {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∀ n : ℤ, IsIso (dgmCohomologyMap f n)

/-! ## The long exact cohomology sequence -/

/-- The underlying short complex of a short complex of differential graded
modules. -/
abbrev dgmUnderlyingShortComplex {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (S : ShortComplex (DifferentialGradedModuleCategory A)) :
    ShortComplex (CochainComplexOver R) :=
  S.map (dgmForgetful (A := A))

theorem dgmUnderlyingShortExact {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (S : ShortComplex (DifferentialGradedModuleCategory A))
    (hS : S.ShortExact) :
    (dgmUnderlyingShortComplex S).ShortExact := by
  exact dgmForgetful_isExact S hS

/-- The connecting map `H^n(M) ⟶ H^(n+1)(K)` attached to a short exact
sequence `0 ⟶ K ⟶ L ⟶ M ⟶ 0`. -/
noncomputable def dgmConnectingMap {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
  (hS : S.ShortExact) (n : ℤ) :
  dgmCohomology S.X₃ n ⟶ dgmCohomology S.X₁ (n + 1) :=
  (dgmUnderlyingShortExact S hS).δ n (n + 1) (by
    change n + 1 = n + 1
    rfl)

/-- The three consecutive exactness assertions in the displayed fragment of
the long exact cohomology sequence. -/
structure DGMLongExactFragment {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : S.ShortExact) (n : ℤ) where
  at_kernel :
    (ShortComplex.mk (dgmCohomologyMap S.f n) (dgmCohomologyMap S.g n)
      (by sorry)).Exact
  at_cokernel :
    (ShortComplex.mk (dgmCohomologyMap S.g n) (dgmConnectingMap hS n)
      (by sorry)).Exact
  at_next_kernel :
    (ShortComplex.mk (dgmConnectingMap hS n)
      (dgmCohomologyMap S.f (n + 1))
      (by sorry)).Exact

theorem dgm_long_exact_cohomology_fragment
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : S.ShortExact) (n : ℤ) : DGMLongExactFragment hS n := by
  sorry

/-! ## Shifts -/

/-- The sign-free comparison
`Tot(M[k] ⊗ A) ≅ Tot(M ⊗ A)[k]` used to define the shifted action. -/
noncomputable abbrev dgmShiftTensorIso {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    tensorProductComplex R
        ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex)
        A.complex ≅
      (CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj
        (tensorProductComplex R M.complex A.complex) :=
  CochainComplex.mapBifunctorShift₁Iso M.complex A.complex
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) k

/-- The action on the shifted module.  Mathlib's
`mapBifunctorShift₁Iso` is the canonical sign-free identification
`Tot(M[k] ⊗ A) ≅ Tot(M ⊗ A)[k]`; the shifted action is then the shift of the
original action. -/
noncomputable def dgmShiftAction {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    tensorProductComplex R
        ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex)
        A.complex ⟶
      ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex) :=
  (dgmShiftTensorIso M k).hom ≫
    (CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action

theorem dgmShiftAction_factorization {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    dgmShiftAction M k =
      (dgmShiftTensorIso M k).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action := rfl

/-- The `k`-shifted differential graded module. -/
noncomputable def dgmShift {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) : DifferentialGradedModule A where
  complex := (CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex
  action := dgmShiftAction M k
  one_action := by sorry
  assoc_action := by sorry

@[simp]
theorem dgmShift_component {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k n : ℤ) :
    (dgmShift M k).complex.X n = M.complex.X (n + k) := rfl

theorem dgmShift_differential {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k n m : ℤ) :
    (dgmShift M k).complex.d n m =
      k.negOnePow • M.complex.d (n + k) (m + k) := rfl

/-- The cohomology of a shifted differential graded module is canonically the
cohomology of the original module in the shifted degree.  Mathlib's
`ShiftSequence` comparison is oriented here as in the source. -/
noncomputable def dgmShiftCohomologyIso {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k n : ℤ) :
  dgmCohomology (dgmShift M k) n ≅ dgmCohomology M (n + k) :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).shiftIso k n (n + k) (by omega)).app
        M.complex)

@[simp]
theorem dgmShift_actionOnHomogeneous {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k n m : ℤ)
    (x : (dgmShift M k).complex.X n) (a : A.complex.X m) :
    (dgmShift M k).actionOnHomogeneous n m x a =
      ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action).f
        (n + m)
          ((dgmShiftTensorIso M k).hom.f (n + m)
            ((HomologicalComplex.ιTensorObj
                ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex)
                A.complex n m (n + m) rfl).hom (x ⊗ₜ[R] a))) := rfl

/-- Under the component identification, the shifted action is the original
action on `M`; only the associative reindexing of the target degree remains. -/
theorem dgmShift_action_preserves_underlying_action {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k n m : ℤ)
    (x : (dgmShift M k).complex.X n) (a : A.complex.X m) :
    (dgmShift M k).actionOnHomogeneous n m x a =
      transportComponent (C := M.complex)
        (show (n + k) + m = (n + m) + k by omega)
        (M.actionOnHomogeneous (n + k) m x a) := by
  sorry

theorem dgmShift_satisfiesLeibniz {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    (dgmShift M k).SatisfiesLeibniz := by
  exact DifferentialGradedModule.satisfiesLeibniz (dgmShift M k)

/-- The shifted map of differential graded modules. -/
noncomputable def dgmShiftMap {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) (k : ℤ) :
    DifferentialGradedModuleHom (dgmShift M k) (dgmShift N k) :=
  ⟨(CategoryTheory.shiftFunctor (CochainComplexOver R) k).map f.underlying,
    by sorry⟩

/-- The functor `[k] : Mod_(A,d) ⥤ Mod_(A,d)`. -/
noncomputable def dgmShiftFunctor {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) (k : ℤ) :
    DifferentialGradedModuleCategory A ⥤ DifferentialGradedModuleCategory A where
  obj M := dgmShift M k
  map f := dgmShiftMap f k
  map_id := by
    intro M
    apply Subtype.ext
    rfl
  map_comp := by
    intro M N P f g
    apply Subtype.ext
    rfl

@[simp]
theorem dgmShiftFunctor_map_component {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (k : ℤ) {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) (n : ℤ) :
    ((dgmShiftFunctor A k).map f).underlying.f n = f.underlying.f (n + k) := rfl

/- The source's final paragraph only announces the triangle constructions
developed in the next numbered section; no additional Chapter 4 declaration
belongs here. -/

end Formalization.Books.Dga.Unit04
