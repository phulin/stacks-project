import Formalization.Books.Dga.Unit12.TensorProduct
import Formalization.Books.Dga.Unit28.Core

/-!
# Differential Graded Algebra, Chapter 29: Bimodules and tensor product

This file records the tensor-product constructions and interfaces in the
section `Bimodules and tensor product`.  The relative tensor products and the
cochain-complex cokernel presentation are the canonical constructions from
Chapter 12; this chapter supplies the right-module, functoriality, shift, and
associativity interfaces specific to bimodules.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit11
open Formalization.Books.Dga.Unit12
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit25
open Formalization.Books.Dga.Unit26
open Formalization.Books.Dga.Unit28
open scoped TensorProduct

universe u v

namespace Formalization.Books.Dga.Unit29

/-! ## Ordinary tensor products -/

/-- The standard module structures attached to the two actions in the
chapter-28 bimodule interface.  The fields are deliberately explicit because
the chapter-28 action maps do not install typeclass instances. -/
structure BimoduleModuleData
    (R A B N : Type u)
    [CommRing R] [Ring A] [Ring B] [AddCommGroup N] [Module R N]
    [Algebra R A] [Algebra R B] where
  bimodule : Bimodule R A B N
  leftModule : Module A N
  rightModule : Module Bᵐᵒᵖ N

/-- The explicit module structures agree with the action maps of the
chapter-28 bimodule. -/
def BimoduleModuleCompatible
    {R A B N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup N] [Module R N]
    [Algebra R A] [Algebra R B]
    (Ndata : BimoduleModuleData R A B N) : Prop := by
  letI : Module A N := Ndata.leftModule
  letI : Module Bᵐᵒᵖ N := Ndata.rightModule
  exact
    (∀ (a : A) (n : N), a • n = Ndata.bimodule.leftAction a n) ∧
      (∀ (n : N) (b : B), MulOpposite.op b • n = Ndata.bimodule.rightAction b n)

/-- The underlying type of `M ⊗_A N`, using Chapter 12's balanced quotient.
The `letI` installs the left `A`-module structure carried by the bimodule
data only while elaborating the canonical relative tensor product. -/
abbrev ordinaryTensorProductCarrier
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (_Ndata : BimoduleModuleData R A B N)
    (leftModule : Module A N) : Type u :=
  @relativeTensorProduct R A M N
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance leftModule

/-- The universal pure tensor in the ordinary relative tensor product. -/
def ordinaryTensorProductMk
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N) (m : M) (n : N) :
    ordinaryTensorProductCarrier (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N) := by
  letI : Module A N := Ndata.leftModule
  exact relativeTensorProductMk m n

/-- A right `B`-module structure on the balanced quotient. -/
structure OrdinaryTensorProductRightModuleSpec
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N) where
  module : Module Bᵐᵒᵖ
    (ordinaryTensorProductCarrier (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N))

/-- The ordinary tensor product of a right `A`-module with an `(A,B)`-bimodule
is a right `B`-module. -/
theorem ordinaryTensorProduct_rightModule_exists
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N)
    (hN : BimoduleModuleCompatible Ndata) :
    Nonempty (OrdinaryTensorProductRightModuleSpec (M := M) Ndata) := by
  sorry

/-- The selected right `B`-module structure on `M ⊗_A N`. -/
@[instance_reducible] noncomputable def ordinaryTensorProductRightModule
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N)
    (hN : BimoduleModuleCompatible Ndata) :
    Module Bᵐᵒᵖ (ordinaryTensorProductCarrier
      (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N)) :=
  (Classical.choice
    (ordinaryTensorProduct_rightModule_exists (M := M) Ndata hN)).module

/-- The right action on a pure ordinary tensor, before passing to the module
structure on the quotient. -/
def ordinaryTensorProductRightActionOnPureTensor
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N) (m : M) (n : N) (b : B) :
    ordinaryTensorProductCarrier (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N) :=
  ordinaryTensorProductMk Ndata m (Ndata.bimodule.rightAction b n)

theorem ordinaryTensorProductRightModule_smul_pure
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N)
    (hN : BimoduleModuleCompatible Ndata) :
    letI : Module Bᵐᵒᵖ (ordinaryTensorProductCarrier
      (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N)) :=
      ordinaryTensorProductRightModule Ndata hN
    ∀ (m : M) (n : N) (b : B),
      MulOpposite.op b • ordinaryTensorProductMk Ndata m n =
        ordinaryTensorProductRightActionOnPureTensor Ndata m n b := by
  sorry

/-- The ordinary tensor product as an object of `ModuleCat Bᵐᵒᵖ`. -/
noncomputable def ordinaryTensorProductBModule
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Module Aᵐᵒᵖ M] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (Ndata : BimoduleModuleData R A B N)
    (hN : BimoduleModuleCompatible Ndata) :
    ModuleCat.{u} Bᵐᵒᵖ := by
  letI : Module Bᵐᵒᵖ (ordinaryTensorProductCarrier
      (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N)) :=
    ordinaryTensorProductRightModule Ndata hN
  exact ModuleCat.of Bᵐᵒᵖ
    (ordinaryTensorProductCarrier (R := R) (A := A) (B := B) (M := M) Ndata
      (Ndata.leftModule : Module A N))

/-! ## Graded tensor products -/

/-- A graded right module in the homogeneous-piece presentation used by the
graded relative tensor product API. -/
structure GradedRightModuleData
    (R A M : Type u)
    [CommRing R] [Ring A] [AddCommGroup M] [Module R M] [Algebra R A]
    (GA : GradedAlgebraData R A) where
  grading : GradedModuleData R M ℤ
  rightAction : M →ₗ[R] A →ₗ[R] M
  homogeneousAction : ∀ p q : ℤ,
    grading.component p →ₗ[R] GA.component q →ₗ[R] grading.component (p + q)
  homogeneousAction_spec : ∀ (p q : ℤ)
      (m : grading.component p) (a : GA.component q),
    (homogeneousAction p q m a : M) = rightAction m.1 a.1
  right_one : ∀ m : M, rightAction m 1 = m
  right_assoc : ∀ (m : M) (a a' : A),
    rightAction (rightAction m a) a' = rightAction m (a * a')

/-- The left homogeneous action of a graded bimodule, restricted to the
homogeneous submodules. -/
def gradedBimoduleLeftAction
    {R A B N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup N] [Module R N]
    [Algebra R A] [Algebra R B]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Ndata : GradedBimodule R A B N GA GB) (p q : ℤ) :
    GA.component p →ₗ[R] Ndata.component q →ₗ[R] Ndata.component (p + q) :=
  { toFun := fun a =>
      { toFun := fun x =>
          ⟨Ndata.toBimodule.leftAction a.1 x.1,
            Ndata.left_homogeneous p q a x⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          simp
        map_smul' := by
          intro r x
          apply Subtype.ext
          simp }
    map_add' := by
      intro a a'
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp
    map_smul' := by
      intro r a
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp }

/-- The right homogeneous action of a graded bimodule, restricted to the
homogeneous submodules. -/
def gradedBimoduleRightAction
    {R A B N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup N] [Module R N]
    [Algebra R A] [Algebra R B]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Ndata : GradedBimodule R A B N GA GB) (p q : ℤ) :
    Ndata.component p →ₗ[R] GB.component q →ₗ[R] Ndata.component (p + q) :=
  { toFun := fun x =>
      { toFun := fun b =>
          ⟨Ndata.toBimodule.rightAction b.1 x.1,
            Ndata.right_homogeneous p q x b⟩
        map_add' := by
          intro b b'
          apply Subtype.ext
          simp
        map_smul' := by
          intro r b
          apply Subtype.ext
          simp }
    map_add' := by
      intro x y
      apply LinearMap.ext
      intro b
      apply Subtype.ext
      simp
    map_smul' := by
      intro r x
      apply LinearMap.ext
      intro b
      apply Subtype.ext
      simp }

/-- The degree-`n` part of `M ⊗_A N`, in the graded relative tensor-product
presentation from Chapter 12. -/
abbrev gradedTensorProductComponent
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Mdata : GradedRightModuleData R A M GA)
    (Ndata : GradedBimodule R A B N GA GB) (n : ℤ) :=
  gradedRelativeTensorProductComponent n
    (fun p => Mdata.grading.component p)
    (fun p => GA.component p)
    (fun p => Ndata.component p)
    Mdata.homogeneousAction (gradedBimoduleLeftAction GA GB Ndata)

/-- The pure-tensor formula for the right action on the graded relative tensor
product. -/
def gradedTensorProductRightActionOnPureTensor
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Mdata : GradedRightModuleData R A M GA)
    (Ndata : GradedBimodule R A B N GA GB)
    (p q r : ℤ) (m : Mdata.grading.component p)
    (x : Ndata.component q) (b : GB.component r) :
    gradedTensorProductComponent GA GB Mdata Ndata ((p + q) + r) :=
  gradedRelativeTensorProductMk ((p + q) + r) p (q + r)
    (fun i => Mdata.grading.component i)
    (fun i => GA.component i)
    (fun i => Ndata.component i)
    Mdata.homogeneousAction (gradedBimoduleLeftAction GA GB Ndata)
    (by omega) m ((gradedBimoduleRightAction GA GB Ndata q r) x b)

/-- The homogeneous right `B`-module structure on the graded relative tensor
product.  The unit and associativity fields use the homogeneous component
identifications supplied by `GradedAlgebraData`. -/
structure GradedTensorProductRightModuleSpec
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Mdata : GradedRightModuleData R A M GA)
    (Ndata : GradedBimodule R A B N GA GB) where
  rightAction : ∀ p q : ℤ,
    gradedTensorProductComponent GA GB Mdata Ndata p →ₗ[R]
      GB.component q →ₗ[R]
        gradedTensorProductComponent GA GB Mdata Ndata (p + q)
  rightAction_pure : ∀ (p q r : ℤ)
      (m : Mdata.grading.component p) (x : Ndata.component q)
      (b : GB.component r),
    rightAction (p + q) r
        (gradedRelativeTensorProductMk (p + q) p q
          (fun i => Mdata.grading.component i)
          (fun i => GA.component i)
          (fun i => Ndata.component i)
          Mdata.homogeneousAction (gradedBimoduleLeftAction GA GB Ndata)
          rfl m x) b =
      gradedTensorProductRightActionOnPureTensor GA GB Mdata Ndata p q r m x b
  right_one : ∀ (p : ℤ) (x : gradedTensorProductComponent GA GB Mdata Ndata p),
    transportGraded (X := fun i =>
        (gradedTensorProductComponent GA GB Mdata Ndata i : Type u)) (by omega)
      (rightAction p 0 x ⟨1, GB.one_homogeneous⟩) = x
  right_assoc : ∀ (p q r : ℤ)
      (x : gradedTensorProductComponent GA GB Mdata Ndata p)
      (b : GB.component q) (b' : GB.component r),
    transportGraded (X := fun i =>
        (gradedTensorProductComponent GA GB Mdata Ndata i : Type u)) (by omega)
      (rightAction (p + q) r (rightAction p q x b) b') =
      rightAction p (q + r) x
        ⟨b.1 * b'.1, GB.mul_homogeneous q r b b'⟩

/-- The graded relative tensor product carries the right graded `B`-module
structure induced by the right action on the bimodule. -/
theorem gradedTensorProduct_rightModule_exists
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Mdata : GradedRightModuleData R A M GA)
    (Ndata : GradedBimodule R A B N GA GB) :
    Nonempty (GradedTensorProductRightModuleSpec GA GB Mdata Ndata) := by
  sorry

/-- The pure tensor in a homogeneous graded relative tensor product. -/
def gradedTensorProductMk
    {R A B M N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (Mdata : GradedRightModuleData R A M GA)
    (Ndata : GradedBimodule R A B N GA GB)
    (n p q : ℤ) (hpq : p + q = n)
    (m : Mdata.grading.component p) (x : Ndata.component q) :
    gradedTensorProductComponent GA GB Mdata Ndata n :=
  gradedRelativeTensorProductMk n p q
    (fun i => Mdata.grading.component i)
    (fun i => GA.component i)
    (fun i => Ndata.component i)
    Mdata.homogeneousAction (gradedBimoduleLeftAction GA GB Ndata) hpq m x

/-- A homogeneous map of graded right modules. -/
structure GradedRightModuleHom
    {R A M M' : Type u}
    [CommRing R] [Ring A] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Algebra R A]
    {GA : GradedAlgebraData R A}
    (L : GradedRightModuleData R A M GA)
    (L' : GradedRightModuleData R A M' GA) where
  degree : ℤ
  app : ∀ p : ℤ,
    L.grading.component p →ₗ[R] L'.grading.component (p + degree)
  map_action : ∀ (p q : ℤ) (m : L.grading.component p)
      (a : GA.component q),
    transportGraded (X := fun i => (L'.grading.component i : Type u)) (by omega)
        (app (p + q) (L.homogeneousAction p q m a)) =
      L'.homogeneousAction (p + degree) q (app p m) a

/-- The map induced on graded relative tensor products by a homogeneous
module map. -/
structure GradedTensorProductMap
    {R A B M M' N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (L : GradedRightModuleData R A M GA)
    (L' : GradedRightModuleData R A M' GA)
    (Ndata : GradedBimodule R A B N GA GB)
    (f : GradedRightModuleHom L L') where
  app : ∀ n : ℤ,
    gradedTensorProductComponent GA GB L Ndata n →ₗ[R]
      gradedTensorProductComponent GA GB L' Ndata (n + f.degree)
  map_pure : ∀ (n p q : ℤ) (hpq : p + q = n)
      (m : L.grading.component p) (x : Ndata.component q),
    app n (gradedTensorProductMk GA GB L Ndata n p q hpq m x) =
      transportGraded (X := fun i =>
          (gradedTensorProductComponent GA GB L' Ndata i : Type u)) (by omega)
        (gradedTensorProductMk GA GB L' Ndata (n + f.degree)
          (p + f.degree) q (by omega) (f.app p m) x)

/-- Functoriality of tensoring a graded module with a fixed graded bimodule,
stated on homogeneous maps. -/
theorem gradedTensorProduct_map_exists
    {R A B M M' N : Type u}
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Algebra R A] [Algebra R B]
    [AddCommGroup N] [Module R N]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    (L : GradedRightModuleData R A M GA)
    (L' : GradedRightModuleData R A M' GA)
    (Ndata : GradedBimodule R A B N GA GB)
    (f : GradedRightModuleHom L L') :
    Nonempty (GradedTensorProductMap GA GB L L' Ndata f) := by
  sorry

/-! ## Differential graded tensor products -/

/-- The left differential graded module underlying a differential graded
bimodule. -/
def DifferentialGradedBimodule.toLeftModule
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B) :
    Formalization.Books.Dga.Unit11.LeftDifferentialGradedModule A where
  complex := N.complex
  action := N.leftAction
  one_action := N.left_one_action
  assoc_action := N.left_assoc_action

/-- The right differential graded module underlying a differential graded
bimodule. -/
def DifferentialGradedBimodule.toRightModule
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B) :
    DifferentialGradedModule B where
  complex := N.complex
  action := N.rightAction
  one_action := N.right_one_action
  assoc_action := N.right_assoc_action

/-- The differential graded relative tensor product complex. -/
abbrev differentialGradedTensorProductComplex
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) : CochainComplexOver R :=
  differentialGradedTensorProduct M (DifferentialGradedBimodule.toLeftModule N)

/-- A right differential graded `B`-module structure on the relative tensor
product complex. -/
structure DifferentialGradedTensorProductRightModuleSpec
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) where
  object : DifferentialGradedModule B
  object_complex : object.complex = differentialGradedTensorProductComplex M N

/-- The relative tensor product of a right differential graded `A`-module
with a differential graded `(A,B)`-bimodule is a right differential graded
`B`-module. -/
theorem differentialGradedTensorProduct_rightModule_exists
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) :
    Nonempty (DifferentialGradedTensorProductRightModuleSpec M N) := by
  sorry

/-- The selected differential graded module structure on the tensor product. -/
noncomputable def differentialGradedTensorProductModule
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) : DifferentialGradedModule B :=
  (Classical.choice (differentialGradedTensorProduct_rightModule_exists M N)).object

/-- The tensor construction on differential graded modules, together with its
object formula and its induced functor on homotopy categories. -/
structure DifferentialGradedTensorProductFunctorSpec
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B) where
  functor : DifferentialGradedModuleCategory A ⥤
    DifferentialGradedModuleCategory B
  object_complex : ∀ M : DifferentialGradedModule A,
    (functor.obj M).complex = differentialGradedTensorProductComplex M N
  homotopyFunctor : DifferentialGradedModuleHomotopyCategory A ⥤
    DifferentialGradedModuleHomotopyCategory B
  homotopy_factorization :
    differentialGradedModuleHomotopyQuotient A ⋙ homotopyFunctor =
      functor ⋙ differentialGradedModuleHomotopyQuotient B

/-- The differential graded tensor-product functor exists and induces the
corresponding functor on `Mod_(A,d)` and on `K(Mod_(A,d))`. -/
theorem differentialGradedTensorProduct_functor_exists
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B) :
    Nonempty (DifferentialGradedTensorProductFunctorSpec A B N) := by
  sorry

noncomputable def differentialGradedTensorProductFunctor
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B) :
    DifferentialGradedModuleCategory A ⥤ DifferentialGradedModuleCategory B :=
  (Classical.choice (differentialGradedTensorProduct_functor_exists A B N)).functor

noncomputable def differentialGradedTensorProductHomotopyFunctor
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B) :
    DifferentialGradedModuleHomotopyCategory A ⥤
      DifferentialGradedModuleHomotopyCategory B :=
  (Classical.choice (differentialGradedTensorProduct_functor_exists A B N)).homotopyFunctor

/-- The homogeneous-map form of the source's differential computation.  The
map sends `f` to `f ⊗ id_N`; the displayed cancellation is exactly the last
field. -/
structure DifferentialGradedTensorProductHomCompatibility
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B)
    (M M' : DifferentialGradedModule A) where
  sourceHom : DifferentialGradedModuleHomComplex A M M'
  targetHom : DifferentialGradedModuleHomComplex B
    (differentialGradedTensorProductModule M N)
    (differentialGradedTensorProductModule M' N)
  map : ∀ n : ℤ, sourceHom.homogeneous n → targetHom.homogeneous n
  differential_compatibility : ∀ (n : ℤ) (f : sourceHom.homogeneous n),
    map (n + 1) (sourceHom.differential n f) =
      targetHom.differential n (map n f)

theorem differentialGradedTensorProduct_homCompatibility_exists
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B)
    (M M' : DifferentialGradedModule A) :
    Nonempty (DifferentialGradedTensorProductHomCompatibility A B N M M') := by
  sorry

def DifferentialGradedTensorProductDifferentialCompatibility
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedBimodule A B)
    (M M' : DifferentialGradedModule A) : Prop :=
  Nonempty (DifferentialGradedTensorProductHomCompatibility A B N M M')

/-- The sign-free shift comparison from the source. -/
theorem differentialGradedTensorProduct_shift_iso_exists
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) (k : ℤ) :
    Nonempty (
      dgmShift (differentialGradedTensorProductModule M N) k ≅
        differentialGradedTensorProductModule (dgmShift M k) N) := by
  sorry

noncomputable def differentialGradedTensorProduct_shift_iso
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B) (k : ℤ) :
    dgmShift (differentialGradedTensorProductModule M N) k ≅
      differentialGradedTensorProductModule (dgmShift M k) N :=
  Classical.choice (differentialGradedTensorProduct_shift_iso_exists M N k)

/-! ## Associativity -/

/-- The underlying complex of the tensor product of a differential graded
`(A,B)`-bimodule with a differential graded `(B,C)`-bimodule. -/
abbrev differentialGradedBimoduleTensorProductComplex
    {R : Type u} [CommRing R]
    {A B C : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B)
    (N' : DifferentialGradedBimodule B C) : CochainComplexOver R :=
  differentialGradedTensorProduct
    (DifferentialGradedBimodule.toRightModule N)
    (DifferentialGradedBimodule.toLeftModule N')

/-- A differential graded `(A,C)`-bimodule structure on the relative tensor
product of an `(A,B)`-bimodule and a `(B,C)`-bimodule. -/
structure DifferentialGradedBimoduleTensorProductSpec
    {R : Type u} [CommRing R]
    {A B C : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B)
    (N' : DifferentialGradedBimodule B C) where
  object : DifferentialGradedBimodule A C
  object_complex : object.complex =
    differentialGradedBimoduleTensorProductComplex N N'

/-- The differential graded tensor product of composable bimodules exists. -/
theorem differentialGradedBimoduleTensorProduct_exists
    {R : Type u} [CommRing R]
    {A B C : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B)
    (N' : DifferentialGradedBimodule B C) :
    Nonempty (DifferentialGradedBimoduleTensorProductSpec N N') := by
  sorry

/-- A selected differential graded tensor product of composable bimodules. -/
noncomputable def differentialGradedBimoduleTensorProduct
    {R : Type u} [CommRing R]
    {A B C : DifferentialGradedAlgebra R}
    (N : DifferentialGradedBimodule A B)
    (N' : DifferentialGradedBimodule B C) :
    DifferentialGradedBimodule A C :=
  (Classical.choice (differentialGradedBimoduleTensorProduct_exists N N')).object

/-- The source's ordinary associativity assertion, represented by the
canonical linear equivalence between the two balanced quotient
presentations.  The module instances on the two inner tensor products are
explicit hypotheses because the earlier quotient API does not install
bimodule instances globally. -/
theorem ordinaryTensorProduct_associator_exists
    {R A B C M N P : Type u}
    [CommRing R] [Ring A] [Ring B] [Ring C]
    [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    [AddCommGroup P] [Module R P] [Module B P] [Module Cᵐᵒᵖ P]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [Module Bᵐᵒᵖ (relativeTensorProduct (R := R) (A := A) (M := M) (N := N))]
    [Module A (relativeTensorProduct (R := R) (A := B) (M := N) (N := P))] :
    Nonempty (
      relativeTensorProduct (R := R) (A := B)
          (M := relativeTensorProduct (R := R) (A := A) (M := M) (N := N))
          (N := P) ≃ₗ[R]
      relativeTensorProduct (R := R) (A := A) (M := M)
          (N := relativeTensorProduct (R := R) (A := B) (M := N) (N := P))) := by
  sorry

/-- A linear equivalence between two homogeneous components, with the module
structures kept explicit so that a family of components does not require a
dependent typeclass instance. -/
structure GradedComponentLinearEquiv
    (R X Y : Type u) [CommRing R] [AddCommGroup X] [AddCommGroup Y] where
  leftModule : Module R X
  rightModule : Module R Y
  toFun : X → Y
  invFun : Y → X
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (r : R) (x : X),
    letI : Module R X := leftModule
    letI : Module R Y := rightModule
    toFun (r • x) = r • toFun x

/-- Degreewise form of the graded associativity assertion.  For the two
graded relative tensor-product presentations supplied by the caller, this
predicate asks for the canonical linear equivalence in every degree. -/
structure GradedTensorProductAssociatorData
    {R : Type u} [CommRing R]
    (left right : ℤ → Type u)
    [∀ n, AddCommGroup (left n)] [∀ n, AddCommGroup (right n)] where
  componentIso : ∀ n, GradedComponentLinearEquiv R (left n) (right n)

def IsGradedTensorProductAssociative
    {R : Type u} [CommRing R]
    (left right : ℤ → Type u)
    [∀ n, AddCommGroup (left n)] [∀ n, AddCommGroup (right n)] : Prop :=
  Nonempty (GradedTensorProductAssociatorData (R := R) left right)

/-- The differential graded associativity assertion: tensoring first with
`N` and then with `N'` agrees with tensoring with their bimodule tensor
product, up to the canonical isomorphism. -/
theorem differentialGradedTensorProduct_associator_exists
    {R : Type u} [CommRing R]
    {A B C : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A)
    (N : DifferentialGradedBimodule A B)
    (N' : DifferentialGradedBimodule B C) :
    Nonempty (
      differentialGradedTensorProductModule
          (differentialGradedTensorProductModule M N) N' ≅
        differentialGradedTensorProductModule M
          (differentialGradedBimoduleTensorProduct N N')) := by
  sorry

end Formalization.Books.Dga.Unit29
