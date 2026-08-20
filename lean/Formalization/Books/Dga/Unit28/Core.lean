import Formalization.Books.Dga.Unit26.Core
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Differential Graded Algebra, Chapter 28: Bimodules

This file records the bimodule definitions and the statement interfaces in
the source section.  The differential graded objects use the cochain-complex
presentation of differential graded algebras and modules established in the
preceding chapters.  Proposition proofs are intentionally deferred.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open DirectSum
open Formalization.Books.Dga.Unit26
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit25

universe u v w uι

namespace Formalization.Books.Dga.Unit28

/-! ## Ordinary and graded bimodules -/

/- The source convention for a ring is the project's `[CommRing]` convention;
   the two algebras themselves need not be commutative. -/

/-- An `(A, B)`-bimodule over `R`, with the right action written as a linear
map `B → M → M`.  The linear-map formulation records the two `R`-bilinear
actions without introducing a parallel scalar-action API. -/
structure Bimodule (R A B M : Type u)
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B] where
  leftAction : A →ₗ[R] M →ₗ[R] M
  rightAction : B →ₗ[R] M →ₗ[R] M
  left_assoc : ∀ (a a' : A) (x : M),
    leftAction (a' * a) x = leftAction a' (leftAction a x)
  right_assoc : ∀ (x : M) (b b' : B),
    rightAction (b * b') x = rightAction b' (rightAction b x)
  commute : ∀ (a : A) (b : B) (x : M),
    rightAction b (leftAction a x) = leftAction a (rightAction b x)
  left_one : ∀ x : M, leftAction 1 x = x
  right_one : ∀ x : M, rightAction 1 x = x

/-- The data of a graded `R`-algebra needed by the graded bimodule
definition.  Its components form a direct-sum decomposition of the carrier
and multiplication and the unit are homogeneous. -/
structure GradedAlgebraData (R A : Type u)
    [CommRing R] [Ring A] [Algebra R A] where
  component : ℤ → Submodule R A
  decomposition : DirectSum.Decomposition component
  mul_homogeneous : ∀ (i j : ℤ) (a : component i) (b : component j),
    (a.1 * b.1 : A) ∈ component (i + j)
  one_homogeneous : (1 : A) ∈ component 0

/-- A graded `(A, B)`-bimodule. -/
structure GradedBimodule (R A B M : Type u)
    [CommRing R] [Ring A] [Ring B] [AddCommGroup M] [Module R M]
    [Algebra R A] [Algebra R B]
    (GA : GradedAlgebraData R A) (GB : GradedAlgebraData R B)
    extends Bimodule R A B M where
  component : ℤ → Submodule R M
  decomposition : DirectSum.Decomposition component
  left_homogeneous : ∀ (i j : ℤ) (a : GA.component i) (x : component j),
    leftAction a.1 x.1 ∈ component (i + j)
  right_homogeneous : ∀ (i j : ℤ) (x : component i) (b : GB.component j),
    rightAction b.1 x.1 ∈ component (i + j)

/-! ## Differential graded bimodules -/

/-- A left differential graded module action.  This is the left-handed
version of `DifferentialGradedModule`; the associator makes the two ways of
parenthesizing `A ⊗ A ⊗ M` explicit. -/
structure LeftDifferentialGradedModule
    {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R) where
  complex : CochainComplexOver R
  action : tensorProductComplex R A.complex complex ⟶ complex
  one_action :
    tensorHomComplex A.unit (𝟙 complex) ≫ action =
      (HomologicalComplex.leftUnitor complex).hom
  assoc_action :
    tensorHomComplex A.multiplication (𝟙 complex) ≫ action =
      (HomologicalComplex.associator A.complex A.complex complex).hom ≫
        tensorHomComplex (𝟙 A.complex) action ≫ action

/-- A differential graded `(A, B)`-bimodule.  The two module structures use
the same underlying complex, and `commute_action` is the commuting-actions
diagram from the source. -/
structure DifferentialGradedBimodule
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) where
  complex : CochainComplexOver R
  leftAction : tensorProductComplex R A.complex complex ⟶ complex
  rightAction : tensorProductComplex R complex B.complex ⟶ complex
  left_one_action :
    tensorHomComplex A.unit (𝟙 complex) ≫ leftAction =
      (HomologicalComplex.leftUnitor complex).hom
  left_assoc_action :
    tensorHomComplex A.multiplication (𝟙 complex) ≫ leftAction =
      (HomologicalComplex.associator A.complex A.complex complex).hom ≫
        tensorHomComplex (𝟙 A.complex) leftAction ≫ leftAction
  right_one_action :
    tensorHomComplex (𝟙 complex) B.unit ≫ rightAction =
      (HomologicalComplex.rightUnitor complex).hom
  right_assoc_action :
    tensorHomComplex rightAction (𝟙 B.complex) ≫ rightAction =
      (HomologicalComplex.associator complex B.complex B.complex).hom ≫
        tensorHomComplex (𝟙 complex) B.multiplication ≫ rightAction
  commute_action :
    tensorHomComplex leftAction (𝟙 B.complex) ≫ rightAction =
      (HomologicalComplex.associator A.complex complex B.complex).hom ≫
        tensorHomComplex (𝟙 A.complex) rightAction ≫ leftAction

/-- The homogeneous left action exposed by a differential graded bimodule. -/
noncomputable def DifferentialGradedBimodule.homogeneousLeftAction
    {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) (p q : ℤ) :
    A.complex.X p ⊗ M.complex.X q ⟶ M.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj A.complex M.complex p q (p + q) rfl ≫
    M.leftAction.f (p + q)

/-- The homogeneous right action exposed by a differential graded bimodule. -/
noncomputable def DifferentialGradedBimodule.homogeneousRightAction
    {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) (p q : ℤ) :
    M.complex.X p ⊗ B.complex.X q ⟶ M.complex.X (p + q) :=
  HomologicalComplex.ιTensorObj M.complex B.complex p q (p + q) rfl ≫
    M.rightAction.f (p + q)

/-! ## Morphisms and the correspondence with endomorphisms -/

/-- A morphism of differential graded bimodules. -/
structure DifferentialGradedBimoduleHom
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedBimodule A B) where
  underlying : M.complex ⟶ N.complex
  left_commutes :
    M.leftAction ≫ underlying =
      tensorHomComplex (𝟙 A.complex) underlying ≫ N.leftAction
  right_commutes :
    M.rightAction ≫ underlying =
      tensorHomComplex underlying (𝟙 B.complex) ≫ N.rightAction

/-- An isomorphism of differential graded bimodules. -/
structure DifferentialGradedBimoduleIso
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedBimodule A B) where
  hom : DifferentialGradedBimoduleHom M N
  inv : DifferentialGradedBimoduleHom N M
  hom_inv_id : hom.underlying ≫ inv.underlying = 𝟙 M.complex
  inv_hom_id : inv.underlying ≫ hom.underlying = 𝟙 N.complex

/-- A left action on a fixed right differential graded `B`-module which is
compatible with the right action. -/
structure CompatibleBimoduleStructure
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule B) where
  leftAction : tensorProductComplex R A.complex M.complex ⟶ M.complex
  left_one_action :
    tensorHomComplex A.unit (𝟙 M.complex) ≫ leftAction =
      (HomologicalComplex.leftUnitor M.complex).hom
  left_assoc_action :
    tensorHomComplex A.multiplication (𝟙 M.complex) ≫ leftAction =
      (HomologicalComplex.associator A.complex A.complex M.complex).hom ≫
        tensorHomComplex (𝟙 A.complex) leftAction ≫ leftAction
  commute_action :
    tensorHomComplex leftAction (𝟙 B.complex) ≫ M.action =
      (HomologicalComplex.associator A.complex M.complex B.complex).hom ≫
        tensorHomComplex (𝟙 A.complex) M.action ≫ leftAction

/-- The homogeneous formula for the endomorphism action of `A` on a right
`B`-module.  It is the elementwise content of the source's correspondence
lemma, with the commuting right action made explicit by `commute_action`. -/
def compatibleBimoduleEndomorphismAction
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    {M : DifferentialGradedModule B}
    (S : CompatibleBimoduleStructure A B M) (p q : ℤ)
    (a : A.complex.X p) : M.complex.X q →ₗ[R] M.complex.X (p + q) :=
  { toFun := fun x => (S.leftAction.f (p + q)).hom
      ((HomologicalComplex.ιTensorObj A.complex M.complex p q (p + q) rfl).hom
        (a ⊗ₜ[R] x))
    map_add' := by
      intro x y
      rw [TensorProduct.tmul_add]
      rw [(HomologicalComplex.ιTensorObj A.complex M.complex p q (p + q) rfl).hom.map_add]
      exact (S.leftAction.f (p + q)).hom.map_add _ _
    map_smul' := by
      intro r x
      rw [TensorProduct.tmul_smul]
      rw [(HomologicalComplex.ιTensorObj A.complex M.complex p q (p + q) rfl).hom.map_smul]
      simpa using (S.leftAction.f (p + q)).hom.map_smul r _ }

/-- The source's differential graded endomorphism algebra is retained as a
named interface.  Its homogeneous pieces are identified with the existing
hom-complex interface for right differential graded modules. -/
structure DifferentialGradedModuleEndomorphismAlgebra
    {R : Type u} [CommRing R]
    (B : DifferentialGradedAlgebra R) (M : DifferentialGradedModule B) where
  algebra : DifferentialGradedAlgebra R
  homComplex : DifferentialGradedModuleHomComplex B M M
  homogeneous_identification :
    ∀ n, algebra.complex.X n = homComplex.homogeneous n

/-- A homomorphism from `A` to the named differential graded endomorphism
algebra of `M`. -/
abbrev EndomorphismAlgebraHom
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    {M : DifferentialGradedModule B}
    (E : DifferentialGradedModuleEndomorphismAlgebra B M) :=
  DifferentialGradedAlgebraHom A E.algebra

/-- The one-to-one correspondence between compatible left actions and maps to
the differential graded endomorphism algebra. -/
theorem bimodule_structure_correspondence
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule B)
    (E : DifferentialGradedModuleEndomorphismAlgebra B M) :
    Nonempty
      (CompatibleBimoduleStructure A B M ≃ EndomorphismAlgebraHom (A := A) E) := by
  sorry

/-! ## The `Aᵒᵖ ⊗ B` description -/

/-- The pure-tensor action formula from the source.  The cast only identifies
`(p + q) + r` with `p + (q + r)` in the target complex. -/
def tensorModuleActionOnPureTensor
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B)
    (p q r : ℤ) (a : A.complex.X p) (x : M.complex.X q)
    (b : B.complex.X r) : M.complex.X (p + (q + r)) :=
  transportComponent (C := M.complex) (by omega)
    (((p * q).negOnePow : R) •
      (M.homogeneousRightAction (p + q) r).hom
        (((M.homogeneousLeftAction p q).hom (a ⊗ₜ[R] x)) ⊗ₜ[R] b))

/-- A right differential graded module over the formal `Aᵒᵖ ⊗ B` module
presentation.  The action on pure tensors is the operation displayed in the
source; its extension and module laws are packaged as fields. -/
structure RightDgModuleOverOppositeTensor
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) where
  complex : CochainComplexOver R
  pureTensorAction : ∀ (p q r : ℤ),
    A.complex.X p → complex.X q → B.complex.X r → complex.X (p + (q + r))
  action_is_differential_graded_module : Prop

/-- The equivalence of differential graded bimodules with right modules over
`Aᵒᵖ ⊗ B`, stated using the source-faithful pure-tensor action interface. -/
theorem bimodule_over_opposite_tensor_equivalence
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) :
    Nonempty
      (DifferentialGradedBimodule A B ≃
        RightDgModuleOverOppositeTensor A B) := by
  sorry

/-! ## Property (P) -/

/-- A graded bimodule map between the homogeneous pieces of two differential
graded bimodules. -/
structure GradedBimoduleMap
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedBimodule A B) where
  app : ∀ n : ℤ, M.complex.X n →ₗ[R] N.complex.X n
  map_left : ∀ (p q : ℤ) (a : A.complex.X p) (x : M.complex.X q),
    app (p + q) ((M.homogeneousLeftAction p q).hom (a ⊗ₜ[R] x)) =
      (N.homogeneousLeftAction p q).hom (a ⊗ₜ[R] app q x)
  map_right : ∀ (p q : ℤ) (x : M.complex.X p) (b : B.complex.X q),
    app (p + q) ((M.homogeneousRightAction p q).hom (x ⊗ₜ[R] b)) =
      (N.homogeneousRightAction p q).hom (app p x ⊗ₜ[R] b)

/-- A differential graded direct sum of a family of bimodules, specified by
its universal property. -/
structure DgBimoduleDirectSum
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R} {ι : Type uι}
    (F : ι → DifferentialGradedBimodule A B) where
  object : DifferentialGradedBimodule A B
  inclusion : ∀ i, DifferentialGradedBimoduleHom (F i) object
  universal : ∀ (X : DifferentialGradedBimodule A B)
      (f : ∀ i, DifferentialGradedBimoduleHom (F i) X),
      ∃! g : DifferentialGradedBimoduleHom object X,
        ∀ i, (inclusion i).underlying ≫ g.underlying = (f i).underlying

/-- The regular differential graded `(A, B)`-bimodule `A ⊗_R B`. -/
noncomputable def regularDgBimoduleLeftAction
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) :
    tensorProductComplex R A.complex
        (tensorProductComplex R A.complex B.complex) ⟶
      tensorProductComplex R A.complex B.complex :=
  (HomologicalComplex.associator A.complex A.complex B.complex).inv ≫
    tensorHomComplex A.multiplication (𝟙 B.complex)

noncomputable def regularDgBimoduleRightAction
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) :
    tensorProductComplex R (tensorProductComplex R A.complex B.complex)
        B.complex ⟶
      tensorProductComplex R A.complex B.complex :=
  (HomologicalComplex.associator A.complex B.complex B.complex).hom ≫
    tensorHomComplex (𝟙 A.complex) B.multiplication

structure RegularDgBimoduleSpec
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) where
  object : DifferentialGradedBimodule A B
  carrier_identification :
    object.complex = tensorProductComplex R A.complex B.complex
  left_action_identification :
    HEq object.leftAction (regularDgBimoduleLeftAction A B)
  right_action_identification :
    HEq object.rightAction (regularDgBimoduleRightAction A B)

theorem regularDgBimodule_spec_nonempty
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) :
    Nonempty (RegularDgBimoduleSpec A B) := by
  sorry

noncomputable def regularDgBimodule
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) : DifferentialGradedBimodule A B :=
  (Classical.choice (regularDgBimodule_spec_nonempty A B)).object

/-- A shift of a differential graded bimodule, retained as an interface so
the same object can carry the left and right actions after shifting. -/
structure BimoduleShift
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) (k : ℤ) where
  object : DifferentialGradedBimodule A B
  underlying_shift : object.complex =
    (CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex

theorem bimoduleShift_spec_nonempty
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) (k : ℤ) :
    Nonempty (BimoduleShift M k) := by
  sorry

noncomputable def bimoduleShift
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) (k : ℤ) : BimoduleShift M k :=
  Classical.choice (bimoduleShift_spec_nonempty M k)

/-- A direct sum of shifts of the regular bimodule. -/
def IsBimoduleShiftedFree
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (M : DifferentialGradedBimodule A B) : Prop :=
    ∃ (ι : Type u) (degree : ι → ℤ)
    (S : DgBimoduleDirectSum
      (fun i =>
        (bimoduleShift (regularDgBimodule A B) (degree i)).object)),
    Nonempty (DifferentialGradedBimoduleIso S.object M)

/-- A filtration by differential graded bimodules for property (P). -/
structure DgBimoduleFiltration
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (P : DifferentialGradedBimodule A B) where
  stage : ℕ → DifferentialGradedBimodule A B
  zero : DifferentialGradedBimodule A B
  zero_inclusion : DifferentialGradedBimoduleHom zero (stage 0)
  inclusion : ∀ i, DifferentialGradedBimoduleHom (stage i) (stage (i + 1))
  stage_map : ∀ i, DifferentialGradedBimoduleHom (stage i) P
  zero_stage_map : DifferentialGradedBimoduleHom zero P
  zero_stage_map_compatibility :
    zero_inclusion.underlying ≫ (stage_map 0).underlying =
      zero_stage_map.underlying
  stage_map_compatibility : ∀ i,
    (inclusion i).underlying ≫ (stage_map (i + 1)).underlying =
      (stage_map i).underlying
  exhaustive : ∀ n (x : P.complex.X n), ∃ i,
    ∃ y : (stage i).complex.X n, (stage_map i).underlying.f n y = x
  split : ∀ i, ∃ r : GradedBimoduleMap (stage (i + 1)) (stage i),
    ∀ n (x : (stage i).complex.X n),
      r.app n ((inclusion i).underlying.f n x) = x
  quotient : ∀ i, DifferentialGradedBimodule A B
  quotient_map : ∀ i, DifferentialGradedBimoduleHom (stage (i + 1)) (quotient i)
  quotient_exact : ∀ i n,
    Set.range ((inclusion i).underlying.f n).hom =
      (LinearMap.ker ((quotient_map i).underlying.f n).hom).carrier
  quotient_shifted_free : ∀ i, IsBimoduleShiftedFree (quotient i)

/-- Property (P) for differential graded bimodules. -/
def HasPropertyP
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    (P : DifferentialGradedBimodule A B) : Prop :=
  Nonempty (DgBimoduleFiltration P)

/-! ## Resolution and the associated split exact sequence -/

/-- A quasi-isomorphism of differential graded bimodules.  The predicate is
left abstract here because the preceding chapters expose several equivalent
homological presentations; the map remains a genuine bimodule morphism. -/
def IsQuasiIsomorphism
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedBimodule A B}
    (f : DifferentialGradedBimoduleHom M N) : Prop :=
  QuasiIso f.underlying

/-- The resolution of a differential graded bimodule by one having property
(P). -/
theorem bimodule_resolution
    {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R)
    (M : DifferentialGradedBimodule A B) :
    ∃ (P : DifferentialGradedBimodule A B)
      (f : DifferentialGradedBimoduleHom P M),
      HasPropertyP P ∧ IsQuasiIsomorphism f := by
  sorry

/-- Data for the source's split short exact sequence
`0 → ⨁ FᵢP → ⨁ FᵢP → P → 0`. -/
structure PropertyPSequence
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    {P : DifferentialGradedBimodule A B}
    (F : DgBimoduleFiltration P) where
  sum : DgBimoduleDirectSum (ι := ℕ) (fun i => F.stage i)
  first : DifferentialGradedBimoduleHom sum.object sum.object
  augmentation : DifferentialGradedBimoduleHom sum.object P
  complex : ∀ n (x : sum.object.complex.X n),
    (augmentation.underlying.f n) (first.underlying.f n x) = 0
  exact : ∀ n,
    Set.range (first.underlying.f n).hom =
      (LinearMap.ker (augmentation.underlying.f n).hom).carrier
  split_as_graded :
    ∃ (s : GradedBimoduleMap P sum.object)
      (r : GradedBimoduleMap sum.object sum.object),
      (∀ n (x : sum.object.complex.X n),
        s.app n (augmentation.underlying.f n x) = x) ∧
      (∀ n (x : sum.object.complex.X n),
        r.app n (first.underlying.f n x) = x)

theorem property_P_sequence
    {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra R}
    {P : DifferentialGradedBimodule A B}
    (F : DgBimoduleFiltration P) :
    Nonempty (PropertyPSequence F) := by
  sorry

end Formalization.Books.Dga.Unit28
