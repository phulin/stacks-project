import Formalization.Books.Dga.Unit03.Definitions
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Basic

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
          transportComponent (C := M.complex) (by omega)
            (M.actionOnHomogeneous n (m + 1) x
              ((A.complex.d m (m + 1)).hom a))

/-- The chain-map condition on the action is the Leibniz rule. -/
theorem DifferentialGradedModule.satisfiesLeibniz
    {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : M.SatisfiesLeibniz := by
  sorry

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
    sorry
  add_mem' := by
    intro f g hf hg
    sorry
  neg_mem' := by
    intro f hf
    sorry

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
  (dgmCohomologyFunctor (A := A) n).map f

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
      (dgmCohomologyMap S.f (n + 1)) (by sorry)).Exact

theorem dgm_long_exact_cohomology_fragment
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : S.ShortExact) (n : ℤ) : DGMLongExactFragment hS n := by
  sorry

/-! ## Shifts -/

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
  (CochainComplex.mapBifunctorShift₁Iso M.complex A.complex
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) k).hom ≫
    (CategoryTheory.shiftFunctor (CochainComplexOver R) k).map M.action

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
          ((CochainComplex.mapBifunctorShift₁Iso M.complex A.complex
              (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) k).hom.f (n + m)
            ((HomologicalComplex.ιTensorObj
                ((CategoryTheory.shiftFunctor (CochainComplexOver R) k).obj M.complex)
                A.complex n m (n + m) rfl).hom (x ⊗ₜ[R] a))) := rfl

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

end Formalization.Books.Dga.Unit04
