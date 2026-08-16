import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic

/-!
# Common interfaces for the differential graded sheaf chapter

The chapter is about sheaves of modules on ringed sites.  The records in this
file expose the site, graded, differential, tensor, and homological data used
by the statements below.  The sheaf condition and the category constructions
are kept as explicit fields or propositions so that this chapter does not
introduce a second implementation of Mathlib's sheaf categories.
-/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The object-and-arrow data of a site used by the chapter. -/
structure RingedSite (R : Type u) [CommRing R] where
  Obj : Type v
  Hom : Obj → Obj → Type v
  id : (U : Obj) → Hom U U
  comp : {U V W : Obj} → Hom U V → Hom V W → Hom U W
  comp_id : ∀ {U V : Obj} (f : Hom U V), comp f (id V) = f
  id_comp : ∀ {U V : Obj} (f : Hom U V), comp (id U) f = f
  assoc : ∀ {U V W X : Obj} (f : Hom U V) (g : Hom V W) (h : Hom W X),
    comp (comp f g) h = comp f (comp g h)

abbrev SiteHom (S : RingedSite.{u,v} R) (U V : S.Obj) := S.Hom U V

/-- A morphism of the underlying sites.  The sheaf-theoretic maps are supplied
by the functorial records in the section files. -/
structure RingedSiteMorphism (S T : RingedSite.{u,v} R) where
  obj : S.Obj → T.Obj
  map : {U V : S.Obj} → SiteHom S U V → SiteHom T (obj U) (obj V)

/-- The Koszul sign appearing in the Leibniz rule. -/
def koszulSign (n : ℤ) : R := if n % 2 = 0 then 1 else -1

@[simp] theorem koszulSign_zero : koszulSign (R := R) 0 = 1 := by
  sorry

@[simp] theorem koszulSign_one : koszulSign (R := R) 1 = -1 := by
  sorry

/-- A family of `R`-module carriers indexed by the objects of a site. -/
abbrev ModuleFamily (S : RingedSite.{u,v} R) := S.Obj → Type u

/-- A graded family of module carriers. -/
abbrev GradedFamily (S : RingedSite.{u,v} R) := ℤ → ModuleFamily S

/-- A cochain family, with the square-zero assertion exposed as data. -/
structure CochainFamily (S : RingedSite.{u,v} R) where
  component : GradedFamily S
  differential : ∀ (n : ℤ) (U : S.Obj), component n U → component (n + 1) U
  differential_squared : Prop

structure CochainMap {S : RingedSite.{u,v} R} (M N : CochainFamily S) where
  app : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component n U
  commutes : Prop

/-- A graded algebra object, with multiplication and unit in each fibre. -/
structure GradedAlgebra (S : RingedSite.{u,v} R) where
  component : GradedFamily S
  mul : ∀ (n m : ℤ) (U : S.Obj),
    component n U → component m U → component (n + m) U
  one : ∀ U : S.Obj, component 0 U
  laws : Prop

structure GradedAlgebraHom {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) where
  app : ∀ (n : ℤ) (U : S.Obj), A.component n U → B.component n U
  map_mul : Prop
  map_one : Prop

/-- A right graded module over a graded algebra. -/
structure GradedModule (S : RingedSite.{u,v} R) (A : GradedAlgebra S) where
  component : GradedFamily S
  action : ∀ (n m : ℤ) (U : S.Obj),
    component n U → A.component m U → component (n + m) U
  laws : Prop

/-- A left graded module over a graded algebra. -/
structure LeftGradedModule (S : RingedSite.{u,v} R) (A : GradedAlgebra S) where
  component : GradedFamily S
  action : ∀ (n m : ℤ) (U : S.Obj),
    A.component n U → component m U → component (n + m) U
  laws : Prop

structure GradedModuleHom {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M N : GradedModule S A) where
  app : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component n U
  commutes : Prop

def GradedModuleHom.IsInjective {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} (f : GradedModuleHom M N) : Prop :=
  ∀ (n : ℤ) (U : S.Obj), Function.Injective (f.app n U)

/-- A degree-`k` map between graded modules. -/
structure HomogeneousMap {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M N : GradedModule S A) (k : ℤ) where
  app : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component (n + k) U

def HomogeneousMap.isModuleMap {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} {k : ℤ} (f : HomogeneousMap M N k) : Prop :=
  ∀ (n m : ℤ) (U : S.Obj) (x : M.component n U)
    (a : A.component m U),
    HEq (f.app (n + m) U (M.action n m U x a))
      (N.action (n + k) m U (f.app n U x) a)

/-- Composition of homogeneous maps.  The dependent degree equality is
recorded by transporting along associativity of addition. -/
def HomogeneousMap.comp {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N P : GradedModule S A} {k l : ℤ}
    (g : HomogeneousMap N P l) (f : HomogeneousMap M N k) :
    HomogeneousMap M P (k + l) where
  app n U x :=
    cast (congrArg (fun q : ℤ => P.component q U) (Int.add_assoc n k l))
      (g.app (n + k) U (f.app n U x))

/-- The graded part of a differential graded algebra. -/
structure DGAlgebra (S : RingedSite.{u,v} R) where
  component : GradedFamily S
  mul : ∀ (n m : ℤ) (U : S.Obj),
    component n U → component m U → component (n + m) U
  one : ∀ U : S.Obj, component 0 U
  graded_laws : Prop
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  differential_squared : Prop
  leibniz : Prop

def dgAlgebraToGradedAlgebra {S : RingedSite.{u,v} R} (A : DGAlgebra S) : GradedAlgebra S where
  component := A.component
  mul := A.mul
  one := A.one
  laws := A.graded_laws

structure DGAlgebraHom {S : RingedSite.{u,v} R} (A B : DGAlgebra S) where
  app : ∀ (n : ℤ) (U : S.Obj), A.component n U → B.component n U
  map_mul : Prop
  map_one : Prop
  commutes_with_differential : Prop

/-- A right differential graded module. -/
structure DGModule (S : RingedSite.{u,v} R) (A : DGAlgebra S) where
  component : GradedFamily S
  action : ∀ (n m : ℤ) (U : S.Obj),
    component n U → A.component m U → component (n + m) U
  graded_laws : Prop
  zero : ∀ (n : ℤ) (U : S.Obj), component n U
  neg : ∀ (n : ℤ) (U : S.Obj), component n U → component n U
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  differential_zero : ∀ (n : ℤ) (U : S.Obj),
    differential n U (zero n U) = zero (n + 1) U
  differential_squared : Prop
  leibniz : Prop

def dgModuleToGradedModule {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) : GradedModule S (dgAlgebraToGradedAlgebra A) where
  component := M.component
  action := M.action
  laws := M.graded_laws

structure DGModuleHom {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M N : DGModule S A) where
  app : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component n U
  commutes_with_action : Prop
  commutes_with_differential : Prop

def DGModuleHom.IsInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f : DGModuleHom M N) : Prop :=
  ∀ (n : ℤ) (U : S.Obj), Function.Injective (f.app n U)

/-- The commutator differential on a homogeneous map, expressed as the
property used by the later differential graded category statements. -/
def homogeneousDifferential {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} {k : ℤ}
    (f : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component (n + k) U) : Prop :=
  ∀ (n : ℤ) (U : S.Obj) (x : M.component n U),
    HEq (N.differential (n + k) U (f n U x))
      (cast
        (congrArg (fun q : ℤ => N.component q U)
          (by
            calc
              (n + 1) + k = n + (1 + k) := Int.add_assoc n 1 k
              _ = n + (k + 1) :=
                congrArg (fun q => n + q) (Int.add_comm 1 k)
              _ = (n + k) + 1 := (Int.add_assoc n k 1).symm))
        (if k % 2 = 0 then
          f (n + 1) U (M.differential n U x)
        else
          N.neg ((n + 1) + k) U (f (n + 1) U (M.differential n U x))))

/-- A differential graded bimodule. -/
structure DGBimodule (S : RingedSite.{u,v} R) (A B : DGAlgebra S) where
  component : GradedFamily S
  leftAction : ∀ (n m : ℤ) (U : S.Obj),
    A.component n U → component m U → component (n + m) U
  rightAction : ∀ (n m : ℤ) (U : S.Obj),
    component n U → B.component m U → component (n + m) U
  graded_bimodule_laws : Prop
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  differential_squared : Prop
  left_leibniz : Prop
  right_leibniz : Prop

abbrev GradedModuleCategory (S : RingedSite.{u,v} R) (A : GradedAlgebra S) :=
  GradedModule S A

abbrev DGModuleCategory (S : RingedSite.{u,v} R) (A : DGAlgebra S) :=
  DGModule S A

/-- Interfaces for the category-theoretic properties asserted in the source. -/
structure AbelianCategoryStatement (C : Type*) where
  has_zero : Nonempty C
  has_kernels : Prop
  has_cokernels : Prop
  exactness : Prop

structure GrothendieckCategoryStatement (C : Type*) where
  abelian : AbelianCategoryStatement C
  has_all_colimits : Prop
  filtered_colimits_exact : Prop
  has_generator : Prop

structure TriangulatedCategoryStatement (C : Type*) where
  shift : ℤ → C → C
  distinguished_triangles : Prop
  axioms : Prop

structure ExactFunctorStatement (A B : Type*) where
  object_map : A → B
  preserves_short_exact : Prop

structure AdjointStatement (A B : Type*) where
  left : A → B
  right : B → A
  hom_bijection : Prop

structure EquivalenceStatement (A B : Type*) where
  forward : A → B
  backward : B → A
  inverse_laws : Prop

/-- The cycle condition and acyclicity predicate used by the chapter. -/
def IsCycle {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) (n : ℤ) (U : S.Obj) (x : M.component n U) : Prop :=
  M.differential n U x = M.zero (n + 1) U

def IsAcyclic {S : RingedSite.{u,v} R} {A : DGAlgebra S} (M : DGModule S A) : Prop :=
  ∀ (n : ℤ) (U : S.Obj) (x : M.component n U),
    IsCycle M n U x →
      ∃ y : M.component (n - 1) U,
        HEq (M.differential (n - 1) U y) x

structure QuasiIsomorphismWitness {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (_f : DGModuleHom M N) where
  induces_cohomology_equivalence : Prop

def IsQuasiIsomorphism {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f : DGModuleHom M N) : Prop :=
  Nonempty (QuasiIsomorphismWitness f)

structure GoodnessWitness {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (_P : DGModule S A) where
  tensor_acyclicity : Prop
  extension_property : Prop
  localization_property : Prop

def IsGood {S : RingedSite.{u,v} R} (A : DGAlgebra S) (P : DGModule S A) : Prop :=
  Nonempty (GoodnessWitness A P)

def IsGradedInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop :=
  ∀ {M N : GradedModule S (dgAlgebraToGradedAlgebra A)}
    (b : GradedModuleHom M N),
    GradedModuleHom.IsInjective b →
    ∀ (a : GradedModuleHom M (dgModuleToGradedModule I)),
      ∃ h : GradedModuleHom N (dgModuleToGradedModule I),
        ∀ (n : ℤ) (U : S.Obj) (x : M.component n U),
          h.app n U (b.app n U x) = a.app n U x

structure FlatWitness {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (_P : DGModule S A) where
  tensor_exactness : Prop

def IsFlat {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (P : DGModule S A) : Prop := Nonempty (FlatWitness P)

/-- Shift of a graded family. -/
def shiftFamily {S : RingedSite.{u,v} R} (M : GradedFamily S) (k : ℤ) : GradedFamily S :=
  fun n U => M (n + k) U

structure ShiftedDGModule {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) (k : ℤ) where
  component : GradedFamily S
  component_eq : component = shiftFamily M.component k
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  differential_squared : Prop

/-- The graded family underlying a cone. -/
def coneFamily {S : RingedSite.{u,v} R} (K L : GradedFamily S) : GradedFamily S :=
  fun n U => L n U × K (n + 1) U

structure ConeData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (K L : DGModule S A) (_f : DGModuleHom K L) where
  component : GradedFamily S
  component_eq : component = coneFamily K.component L.component
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  module_action : Prop
  differential_squared : Prop

structure HomotopyData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (_f _g : DGModuleHom M N) where
  homotopy : ∀ (n : ℤ) (U : S.Obj), M.component n U → N.component (n - 1) U
  equation : Prop

def IsZeroDGModuleHom {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f : DGModuleHom M N) : Prop :=
  ∀ (n : ℤ) (U : S.Obj) (x : M.component n U),
    f.app n U x = N.zero n U

structure KInjectiveWitness {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (_I : DGModule S A) where
  acyclic_orthogonality : ∀ {M : DGModule S A},
    IsAcyclic M → ∀ (f : DGModuleHom M _I),
      ∃ z : DGModuleHom M _I,
        IsZeroDGModuleHom z ∧ Nonempty (HomotopyData f z)

def IsKInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop := Nonempty (KInjectiveWitness I)

def Homotopic {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f g : DGModuleHom M N) : Prop :=
  Nonempty (HomotopyData f g)

structure HomotopyCategoryData (S : RingedSite.{u,v} R) (A : DGAlgebra S) where
  Hom : (M N : DGModule S A) → Type (max u v)
  quotient_property : Prop

structure DerivedCategoryData (S : RingedSite.{u,v} R) (A : DGAlgebra S) where
  Hom : (M N : DGModule S A) → Type (max u v)
  localization_property : Prop
  triangulated : TriangulatedCategoryStatement (DGModuleCategory S A)

structure GradedTensorModel {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModule S A) (N : LeftGradedModule S A) where
  component : GradedFamily S
  balanced : Prop
  universal : Prop

structure DGTensorModel {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M N : DGModule S A) where
  component : GradedFamily S
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  balanced : Prop
  leibniz : Prop
  differential_squared : Prop

def gradedTensorProduct {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M : GradedModule S A} {N : LeftGradedModule S A}
    (T : GradedTensorModel M N) : GradedFamily S := T.component

def dgTensorProduct {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (T : DGTensorModel M N) : GradedFamily S := T.component

structure InternalHomModel {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M N : GradedModule S A) where
  component : GradedFamily S
  module_map_property : Prop
  composition_property : Prop

structure DGInternalHomModel {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M N : DGModule S A) where
  component : GradedFamily S
  differential : ∀ (n : ℤ) (U : S.Obj),
    component n U → component (n + 1) U
  module_map_property : Prop
  commutator_property : Prop

def internalHom {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} (H : InternalHomModel M N) : GradedFamily S := H.component

def dgInternalHom {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (H : DGInternalHomModel M N) : GradedFamily S := H.component

structure PullbackData {S T : RingedSite.{u,v} R} (A : DGAlgebra T) (B : DGAlgebra S) where
  morphism : RingedSiteMorphism S T
  object_map : DGModule T A → DGModule S B

structure PullPushFunctorData {S T : RingedSite.{u,v} R}
    (A : DGAlgebra S) (B : DGAlgebra T) where
  pull : DGModule T B → DGModule S A
  push : DGModule S A → DGModule T B
  adjunction : Prop

structure ShortExactSequence {S : RingedSite.{u,v} R} {A : DGAlgebra S} where
  K : DGModule S A
  L : DGModule S A
  M : DGModule S A
  injection : DGModuleHom K L
  projection : DGModuleHom L M
  exact : Prop
  graded_split : Prop

structure DerivedFunctorData (A B : Type*) where
  map : A → B
  derived : Prop

structure DeltaFunctorData (A B : Type*) where
  degreeZero : A → B
  connecting : Prop
  exactness : Prop

structure CartesianCondition {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  object : DGModule S A
  condition : ∀ {U V : S.Obj}, SiteHom S U V → Prop

structure InverseDGSystem (R : Type u) [CommRing R] where
  algebra : ℕ → Type v
  transition : ∀ {m n : ℕ}, m ≤ n → algebra n → algebra m

end Sdga
