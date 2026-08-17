import Formalization.Books.Dga.Unit14.GradedProjectiveModules
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Differential Graded Algebra, Chapter 14: Projective modules and DG algebras

This file formalizes the third source section.  The differential graded
objects are built over the external graded-algebra interface from `Core`.
The shift and homotopy constructions are packaged by small specifications so
that their proposition-level sign and cast verifications can remain deferred
in this statements stage while the exported definitions retain real bodies.
-/

namespace Formalization.Books.Dga.Unit14

open CategoryTheory

universe u v w

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## Degree transport and differential graded algebras -/

/-- Transport a homogeneous element along an equality of degrees. -/
def gradedTransport {M : ℤ → Type w} {i j : ℤ} (h : i = j) (x : M i) : M j :=
  h ▸ x

/-- The corresponding linear transport map. -/
def gradedTransportLinearMap
    {S : Type u} [Semiring S] {M : ℤ → Type w}
    [∀ n, AddCommMonoid (M n)] [∀ n, Module S (M n)]
    {i j : ℤ} (h : i = j) : M i →ₗ[S] M j :=
  h ▸ (LinearMap.id : M i →ₗ[S] M i)

/-- The sign `(-1)^n`, represented in an arbitrary ring. -/
def gradedSign (S : Type u) [Ring S] (n : ℤ) : S :=
  ((n.negOnePow : ℤ) : S)

/-- External differential graded algebra data on the graded algebra `A`. -/
structure DifferentialGradedAlgebraData
    (R : Type u) (A : ℤ → Type v)
    [CommRing R]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A] where
  differential : ∀ n : ℤ, A n →ₗ[R] A (n + 1)
  differential_square : ∀ (n : ℤ) (a : A n),
    differential (n + 1) (differential n a) = 0
  differential_leibniz : ∀ {i j : ℤ} (a : A i) (b : A j),
    differential (i + j) (GradedMonoid.GMul.mul a b) =
      gradedTransport
          (show (i + 1) + j = (i + j) + 1 by
            calc
              (i + 1) + j = i + (1 + j) := add_assoc i 1 j
              _ = i + (j + 1) := by rw [add_comm 1 j]
              _ = (i + j) + 1 := (add_assoc i j 1).symm)
        (GradedMonoid.GMul.mul (differential i a) b) +
      gradedSign R i •
        gradedTransport
          (show i + (j + 1) = (i + j) + 1 by
            exact (add_assoc i j 1).symm)
          (GradedMonoid.GMul.mul a (differential j b))

/-! ## Differential graded modules and maps -/

/-- The Leibniz law for a differential graded right module. -/
def DifferentialGradedModuleLeibniz
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (M : GradedRightModule.{u, v, w} (R := R) (A := A))
    (d : ∀ n : ℤ, M.component n →ₗ[R] M.component (n + 1)) : Prop :=
  ∀ {i j : ℤ} (m : M.component i) (a : A j),
    d (i + j) (M.action m a) =
      gradedTransport
          (show (i + 1) + j = (i + j) + 1 by
            calc
              (i + 1) + j = i + (1 + j) := add_assoc i 1 j
              _ = i + (j + 1) := by rw [add_comm 1 j]
              _ = (i + j) + 1 := (add_assoc i j 1).symm)
        (M.action (d i m) a) +
      gradedSign R i •
        gradedTransport
          (show i + (j + 1) = (i + j) + 1 by
            exact (add_assoc i j 1).symm)
          (M.action m (D.differential j a))

/-- A differential graded right module over `D`. -/
structure DifferentialGradedModuleData
    {R : Type u} {A : ℤ → Type v}
    [CommRing R]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
    (D : DifferentialGradedAlgebraData R A) where
  graded : GradedRightModule.{u, v, w} (R := R) (A := A)
  differential : ∀ n : ℤ,
    graded.component n →ₗ[R] graded.component (n + 1)
  differential_square : ∀ (n : ℤ) (m : graded.component n),
    differential (n + 1) (differential n m) = 0
  differential_leibniz :
    DifferentialGradedModuleLeibniz D graded differential

/-- A degree-zero homomorphism of differential graded modules. -/
structure DifferentialGradedModuleHom
    {R : Type u} {A : ℤ → Type v}
    [CommRing R]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
    {D : DifferentialGradedAlgebraData R A}
    (M N : DifferentialGradedModuleData D) where
  underlying : GradedRightModuleHom.{u, v, w} M.graded N.graded
  commutes_with_differential : ∀ (n : ℤ) (m : M.graded.component n),
    N.differential n (underlying.app n m) =
      underlying.app (n + 1) (M.differential n m)

namespace DifferentialGradedModuleHom

/-- The identity map of differential graded modules. -/
def id
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) :
    DifferentialGradedModuleHom M M where
  underlying := GradedRightModuleHom.id M.graded
  commutes_with_differential := by
    intro n m
    rfl

/-- Composition of degree-zero differential graded module maps. -/
def comp
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N P : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N)
    (g : DifferentialGradedModuleHom N P) :
    DifferentialGradedModuleHom M P where
  underlying := GradedRightModuleHom.comp f.underlying g.underlying
  commutes_with_differential := by
    intro n m
    change P.differential n (g.underlying.app n (f.underlying.app n m)) =
      g.underlying.app (n + 1)
        (f.underlying.app (n + 1) (M.differential n m))
    rw [g.commutes_with_differential, f.commutes_with_differential]

@[ext]
theorem ext
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    {f g : DifferentialGradedModuleHom M N}
    (h : f.underlying = g.underlying) : f = g := by
  cases f
  cases g
  cases h
  rfl

end DifferentialGradedModuleHom

instance differentialGradedModuleCategory
    {D : DifferentialGradedAlgebraData (R := R) (A := A)} :
    Category (DifferentialGradedModuleData D) where
  Hom M N := DifferentialGradedModuleHom M N
  id := DifferentialGradedModuleHom.id
  comp f g := DifferentialGradedModuleHom.comp f g
  id_comp f := by
    apply DifferentialGradedModuleHom.ext
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro m
    rfl
  comp_id f := by
    apply DifferentialGradedModuleHom.ext
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro m
    rfl
  assoc f g h := by
    apply DifferentialGradedModuleHom.ext
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro m
    rfl

/-- The category of differential graded right modules over `D`. -/
abbrev DifferentialGradedModuleCategory
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :=
  DifferentialGradedModuleData D

/-- The source's phrase “projective as a graded `A`-module”. -/
abbrev IsGradedProjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) : Prop :=
  GradedProjective P.graded

/-- Degreewise surjectivity of a homomorphism of differential graded modules. -/
def DifferentialGradedModuleHom.DegreewiseSurjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.underlying.app n)

/-- An admissible epimorphism is a degreewise surjective DG map whose
underlying graded map splits. -/
def IsAdmissibleEpimorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M P : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M P) : Prop :=
  DifferentialGradedModuleHom.DegreewiseSurjective f ∧
    ∃ s : GradedRightModuleHom.{u, v, w} (R := R) (A := A) P.graded M.graded,
      GradedRightModuleHom.comp f.underlying s = GradedRightModuleHom.id M.graded

/-! ## The graded-projective target lemma -/

/-- A surjective DG map onto a graded-projective target is admissible. -/
theorem target_graded_projective_admissible
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M P : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M P)
    (hf : DifferentialGradedModuleHom.DegreewiseSurjective f)
    (hP : IsGradedProjective P) :
    IsAdmissibleEpimorphism f := by
  sorry

/-! ## Shifts and Hom computations -/

/-- A specification for the differential graded shift of the regular module. -/
structure DifferentialGradedAlgebraShiftSpec
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) where
  object : DifferentialGradedModuleData D
  component_eq : ∀ n : ℤ, object.graded.component n = A (n + k)
  action_eq : ∀ {i j : ℤ} (m : A (i + k)) (a : A j),
    HEq
      (object.graded.action (cast (component_eq i).symm m) a)
      (GradedMonoid.GMul.mul m a)
  differential_eq : ∀ (n : ℤ) (m : A (n + k)),
    HEq
      (object.differential n (cast (component_eq n).symm m))
      (gradedSign R k • D.differential (n + k) m)

theorem differentialGradedAlgebraShiftSpec_nonempty
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    Nonempty (DifferentialGradedAlgebraShiftSpec (R := R) (A := A) D k) := by
  sorry

/-- The shifted regular differential graded module `A[k]`. -/
noncomputable def differentialGradedAlgebraShift
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    DifferentialGradedModuleData D :=
  (Classical.choice
      (differentialGradedAlgebraShiftSpec_nonempty (R := R) (A := A) D k)).object

/-- The cycle submodule in degree `n`. -/
abbrev dgCycles
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) (n : ℤ) :=
  LinearMap.ker (M.differential n)

/-- The previous differential, transported into degree `n`. -/
def dgDifferentialTo
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) (n : ℤ) :
    M.graded.component (n - 1) →ₗ[R] M.graded.component n :=
  (gradedTransportLinearMap (sub_add_cancel n 1)).comp (M.differential (n - 1))

/-- The previous differential lands in cycles. -/
theorem dgDifferentialTo_is_cycle
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) (n : ℤ)
    (m : M.graded.component (n - 1)) :
    (dgDifferentialTo M n m : M.graded.component n) ∈ dgCycles M n := by
  sorry

/-- The boundary submodule in the cycle module. -/
def dgBoundary
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) (n : ℤ) :
    Submodule R (dgCycles M n) :=
  LinearMap.range
    ((dgDifferentialTo M n).codRestrict (dgCycles M n)
      (dgDifferentialTo_is_cycle M n))

/-- Cohomology of a differential graded module in degree `n`. -/
abbrev dgCohomology
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) (n : ℤ) :=
  dgCycles M n ⧸ dgBoundary M n

/-- The Hom from a shifted regular DG module is the cycle module in the
corresponding degree. -/
theorem dg_hom_from_shift_evaluation_equiv
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (M : DifferentialGradedModuleData D) (k : ℤ) :
    Nonempty
      (DifferentialGradedModuleHom
          (differentialGradedAlgebraShift D k) M ≃ dgCycles M (-k)) := by
  sorry

/-! ## The homotopy-category Hom computation -/

/-- A degree `-1` graded homotopy family. -/
structure GradedRightModuleHomotopy
    (M N : GradedRightModule.{u, v, w} (R := R) (A := A)) where
  app : ∀ n : ℤ, M.component n →ₗ[R] N.component (n - 1)
  map_action : ∀ {i j : ℤ} (m : M.component i) (a : A j),
    HEq (app (i + j) (M.action m a))
      (N.action (app i m) a)

/-- Chain homotopy of DG module maps. -/
def DifferentialGradedModuleHomotopic
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f g : DifferentialGradedModuleHom M N) : Prop :=
  ∃ h : GradedRightModuleHomotopy M.graded N.graded,
    ∀ (n : ℤ) (m : M.graded.component n),
      HEq
        (f.underlying.app n m - g.underlying.app n m)
        (gradedTransport
            (sub_add_cancel n 1)
            (N.differential (n - 1) (h.app n m)) +
          gradedTransport
            (show (n + 1) - 1 = n by
              calc
                (n + 1) - 1 = n + (1 - 1) := by rw [add_sub_assoc]
                _ = n := by simp)
            (h.app (n + 1) (M.differential n m)))

theorem dgHomotopy_equivalence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DifferentialGradedModuleData D) :
    _root_.Equivalence (fun f g : DifferentialGradedModuleHom M N =>
      DifferentialGradedModuleHomotopic f g) := by
  sorry

noncomputable def dgHomotopySetoid
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DifferentialGradedModuleData D) :
    Setoid (DifferentialGradedModuleHom M N) :=
  { r := fun f g => DifferentialGradedModuleHomotopic f g
    iseqv := dgHomotopy_equivalence M N }

/-- The Hom type in the homotopy category of differential graded modules. -/
abbrev dgHomotopyCategoryHom
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DifferentialGradedModuleData D) :=
  Quotient (dgHomotopySetoid M N)

/-- The homotopy-category Hom from `A[k]` is `H^(-k)(M)`. -/
theorem dg_homotopy_hom_from_shift_evaluation_equiv
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (M : DifferentialGradedModuleData D) (k : ℤ) :
    Nonempty
      (dgHomotopyCategoryHom (differentialGradedAlgebraShift D k) M ≃
        dgCohomology M (-k)) := by
  sorry

end Formalization.Books.Dga.Unit14
