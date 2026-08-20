import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Torsor.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Deformation Theory, Chapter 2: Deformations of rings

This file formalizes the single numbered source section
books/defos.tex:32-478. The naive cotangent complex is the canonical
presentation-independent interface from Commutative Algebra, Chapter 134.
Square-zero algebra extensions are recorded as explicit exact extension data;
the classification and lifting results are theorem interfaces, as in this
stage of the formalization.
-/

namespace Formalization.Books.Defos.Unit02

open Formalization.Books.Algebra.Unit134
open Formalization.Books.Algebra.Unit131
open Formalization.Books.MoreAlgebra.Unit83

universe u v

noncomputable section

/-! ## Square-zero extensions and the deformation problem -/

/-- A square-zero extension of B by the B-module N over a fixed ring map
f : R → B.

The additive map inclusion identifies N with the kernel, `module_action`
records the prescribed B-module structure on the kernel, and `square_zero`
records its square-zero condition. -/
structure SquareZeroAlgebraExtension {R B N : Type u}
    [CommRing R] [CommRing B] [AddCommGroup N] [Module B N]
    (f : R →+* B) where
  carrier : CommRingCat.{u}
  base : R →+* carrier
  projection : carrier →+* B
  projection_base : projection.comp base = f
  projection_surjective : Function.Surjective projection
  inclusion : N →+ carrier
  inclusion_injective : Function.Injective inclusion
  exact : ∀ x, projection x = 0 ↔ ∃ n, inclusion n = x
  module_action : ∀ (x : carrier) (n : N),
    x * inclusion n = inclusion (projection x • n)
  square_zero : ∀ m n : N, inclusion m * inclusion n = 0

/-- An isomorphism of square-zero extensions preserving base, quotient, and
the named kernel module. -/
structure SquareZeroAlgebraExtension.Iso
    {R B N : Type u} [CommRing R] [CommRing B] [AddCommGroup N] [Module B N]
    {f : R →+* B} (E F : SquareZeroAlgebraExtension (N := N) f) where
  hom : E.carrier ≃+* F.carrier
  base_commutes : hom.toRingHom.comp E.base = F.base
  projection_commutes : F.projection.comp hom.toRingHom = E.projection
  inclusion_commutes : ∀ n, hom (E.inclusion n) = F.inclusion n

namespace SquareZeroAlgebraExtension

variable {R B N : Type u} [CommRing R] [CommRing B]
  [AddCommGroup N] [Module B N] {f : R →+* B}

/-- The identity isomorphism of a square-zero extension. -/
def Iso.refl (E : SquareZeroAlgebraExtension (N := N) f) : Iso E E where
  hom := RingEquiv.refl _
  base_commutes := by simp
  projection_commutes := by simp
  inclusion_commutes := by intro n; rfl

/-- The inverse of an extension isomorphism. -/
def Iso.symm {E F : SquareZeroAlgebraExtension (N := N) f} (e : Iso E F) : Iso F E where
  hom := e.hom.symm
  base_commutes := by
    apply RingHom.ext
    intro r
    change e.hom.symm (F.base r) = E.base r
    rw [← congrArg (fun g => g r) e.base_commutes]
    simp
  projection_commutes := by
    apply RingHom.ext
    intro x
    change E.projection (e.hom.symm x) = F.projection x
    rw [← e.projection_commutes]
    simp
  inclusion_commutes := by
    intro n
    apply e.hom.injective
    simp [e.inclusion_commutes]

/-- Composition of extension isomorphisms. -/
def Iso.trans {E F G : SquareZeroAlgebraExtension (N := N) f}
    (e₁ : Iso E F) (e₂ : Iso F G) : Iso E G where
  hom := e₁.hom.trans e₂.hom
  base_commutes := by
    apply RingHom.ext
    intro r
    change e₂.hom (e₁.hom (E.base r)) = G.base r
    calc
      e₂.hom (e₁.hom (E.base r)) = e₂.hom (F.base r) := by
        congr 1
        exact congrArg (fun h => h r) e₁.base_commutes
      _ = G.base r := by
        exact congrArg (fun h => h r) e₂.base_commutes
  projection_commutes := by
    apply RingHom.ext
    intro x
    change G.projection (e₂.hom (e₁.hom x)) = E.projection x
    calc
      G.projection (e₂.hom (e₁.hom x)) = F.projection (e₁.hom x) := by
        exact congrArg (fun h => h (e₁.hom x)) e₂.projection_commutes
      _ = E.projection x := by
        exact congrArg (fun h => h x) e₁.projection_commutes
  inclusion_commutes := by
    intro n
    simp [e₁.inclusion_commutes, e₂.inclusion_commutes]

end SquareZeroAlgebraExtension

/-- A square-zero extension A' of A by the A-module I. -/
structure SquareZeroRingExtension (A' A I : Type u)
    [CommRing A'] [CommRing A] [AddCommGroup I] [Module A I] where
  quotient : A' →+* A
  quotient_surjective : Function.Surjective quotient
  inclusion : I →+ A'
  inclusion_injective : Function.Injective inclusion
  exact : ∀ x, quotient x = 0 ↔ ∃ i, inclusion i = x
  module_action : ∀ (x : A') (i : I),
    x * inclusion i = inclusion (quotient x • i)
  square_zero : ∀ i j : I, inclusion i * inclusion j = 0

/-- The deformation problem from the source diagram. -/
structure DeformationProblem (A' A B I N : Type u)
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module A N] [Module B N] [Algebra A B]
    [IsScalarTower A B N] where
  base_extension : SquareZeroRingExtension A' A I
  coefficient : I →ₗ[A] N

namespace DeformationProblem

variable {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
  [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
  [Algebra A B] [IsScalarTower A B N]

/-- The ring map A' → A in the deformation problem. -/
abbrev quotient (P : DeformationProblem A' A B I N) : A' →+* A :=
  P.base_extension.quotient

/-- The ring map A → B in the deformation problem. -/
abbrev targetMap (P : DeformationProblem A' A B I N) : A →+* B :=
  algebraMap A B

end DeformationProblem

/-- A solution to the source deformation problem. -/
structure DeformationSolution {A' A B I N : Type u}
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module A N] [Module B N] [Algebra A B]
    [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) where
  extension : SquareZeroAlgebraExtension (N := N)
    ((algebraMap A B).comp P.base_extension.quotient)
  base_kernel : ∀ i,
    extension.base (P.base_extension.inclusion i) = extension.inclusion (P.coefficient i)

/-- The front and back solutions and all vertical maps in the diagram used
for the obstruction lemma. -/
structure DeformationSolutionDiagram
    {A₁' A₂' A₁ A₂ B₁ B₂ I₁ I₂ N₁ N₂ : Type u}
    [CommRing A₁'] [CommRing A₂'] [CommRing A₁] [CommRing A₂]
    [CommRing B₁] [CommRing B₂]
    [AddCommGroup I₁] [Module A₁ I₁]
    [AddCommGroup I₂] [Module A₂ I₂]
    [AddCommGroup N₁] [Module A₁ N₁] [Module B₁ N₁]
    [Algebra A₁ B₁] [IsScalarTower A₁ B₁ N₁]
    [AddCommGroup N₂] [Module A₂ N₂] [Module B₂ N₂]
    [Algebra A₂ B₂] [IsScalarTower A₂ B₂ N₂]
    (P₁ : DeformationProblem A₁' A₁ B₁ I₁ N₁)
    (P₂ : DeformationProblem A₂' A₂ B₂ I₂ N₂) where
  solution₁ : DeformationSolution P₁
  solution₂ : DeformationSolution P₂
  baseMap : A₁' →+* A₂'
  quotientMap : A₁ →+* A₂
  targetMap : B₁ →+* B₂
  idealMap : I₁ →ₛₗ[quotientMap] I₂
  kernelMap : N₁ →ₛₗ[targetMap] N₂
  base_square : quotientMap.comp P₁.base_extension.quotient =
    P₂.base_extension.quotient.comp baseMap
  target_square : targetMap.comp (algebraMap A₁ B₁) =
    (algebraMap A₂ B₂).comp quotientMap
  base_kernel_commutes : ∀ i,
    baseMap (P₁.base_extension.inclusion i) =
      P₂.base_extension.inclusion (idealMap i)
  coefficient_square : ∀ i,
    P₂.coefficient (idealMap i) = kernelMap (P₁.coefficient i)

/-- A map between the two selected solutions in a solution diagram. -/
structure DeformationSolutionMap
    {A₁' A₂' A₁ A₂ B₁ B₂ I₁ I₂ N₁ N₂ : Type u}
    [CommRing A₁'] [CommRing A₂'] [CommRing A₁] [CommRing A₂]
    [CommRing B₁] [CommRing B₂]
    [AddCommGroup I₁] [Module A₁ I₁]
    [AddCommGroup I₂] [Module A₂ I₂]
    [AddCommGroup N₁] [Module A₁ N₁] [Module B₁ N₁]
    [Algebra A₁ B₁] [IsScalarTower A₁ B₁ N₁]
    [AddCommGroup N₂] [Module A₂ N₂] [Module B₂ N₂]
    [Algebra A₂ B₂] [IsScalarTower A₂ B₂ N₂]
    {P₁ : DeformationProblem A₁' A₁ B₁ I₁ N₁}
    {P₂ : DeformationProblem A₂' A₂ B₂ I₂ N₂}
    (D : DeformationSolutionDiagram P₁ P₂) where
  hom : D.solution₁.extension.carrier →+* D.solution₂.extension.carrier
  base_commutes : hom.comp D.solution₁.extension.base =
    D.solution₂.extension.base.comp D.baseMap
  quotient_commutes : D.solution₂.extension.projection.comp hom =
    D.targetMap.comp D.solution₁.extension.projection
  kernel_commutes : ∀ n,
    hom (D.solution₁.extension.inclusion n) =
      D.solution₂.extension.inclusion (D.kernelMap n)

/-! ## The naive Ext groups used by the source -/

/-- Precomposition by the naive cotangent differential on B-linear maps. -/
def naiveCotangentHomMap (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] :
    (CanonicalCotangentSpace A B →ₗ[B] N) →ₗ[B]
      (CanonicalConormal A B →ₗ[B] N) :=
  LinearMap.lcomp B N (NaiveCotangentComplex A B)

/-- The degree-one Ext group of the two-term naive cotangent complex.

Since the degree-zero term is free, this is the source cokernel formula
Hom(Ω,N) → Hom(J/J²,N). -/
abbrev NaiveExtOne (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] : ModuleCat.{u} B :=
  ModuleCat.of B
    ((CanonicalConormal A B →ₗ[B] N) ⧸
      LinearMap.range (naiveCotangentHomMap A B N))

/-- The Ext-one group over the base quotient `A' → A`, with its canonical
algebra structure induced by the quotient map. -/
abbrev DeformationProblem.baseNaiveExtOne
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) : Type u :=
  letI : Algebra A' A := P.base_extension.quotient.toAlgebra
  NaiveExtOne A' A N

/-- The Ext-one group in which the base extension class itself lives. -/
abbrev DeformationProblem.baseExtensionNaiveExtOne
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) : Type u :=
  letI : Algebra A' A := P.base_extension.quotient.toAlgebra
  NaiveExtOne A' A I

/-- The Ext-one group over `A' → B`, using the composite structural map. -/
abbrev DeformationProblem.liftingNaiveExtOne
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) : Type u :=
  letI : Algebra A' B :=
    ((algebraMap A B).comp P.base_extension.quotient).toAlgebra
  NaiveExtOne A' B N

/-- The degree-zero Hom group governing automorphisms of a square-zero
extension. -/
abbrev DerivationHom (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] : ModuleCat.{u} B :=
  ModuleCat.of B
    (ModuleOfDifferentials A B →ₗ[B] N)

/-- The source's principal homogeneous spaces are Mathlib's canonical
`AddTorsor` structures. -/
abbrev PrincipalHomogeneousSpace (G : Type u) (P : Type v) [AddGroup G] :=
  AddTorsor G P

/-! ## Isomorphism classes and classification interfaces -/

/-- The setoid of square-zero algebra extensions under extension isomorphism. -/
def extensionSetoid {R B N : Type u} [CommRing R] [CommRing B]
    [AddCommGroup N] [Module B N] {f : R →+* B} :
    Setoid (SquareZeroAlgebraExtension (N := N) f) where
  r E F := Nonempty (SquareZeroAlgebraExtension.Iso E F)
  iseqv := {
    refl := fun E => ⟨SquareZeroAlgebraExtension.Iso.refl E⟩
    symm := by
      intro E F h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro E F G hEF hFG
      rcases hEF with ⟨e₁⟩
      rcases hFG with ⟨e₂⟩
      exact ⟨e₁.trans e₂⟩ }

/-- Isomorphism classes of square-zero algebra extensions. -/
abbrev ExtensionClass {R B N : Type u} [CommRing R] [CommRing B]
    [AddCommGroup N] [Module B N] {f : R →+* B} :=
  Quotient (extensionSetoid (f := f) (N := N))

/-- The class of a specified square-zero extension. -/
def extensionClassOf {R B N : Type u} [CommRing R] [CommRing B]
    [AddCommGroup N] [Module B N] {f : R →+* B}
    (E : SquareZeroAlgebraExtension (N := N) f) :
      ExtensionClass (N := N) (f := f) :=
  Quotient.mk (extensionSetoid (f := f) (N := N)) E

/-- The setoid of solutions under isomorphisms of the underlying extensions. -/
def solutionSetoid {A' A B I N : Type u}
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module A N] [Module B N] [Algebra A B]
    [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) :
    Setoid (DeformationSolution P) where
  r E F := Nonempty (SquareZeroAlgebraExtension.Iso E.extension F.extension)
  iseqv := {
    refl := fun E => ⟨SquareZeroAlgebraExtension.Iso.refl E.extension⟩
    symm := by
      intro E F h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro E F G hEF hFG
      rcases hEF with ⟨e₁⟩
      rcases hFG with ⟨e₂⟩
      exact ⟨e₁.trans e₂⟩ }

/-- Isomorphism classes of solutions to a deformation problem. -/
abbrev SolutionClass {A' A B I N : Type u}
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module A N] [Module B N] [Algebra A B]
    [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) :=
  Quotient (solutionSetoid P)

/-- The source notion of a compatible map between two square-zero extensions. -/
structure ExtensionMap {R₁ R₂ B₁ B₂ N₁ N₂ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing B₁] [CommRing B₂]
    [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂]
    {f₁ : R₁ →+* B₁} {f₂ : R₂ →+* B₂}
    (E₁ : SquareZeroAlgebraExtension (N := N₁) f₁)
    (E₂ : SquareZeroAlgebraExtension (N := N₂) f₂)
    (baseMap : R₁ →+* R₂) (quotientMap : B₁ →+* B₂)
    (kernelMap : N₁ →+ N₂) where
  hom : E₁.carrier →+* E₂.carrier
  base_commutes : hom.comp E₁.base = E₂.base.comp baseMap
  quotient_commutes : E₂.projection.comp hom = quotientMap.comp E₁.projection
  kernel_commutes : ∀ n, hom (E₁.inclusion n) = E₂.inclusion (kernelMap n)

/-! ## The lemmas of the section -/

/-- The obstruction class for a commutative diagram of solutions. -/
theorem exists_canonical_obstruction
    {A₁' A₂' A₁ A₂ B₁ B₂ I₁ I₂ N₁ N₂ : Type u}
    [CommRing A₁'] [CommRing A₂'] [CommRing A₁] [CommRing A₂]
    [CommRing B₁] [CommRing B₂]
    [AddCommGroup I₁] [Module A₁ I₁]
    [AddCommGroup I₂] [Module A₂ I₂]
    [AddCommGroup N₁] [Module A₁ N₁] [Module B₁ N₁]
    [Algebra A₁ B₁] [IsScalarTower A₁ B₁ N₁]
    [AddCommGroup N₂] [Module A₂ N₂] [Module B₂ N₂]
    [Algebra A₂ B₂] [IsScalarTower A₂ B₂ N₂] [Module B₁ N₂]
    {P₁ : DeformationProblem A₁' A₁ B₁ I₁ N₁}
    {P₂ : DeformationProblem A₂' A₂ B₂ I₂ N₂}
    (D : DeformationSolutionDiagram P₁ P₂) :
    ∃ obstruction : NaiveExtOne A₁ B₁ N₂,
      (obstruction = 0 ↔
        Nonempty (DeformationSolutionMap D)) := by
  sorry

/-- Once a compatible map exists, all compatible maps in the source diagram
form an additive torsor under `Hom_{B₁}(Ω_{B₁/A₁}, N₂)`. -/
theorem compatible_extension_maps_is_addTorsor
    {A₁' A₂' A₁ A₂ B₁ B₂ I₁ I₂ N₁ N₂ : Type u}
    [CommRing A₁'] [CommRing A₂'] [CommRing A₁] [CommRing A₂]
    [CommRing B₁] [CommRing B₂]
    [AddCommGroup I₁] [Module A₁ I₁]
    [AddCommGroup I₂] [Module A₂ I₂]
    [AddCommGroup N₁] [Module A₁ N₁] [Module B₁ N₁]
    [Algebra A₁ B₁] [IsScalarTower A₁ B₁ N₁]
    [AddCommGroup N₂] [Module A₂ N₂] [Module B₂ N₂]
    [Algebra A₂ B₂] [IsScalarTower A₂ B₂ N₂] [Module B₁ N₂]
    {P₁ : DeformationProblem A₁' A₁ B₁ I₁ N₁}
    {P₂ : DeformationProblem A₂' A₂ B₂ I₂ N₂}
    (D : DeformationSolutionDiagram P₁ P₂)
    (h : Nonempty (DeformationSolutionMap D)) :
    Nonempty (PrincipalHomogeneousSpace (DerivationHom A₁ B₁ N₂ : Type u)
      (DeformationSolutionMap D)) := by
  sorry

/-- If one solution exists, solution isomorphism classes form a torsor under
Ext one of the naive cotangent complex. -/
theorem solution_classes_is_addTorsor
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N] (P : DeformationProblem A' A B I N)
    (h : Nonempty (DeformationSolution P)) :
    Nonempty (PrincipalHomogeneousSpace (NaiveExtOne A B N : Type u)
      (SolutionClass P)) := by
  sorry

/-- The classification of square-zero extensions of A-algebras by the first
Ext group of the naive cotangent complex. -/
theorem extension_classes_equiv_naiveExtOne
    {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] :
    Nonempty (ExtensionClass (N := N) (f := algebraMap A B) ≃
      (NaiveExtOne A B N : Type u)) := by
  sorry

/-- The base square-zero extension, viewed as an algebra extension of `A`.

This is the extension `A'` itself, with quotient map `A' → A` and identity
structure map from `A'` to its carrier. -/
def SquareZeroRingExtension.toAlgebraExtension
    {A' A I : Type u} [CommRing A'] [CommRing A]
    [AddCommGroup I] [Module A I]
    (E : SquareZeroRingExtension A' A I) :
    SquareZeroAlgebraExtension (N := I) E.quotient where
  carrier := CommRingCat.of A'
  base := RingHom.id A'
  projection := E.quotient
  projection_base := by simp
  projection_surjective := E.quotient_surjective
  inclusion := E.inclusion
  inclusion_injective := E.inclusion_injective
  exact := E.exact
  module_action := E.module_action
  square_zero := E.square_zero

/-- The split extension `N ⊕ B` appearing in the source proof of the
classification lemma. -/
theorem trivial_extension_exists
    {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] :
    Nonempty (SquareZeroAlgebraExtension (N := N) (algebraMap A B)) := by
  sorry

/-- The Ext-one value attached to an extension through the classification
equivalence.  This is a usable chosen representative of the canonical class
map; the classification theorem above is the invariant statement. -/
noncomputable def extensionClassValue
    {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (E : SquareZeroAlgebraExtension (N := N) (algebraMap A B)) :
    NaiveExtOne A B N :=
  (Classical.choice (extension_classes_equiv_naiveExtOne (A := A) (B := B)
    (N := N))) (extensionClassOf E)

namespace DeformationProblem

/-- The Ext-one class of the given base extension `A'` of `A` by `I`. -/
noncomputable def baseExtensionClass
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N]
    [Module B N] [Algebra A B] [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N) : P.baseExtensionNaiveExtOne :=
  letI : Algebra A' A := P.base_extension.quotient.toAlgebra
  extensionClassValue (P.base_extension.toAlgebraExtension)

end DeformationProblem

/-! ## Presentation formula and functoriality -/

/-- The displayed cokernel formula for the naive Ext group attached to a
presentation P of B over A. -/
theorem presentation_naiveExtOne_formula
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι) :
    Nonempty (
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸
        LinearMap.range
          (LinearMap.lcomp B N P.toExtension.cotangentComplex)) ≃ₗ[B]
        (NaiveExtOne A B N : Type u)) := by
  sorry

/-- The presentation-level cokernel before identifying it with the canonical
naive Ext-one group. -/
abbrev PresentationNaiveExtOne
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι) : ModuleCat.{u} B :=
  ModuleCat.of B
    ((P.toExtension.Cotangent →ₗ[B] N) ⧸
      LinearMap.range
        (LinearMap.lcomp B N P.toExtension.cotangentComplex))

/-- The quotient map which records a presentation lift's extension class. -/
noncomputable def presentationExtensionClass
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι) :
    (P.toExtension.Cotangent →ₗ[B] N) →ₗ[B]
      (PresentationNaiveExtOne (N := N) P : Type u) :=
  Submodule.mkQ _

/-- A chosen lift of a polynomial presentation to an extension. -/
structure PresentationLift
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι) (E : SquareZeroAlgebraExtension (N := N) (algebraMap A B)) where
  map : P.toExtension.Ring →+* E.carrier
  map_base : map.comp (algebraMap A P.toExtension.Ring) = E.base
  map_projection : E.projection.comp map = algebraMap P.toExtension.Ring B

/-- The kernel-valued map obtained by restricting a presentation lift to the
kernel of the presentation.  The square-zero condition makes this descend to
the conormal module; the descent itself is the following theorem interface. -/
noncomputable def PresentationLift.kernelValue
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    {P : Presentation A B ι} {E : SquareZeroAlgebraExtension (N := N) (algebraMap A B)}
    (L : PresentationLift P E) (x : P.toExtension.ker) : N :=
  Classical.choose ((E.exact (L.map x)).mp (by
    have hx : E.projection (L.map x) =
        (algebraMap P.toExtension.Ring B) x :=
      congrArg (fun f => f x) L.map_projection
    rw [hx]
    simpa only [RingHom.mem_ker] using x.property))

theorem PresentationLift.kernelValue_spec
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    {P : Presentation A B ι} {E : SquareZeroAlgebraExtension (N := N) (algebraMap A B)}
    (L : PresentationLift P E) (x : P.toExtension.ker) :
    E.inclusion (L.kernelValue x) = L.map x := by
  exact Classical.choose_spec ((E.exact (L.map x)).mp (by
    have hx : E.projection (L.map x) =
        (algebraMap P.toExtension.Ring B) x :=
      congrArg (fun f => f x) L.map_projection
    rw [hx]
    simpa only [RingHom.mem_ker] using x.property))

/-- The class construction in the source restricts a presentation lift to the
conormal term, modulo maps from the cotangent-space term. -/
theorem extension_class_is_restriction_of_lift
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι)
    (E : SquareZeroAlgebraExtension (N := N) (algebraMap A B))
    (L : PresentationLift P E) :
    ∃ restriction : P.toExtension.Cotangent →ₗ[B] N,
      ∀ x : P.toExtension.ker,
        restriction (Algebra.Extension.Cotangent.mk x) = L.kernelValue x := by
  sorry

/-- The source comparison of extension classes under A → B → C and a map of
kernel modules. -/
structure ExtensionClassComparison
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module C N]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower B C N] [IsScalarTower A B C]
    (c : M →ₗ[B] N) where
  sourceMap : NaiveExtOne A B M →+ NaiveExtOne A B N
  targetMap : NaiveExtOne A C N →+ NaiveExtOne A B N

/-- The functoriality criterion for a map between two square-zero extensions. -/
theorem extension_map_iff_classes_agree
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module C N]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower B C N] [IsScalarTower A B C]
    (c : M →ₗ[B] N)
    (E : SquareZeroAlgebraExtension (N := M) (algebraMap A B))
    (F : SquareZeroAlgebraExtension (N := N) (algebraMap A C)) :
    ∃ comparison : ExtensionClassComparison c,
      Nonempty (ExtensionMap E F (RingHom.id A) (algebraMap B C)
        c.toAddMonoidHom) ↔
        comparison.sourceMap (extensionClassValue E) =
          comparison.targetMap (extensionClassValue F) := by
  sorry

/- The source constructs the two comparison extensions by pushout and
pullback. Their underlying carriers are retained explicitly here. -/

/-- Underlying additive carrier of the pushout (N × B')/M. -/
abbrev pushoutCarrier {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (E : SquareZeroAlgebraExtension (N := M) (algebraMap A B)) (c : M →ₗ[B] N) : Type u :=
  (N × E.carrier) ⧸
    AddSubgroup.closure {x : N × E.carrier |
      ∃ m : M, x = (c m, -E.inclusion m)}

/-- Underlying carrier of the pullback C' ×_C B. -/
def pullbackSubgroup {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C]
    [AddCommGroup N] [Module C N]
    (E : SquareZeroAlgebraExtension (N := N) (algebraMap A C)) (g : B →+* C) :
    AddSubgroup (E.carrier × B) where
  carrier := {x | E.projection x.1 = g x.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change E.projection (x.1 + y.1) = g (x.2 + y.2)
    rw [map_add, map_add, hx, hy]
  neg_mem' := by
    intro x hx
    change E.projection (-x.1) = g (-x.2)
    rw [map_neg, map_neg, hx]

abbrev pullbackCarrier {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C]
    [AddCommGroup N] [Module C N]
    (E : SquareZeroAlgebraExtension (N := N) (algebraMap A C)) (g : B →+* C) : Type u :=
  pullbackSubgroup E g

/-- The pushout carrier carries the square-zero extension structure described
in the source. -/
theorem exists_pushout_extension
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (E : SquareZeroAlgebraExtension (N := M) (algebraMap A B)) (c : M →ₗ[B] N) :
    ∃ F : SquareZeroAlgebraExtension (N := N) (algebraMap A B),
      Nonempty (F.carrier ≃+ pushoutCarrier E c) := by
  sorry

/-- The pullback carrier carries the square-zero extension structure described
in the source. -/
theorem exists_pullback_extension
    {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [AddCommGroup N] [Module B N] [Module C N]
    (E : SquareZeroAlgebraExtension (N := N) (algebraMap A C)) (g : B →+* C) :
    ∃ F : SquareZeroAlgebraExtension (N := N) (algebraMap A B),
      Nonempty (F.carrier ≃+ pullbackCarrier E g) := by
  sorry

/-! ## Parametrization and the final lifting theorem -/

/-- The parametrization of solutions by the fibre of the natural Ext map. -/
theorem solution_classes_equiv_fibre
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N] (P : DeformationProblem A' A B I N) :
    ∃ (map : P.liftingNaiveExtOne →+ P.baseNaiveExtOne)
      (image : P.baseExtensionNaiveExtOne →+ P.baseNaiveExtOne),
      Nonempty (SolutionClass P ≃
        {ζ : P.liftingNaiveExtOne // map ζ = image P.baseExtensionClass}) := by
  sorry

/-! The source remark says that the image of the base extension class would be
the obstruction in Ext degree two if the displayed transitivity maps formed a
distinguished triangle. The current project API has no presentation-level
derived-category triangle for the naive complex, so this counterfactual
warning is recorded here rather than replaced by an unconditional theorem. -/

/-- A local complete-intersection map admits a solution to every square-zero
lifting problem. -/
theorem exists_solution_of_localCompleteIntersection
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module A N] [Module B N]
    [Algebra A B] [IsScalarTower A B N]
    (P : DeformationProblem A' A B I N)
    (h : IsLocalCompleteIntersectionHom (algebraMap A B)) :
    Nonempty (DeformationSolution P) := by
  sorry

end
end Formalization.Books.Defos.Unit02
