import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.MoreAlgebra.Unit83.PseudoCoherentPerfectRingMaps
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Torsor
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

universe u

noncomputable section

/-! ## Square-zero extensions and the deformation problem -/

/-- A square-zero extension of B by the B-module N over a fixed ring map
f : R → B.

The additive map inclusion identifies N with the kernel, ideal records that
the kernel is an ideal, and square_zero records its square-zero condition. -/
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
  ideal : ∀ (x : carrier) (n : N), ∃ m : N, x * inclusion n = inclusion m
  square_zero : ∀ m n : N, inclusion m * inclusion n = 0

/-- An isomorphism of square-zero extensions preserving base, quotient, and
the named kernel module. -/
structure SquareZeroAlgebraExtension.Iso
    {R B N : Type u} [CommRing R] [CommRing B] [AddCommGroup N] [Module B N]
    {f : R →+* B} (E F : SquareZeroAlgebraExtension f N) where
  hom : E.carrier ≃+* F.carrier
  base_commutes : hom.toRingHom.comp E.base = F.base
  projection_commutes : F.projection.comp hom.toRingHom = E.projection
  inclusion_commutes : ∀ n, hom (E.inclusion n) = F.inclusion n

namespace SquareZeroAlgebraExtension

variable {R B N : Type u} [CommRing R] [CommRing B]
  [AddCommGroup N] [Module B N] {f : R →+* B}

/-- The identity isomorphism of a square-zero extension. -/
def Iso.refl (E : SquareZeroAlgebraExtension f N) : Iso E E where
  hom := RingEquiv.refl _
  base_commutes := by simp
  projection_commutes := by simp
  inclusion_commutes := by intro n; rfl

/-- The inverse of an extension isomorphism. -/
def Iso.symm {E F : SquareZeroAlgebraExtension f N} (e : Iso E F) : Iso F E where
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
def Iso.trans {E F G : SquareZeroAlgebraExtension f N}
    (e₁ : Iso E F) (e₂ : Iso F G) : Iso E G where
  hom := e₁.hom.trans e₂.hom
  base_commutes := by
    apply RingHom.ext
    intro r
    change e₂.hom (e₁.hom (E.base r)) = G.base r
    rw [e₁.base_commutes, e₂.base_commutes]
  projection_commutes := by
    apply RingHom.ext
    intro x
    change G.projection (e₂.hom (e₁.hom x)) = E.projection x
    rw [← e₂.projection_commutes, ← e₁.projection_commutes]
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
  ideal : ∀ (x : A') (i : I), ∃ j : I, x * inclusion i = inclusion j
  square_zero : ∀ i j : I, inclusion i * inclusion j = 0

/-- The deformation problem from the source diagram. -/
structure DeformationProblem (A' A B I N : Type u)
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module B N] [Algebra A B] where
  base_extension : SquareZeroRingExtension A' A I
  coefficient : I →ₗ[A] N

namespace DeformationProblem

variable {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
  [AddCommGroup I] [Module A I] [AddCommGroup N] [Module B N]
  [Algebra A B]

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
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : DeformationProblem A' A B I N) where
  extension : SquareZeroAlgebraExtension
    ((algebraMap A B).comp P.base_extension.quotient) N
  map_from_base : A' →+* extension.carrier
  map_from_base_projection : extension.projection.comp map_from_base =
    (algebraMap A B).comp P.base_extension.quotient
  map_from_base_kernel : ∀ i,
    map_from_base (P.base_extension.inclusion i) = extension.inclusion (P.coefficient i)

/-! ## The naive Ext groups used by the source -/

/-- Precomposition by the naive cotangent differential on B-linear maps. -/
def naiveCotangentHomMap (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] :
    (CanonicalCotangentSpace A B →ₗ[B] N) →ₗ[B]
      (CanonicalConormal A B →ₗ[B] N) :=
  LinearMap.llcomp B (CanonicalConormal A B) (CanonicalCotangentSpace A B) N
    (NaiveCotangentComplex A B)

/-- The degree-one Ext group of the two-term naive cotangent complex.

Since the degree-zero term is free, this is the source cokernel formula
Hom(Ω,N) → Hom(J/J²,N). -/
abbrev NaiveExtOne (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] : ModuleCat.{u} B :=
  ModuleCat.of B
    ((CanonicalConormal A B →ₗ[B] N) ⧸
      LinearMap.range (naiveCotangentHomMap A B N))

/-- The degree-zero Hom group governing automorphisms of a square-zero
extension. -/
abbrev DerivationHom (A B N : Type u) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] : ModuleCat.{u} B :=
  ModuleCat.of B
    (ModuleOfDifferentials A B →ₗ[B] N)

/-- A principal homogeneous space, packaged with the operations needed by
Mathlib's canonical AddTorsor class. -/
structure PrincipalHomogeneousSpace (G P : Type u) [AddGroup G] where
  addAction : AddAction G P
  vsub : VSub G P
  torsor : @AddTorsor G P inferInstance addAction vsub

/-! ## Isomorphism classes and classification interfaces -/

/-- The setoid of square-zero algebra extensions under extension isomorphism. -/
def extensionSetoid {R B N : Type u} [CommRing R] [CommRing B]
    [AddCommGroup N] [Module B N] {f : R →+* B} :
    Setoid (SquareZeroAlgebraExtension f N) where
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

/-- The setoid of solutions under isomorphisms of the underlying extensions. -/
def solutionSetoid {A' A B I N : Type u}
    [CommRing A'] [CommRing A] [CommRing B] [AddCommGroup I] [Module A I]
    [AddCommGroup N] [Module B N] [Algebra A B]
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
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : DeformationProblem A' A B I N) :=
  Quotient (solutionSetoid P)

/-- The source notion of a compatible map between two square-zero extensions. -/
structure ExtensionMap {R₁ R₂ B₁ B₂ N₁ N₂ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing B₁] [CommRing B₂]
    [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂]
    {f₁ : R₁ →+* B₁} {f₂ : R₂ →+* B₂}
    (E₁ : SquareZeroAlgebraExtension f₁ N₁)
    (E₂ : SquareZeroAlgebraExtension f₂ N₂)
    (baseMap : R₁ →+* R₂) (quotientMap : B₁ →+* B₂)
    (kernelMap : N₁ →+ N₂) where
  hom : E₁.carrier →+* E₂.carrier
  base_commutes : hom.comp E₁.base = E₂.base.comp baseMap
  quotient_commutes : E₂.projection.comp hom = quotientMap.comp E₁.projection
  kernel_commutes : ∀ n, hom (E₁.inclusion n) = E₂.inclusion (kernelMap n)

/-! ## The lemmas of the section -/

/-- The obstruction class for a commutative diagram of solutions. -/
theorem exists_canonical_obstruction
    {R₁ R₂ A₁ A₂ B₁ B₂ N₁ N₂ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [CommRing B₁] [CommRing B₂]
    [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂]
    [Module B₁ N₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    {f₁ : A₁ →+* B₁} {f₂ : A₂ →+* B₂}
    (E₁ : SquareZeroAlgebraExtension f₁ N₁)
    (E₂ : SquareZeroAlgebraExtension f₂ N₂)
    (baseMap : R₁ →+* R₂) (quotientMap : B₁ →+* B₂)
    (kernelMap : N₁ →+ N₂)
    (hbase : ∃ hom : E₁.carrier →+* E₂.carrier,
      hom.comp E₁.base = E₂.base.comp baseMap)
    (hom : E₁.carrier →+* E₂.carrier)
    (hquotient : E₂.projection.comp hom = quotientMap.comp E₁.projection) :
    ∃ obstruction : NaiveExtOne A₁ B₁ N₂,
      (obstruction = 0 ↔
        Nonempty (ExtensionMap E₁ E₂ baseMap quotientMap kernelMap)) := by
  sorry

/-- Once a compatible map exists, all compatible maps form an additive torsor
under Hom_B(Ω_{B/A},N). -/
theorem compatible_extension_maps_is_addTorsor
    {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (E₁ E₂ : SquareZeroAlgebraExtension (algebraMap A B) N)
    [AddAction (DerivationHom A B N : Type u)
      (ExtensionMap E₁ E₂ (RingHom.id A) (RingHom.id B) (AddMonoidHom.id N))]
    [VSub (DerivationHom A B N : Type u)
      (ExtensionMap E₁ E₂ (RingHom.id A) (RingHom.id B) (AddMonoidHom.id N))]
    (h : Nonempty (ExtensionMap E₁ E₂ (RingHom.id A) (RingHom.id B) (AddMonoidHom.id N))) :
    Nonempty (AddTorsor (DerivationHom A B N : Type u)
      (ExtensionMap E₁ E₂ (RingHom.id A) (RingHom.id B) (AddMonoidHom.id N))) := by
  sorry

/-- If one solution exists, solution isomorphism classes form a torsor under
Ext one of the naive cotangent complex. -/
theorem solution_classes_is_addTorsor
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module B N]
    [Algebra A B] (P : DeformationProblem A' A B I N)
    (h : Nonempty (DeformationSolution P)) :
    Nonempty (AddTorsor (NaiveExtOne A B N : Type u) (SolutionClass P)) := by
  sorry

/-- The classification of square-zero extensions of A-algebras by the first
Ext group of the naive cotangent complex. -/
theorem extension_classes_equiv_naiveExtOne
    {A B N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B] :
    Nonempty (ExtensionClass (f := algebraMap A B) N ≃+
      (NaiveExtOne A B N : Type u)) := by
  sorry

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
          (LinearMap.llcomp B P.toExtension.Cotangent
            P.toExtension.CotangentSpace N P.toExtension.cotangentComplex)) ≃+
        (NaiveExtOne A B N : Type u)) := by
  sorry

/-- A chosen lift of a polynomial presentation to an extension. -/
structure PresentationLift
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι) (E : SquareZeroAlgebraExtension (algebraMap A B) N) where
  map : P.toExtension.Ring →+* E.carrier
  map_base : map.comp (algebraMap A P.toExtension.Ring) = E.base

/-- The class construction in the source restricts a presentation lift to the
conormal term, modulo maps from the cotangent-space term. -/
theorem extension_class_is_restriction_of_lift
    {A B N ι : Type u} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] [Algebra A B]
    (P : Presentation A B ι)
    (E : SquareZeroAlgebraExtension (algebraMap A B) N)
    (L : PresentationLift P E) :
    ∃ restriction : P.toExtension.Cotangent →ₗ[B] N,
      (restriction = 0 ↔ restriction ∈ LinearMap.range
        (LinearMap.llcomp B P.toExtension.Cotangent
          P.toExtension.CotangentSpace N P.toExtension.cotangentComplex)) := by
  sorry

/-- The source comparison of extension classes under A → B → C and a map of
kernel modules. -/
structure ExtensionClassComparison
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module C N]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : M →+ N) where
  map : NaiveExtOne A B M →+ NaiveExtOne A C N

/-- The functoriality criterion for a map between two square-zero extensions. -/
theorem extension_map_iff_classes_agree
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module C N]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : M →+ N)
    (comparison : ExtensionClassComparison c)
    (E : SquareZeroAlgebraExtension (algebraMap A B) M)
    (F : SquareZeroAlgebraExtension (algebraMap A C) N)
    (ξ : NaiveExtOne A B M) (ζ : NaiveExtOne A C N) :
    Nonempty (ExtensionMap E F (algebraMap A B) (algebraMap B C) c) ↔
      comparison.map ξ = ζ := by
  sorry

/- The source constructs the two comparison extensions by pushout and
pullback. Their underlying carriers are retained explicitly here. -/

/-- Underlying additive carrier of the pushout (N × B')/M. -/
def pushoutCarrier {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (E : SquareZeroAlgebraExtension (algebraMap A B) M) (c : M →+ N) : Type u :=
  (N × E.carrier) ⧸
    Submodule.span ℤ {x : N × E.carrier |
      ∃ m : M, x = (c m, -E.inclusion m)}

/-- Underlying carrier of the pullback C' ×_C B. -/
def pullbackCarrier {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup N] [Module C N]
    (E : SquareZeroAlgebraExtension (algebraMap A C) N) (g : B →+* C) : Type u :=
  {x : E.carrier × B // E.projection x.1 = g x.2}

/-- The pushout carrier carries the square-zero extension structure described
in the source. -/
theorem exists_pushout_extension
    {A B M N : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (E : SquareZeroAlgebraExtension (algebraMap A B) M) (c : M →+ N) :
    ∃ F : SquareZeroAlgebraExtension (algebraMap A B) N,
      Nonempty (F.carrier ≃+ pushoutCarrier E c) := by
  sorry

/-- The pullback carrier carries the square-zero extension structure described
in the source. -/
theorem exists_pullback_extension
    {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup N] [Module C N]
    (E : SquareZeroAlgebraExtension (algebraMap A C) N) (g : B →+* C) :
    ∃ F : SquareZeroAlgebraExtension (algebraMap A B) N,
      Nonempty (F.carrier ≃+ pullbackCarrier E g) := by
  sorry

/-! ## Parametrization and the final lifting theorem -/

/-- The parametrization of solutions by the fibre of the natural Ext map. -/
theorem solution_classes_equiv_fibre
    {A' A B I N : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module B N]
    [Algebra A B] (P : DeformationProblem A' A B I N)
    (map : NaiveExtOne A' B N →+ NaiveExtOne A B N)
    (ξ : NaiveExtOne A B N) :
    Nonempty (SolutionClass P ≃
      {ζ : NaiveExtOne A' B N // map ζ = ξ}) := by
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
    [AddCommGroup I] [Module A I] [AddCommGroup N] [Module B N]
    [Algebra A B]
    (P : DeformationProblem A' A B I N)
    (h : IsLocalCompleteIntersectionHom (algebraMap A B)) :
    Nonempty (DeformationSolution P) := by
  sorry

end Formalization.Books.Defos.Unit02
