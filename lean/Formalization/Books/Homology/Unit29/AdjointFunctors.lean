import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Categories.Unit24.AdjointFunctors
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.RingHom.Flat

/-!
# Homological Algebra, Chapter 29: Injectives and adjoint functors

This file records the source's adjoint criteria for injectives, the change of
rings example, transfer of enough and functorial injective embeddings, and the
criterion for constructing a left adjoint from a quotient-generating family.
Mathlib's canonical injective, exactness, adjunction, module-category, and
representability interfaces are used throughout.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit27
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace Formalization.Books.Homology.Unit29

/-! ## Injectives and adjoint functors -/

/- The source's conditions (a), (b), and (c) are respectively Mathlib's
   preservation of monomorphisms, exactness from Categories Chapter 23, and
   preservation of injective objects.  The existing
   `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
   and `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`
   are the direct proof interfaces for the two adjoint implications. -/
theorem adjoint_preserve_injectives
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) :
    (PreservesMonomorphisms v ↔ IsExact v) ∧
      (IsExact v → Functor.PreservesInjectiveObjects u) ∧
      (EnoughInjectives A →
        List.TFAE [PreservesMonomorphisms v, IsExact v,
          Functor.PreservesInjectiveObjects u]) := by
  have hCol : PreservesFiniteColimits v := by
    constructor
    intro J _ _
    exact hAdj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hMonoOfExact : IsExact v → PreservesMonomorphisms v := by
    intro h
    exact @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ v
      (h.1.preservesFiniteLimits WalkingCospan)
  have hExactOfMono : PreservesMonomorphisms v → IsExact v := by
    intro h
    refine ⟨?_, hCol⟩
    apply (Functor.preservesFiniteLimits_tfae v).out 0 3 |>.1
    intro S hS
    have hMap : ∀ (S : ShortComplex B), S.ShortExact →
        (S.map v).Exact ∧ Epi (v.map S.g) :=
      ((Functor.preservesFiniteColimits_tfae v).out 3 0).1 hCol
    have hS' := hMap S hS
    have hMonoS : Mono S.f := hS.mono_f
    exact ⟨hS'.1,
      @PreservesMonomorphisms.preserves B _ A _ v h _ _ S.f hMonoS⟩
  have hExactInjective : IsExact v → Functor.PreservesInjectiveObjects u := by
    intro h
    refine ⟨?_⟩
    intro I hI
    exact @Adjunction.map_injective B _ A _ v u hAdj (hMonoOfExact h) I hI
  refine ⟨⟨hExactOfMono, hMonoOfExact⟩, hExactInjective, ?_⟩
  intro hEnough
  have hEnough' : EnoughInjectives A := hEnough
  apply List.tfae_of_forall (IsExact v)
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact ⟨hExactOfMono, hMonoOfExact⟩
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact Iff.rfl
  have hp := List.mem_singleton.mp hp
  subst p
  constructor
  · exact fun h =>
      hExactOfMono
        (@Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
          B _ A _ hEnough' v u hAdj h)
  · exact hExactInjective

/-! ### Change of rings -/

/- For a map of commutative rings, the source's restriction-of-scalars functor
   is the right adjoint of extension of scalars.  The exactness assertions are
   stated using the chapter's `IsExact` and `IsRightExact` interfaces. -/
theorem change_of_rings_adjunction
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Nonempty (ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f) ∧
      IsExact (ModuleCat.restrictScalars f) ∧
        IsRightExact (ModuleCat.extendScalars f) := by
  sorry

/- The source's final change-of-rings conclusion is the canonical flatness
   criterion for the restriction functor on module categories. -/
theorem change_of_rings_preserves_injectives_iff_flat
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Functor.PreservesInjectiveObjects (ModuleCat.restrictScalars f) ↔
      RingHom.Flat f := by
  sorry

/- The source's example is stated with an explicit primality hypothesis, since
   `ZMod p` is the field occurring in the example only for prime `p`. -/
theorem zmod_prime_change_of_rings_counterexample
    (p : ℕ) (hp : Nat.Prime p) :
    Injective (ModuleCat.of (ZMod p) (ZMod p)) ∧
      ¬ Injective
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
          (ModuleCat.of (ZMod p) (ZMod p))) ∧
      ¬ Functor.PreservesInjectiveObjects
        (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))) := by
  sorry

/-! ### Enough injectives and faithfulness -/

theorem adjoint_enough_injectives
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v)
    (hEnough : EnoughInjectives A)
    (hReflectsZero : ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀) :
    EnoughInjectives B := by
  sorry

/- In the presence of the adjunction and preservation of monomorphisms, the
   source's objectwise condition (4) is exactly faithfulness of `v`. -/
theorem adjoint_faithful_iff_reflects_zero
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v) :
    Functor.Faithful v ↔
      ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀ := by
  sorry

/- The zero-functor example from the source makes the need for the objectwise
   zero-reflection hypothesis explicit.  The two constant functors at the
   zero objects are the canonical zero functors in an abelian category. -/
theorem zero_functors_counterexample
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (hB : ∃ X : B, ¬ IsZero X) :
    let u₀ : A ⥤ B := (Functor.const A).obj (0 : B)
    let v₀ : B ⥤ A := (Functor.const B).obj (0 : A)
    Nonempty (v₀ ⊣ u₀) ∧
      PreservesMonomorphisms v₀ ∧
        IsExact v₀ ∧
          ¬ Functor.Faithful v₀ ∧
            ¬ (∀ X : B, IsZero (v₀.obj X) → IsZero X) := by
  sorry

/-! ### Functorial injective embeddings -/

theorem adjoint_functorial_injective_embeddings
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hAdj : v ⊣ u) (hMono : PreservesMonomorphisms v)
    (hEnough : EnoughInjectives A)
    (hReflectsZero : ∀ B₀ : B, IsZero (v.obj B₀) → IsZero B₀)
    (hFunctorial : HasFunctorialInjectiveEmbeddings (C := A)) :
    HasFunctorialInjectiveEmbeddings (C := B) := by
  sorry

/-! ### A partially defined left adjoint -/

/- `CorepresentableBy` is the precise functorial form of the source's
   equality
   `Hom_A(Q, A) = Hom_B(P, u(A))`.  Its `homEquiv (𝟙 Q)` is the source's
   universal map `P → u(Q)`, and `CorepresentableBy.homEquiv_eq` supplies the
   displayed characterization of all represented morphisms.  The remaining
   maps on the quotient-generating family and the exact sequence
   `P₂ → P₁ → B → 0` are construction details of the standard proof, so no
   parallel functor or presentation API is introduced here. -/
theorem left_adjoint_of_quotient_generators
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (u : A ⥤ B) (Pset : Set B)
    (hQuotient : ∀ B₀ : B,
      ∃ P : B, P ∈ Pset ∧ ∃ f : P ⟶ B₀, Epi f)
    (hRepresentable : ∀ P : B, P ∈ Pset →
      ∃ Q : A,
        Nonempty ((u ⋙ coyoneda.obj (Opposite.op P)).CorepresentableBy Q)) :
    ∃ v : B ⥤ A, Nonempty (v ⊣ u) := by
  sorry

end Formalization.Books.Homology.Unit29
