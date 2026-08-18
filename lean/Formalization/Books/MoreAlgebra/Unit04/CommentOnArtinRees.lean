import Mathlib.Algebra.Module.GradedModule
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic

/-!
# More on Algebra, Chapter 4: A comment on the Artin-Rees property

The source's powers of an ideal acting on a module are written with
`I ^ n • ⊤`, and cokernels are represented by Mathlib's canonical submodule
quotients.  The associated graded construction uses the external `DirectSum`
graded-ring and graded-module interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit04

open DirectSum
open scoped DirectSum TensorProduct

universe u v

noncomputable section

/-! ## Artin-Rees bounds and approximate complexes -/

/-- `c` works for `f` in the Artin-Rees lemma for the ideal `I`.

The source writes `f(M) ∩ I^n N ⊆ f(I^(n-c) M)`.  The canonical Mathlib
forms of these two submodules are `LinearMap.range`/`inf` and
`Submodule.map`/`smul`.
-/
def ArtinReesWorks
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (c : ℕ) : Prop :=
  ∀ n ≥ c,
    LinearMap.range f ⊓ I ^ n • (⊤ : Submodule R N) ≤
      Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M))

/-- Every map between finite modules over a Noetherian ring has a working
Artin-Rees exponent. -/
theorem exists_artinReesWorks
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ArtinReesWorks I f c := by
  sorry

/-- Equality modulo a submodule, expressed by equality after the canonical
quotient map. -/
def LinearMap.CongruentModulo
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (P : Submodule R N) (f g : M →ₗ[R] N) : Prop :=
  P.mkQ.comp f = P.mkQ.comp g

/-- The preimage estimate proved while correcting an approximate complex. -/
theorem approximate_complex_preimage
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    ∀ n ≥ c,
      Submodule.comap g' (I ^ n • (⊤ : Submodule A N)) ≤
        LinearMap.range f' ⊔ I ^ (n - c) • (⊤ : Submodule A M) := by
  sorry

/-- The approximate-complex lemma.  The source's assertion that `S` is a
complex is implied by its stronger exactness hypothesis; the complex
condition for `S'` is retained explicitly.  Its displayed kernel/intersection
calculation is represented by the stronger preimage estimate above together
with the canonical `Function.Exact` conclusion. -/
theorem approximate_complex
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g) (hS' : g'.comp f' = 0)
    (hI : I ≤ Ring.jacobson A)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    ArtinReesWorks I g' c ∧ Function.Exact f' g' := by
  sorry

/-! ## Associated graded modules -/

/-- A subquotient of a submodule, written with the subtype as its carrier. -/
abbrev submoduleQuotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) : Type _ :=
  HasQuotient.Quotient (P : Type _) (Q.comap P.subtype)

/-- The degree-`n` component `I^n/I^(n+1)` of the associated graded ring.
The denominator is pulled back to the subtype `I^n` so that the quotient is
literally the source's degreewise quotient. -/
abbrev associatedGradedRingPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Type u :=
  submoduleQuotient (I ^ n : Submodule R R) (I ^ (n + 1) : Submodule R R)

/-- The degree-`n` component `I^n M/I^(n+1) M` of the associated graded
module. -/
abbrev associatedGradedModulePiece
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) : Type _ :=
  submoduleQuotient (I ^ n • (⊤ : Submodule R M))
    (I ^ (n + 1) • (⊤ : Submodule R M))

/-- The associated graded ring `Gr_I(A)`, with the direct-sum carrier. -/
abbrev associatedGradedRing
    {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  DirectSum ℕ (associatedGradedRingPiece I)

/-- The associated graded module `Gr_I(M)`, with the direct-sum carrier. -/
abbrev associatedGradedModule
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) : Type _ :=
  DirectSum ℕ (fun n => associatedGradedModulePiece (M := M) I n)

/-- The canonical graded-ring operations on the degreewise ideal quotients.
The construction is the usual product of ideal powers followed by passage to
the quotient; its existence is recorded as an interface because the proving
stage supplies the quotient-compatibility calculations. -/
theorem associatedGradedRing_gcommRing_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (DirectSum.GCommRing (associatedGradedRingPiece I)) := by
  sorry

noncomputable instance associatedGradedRing_gcommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedRingPiece I) :=
  Classical.choice (associatedGradedRing_gcommRing_exists I)

/-- The canonical graded-module action of `Gr_I(A)` on `Gr_I(M)`. -/
theorem associatedGradedModule_gmodule_exists
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Nonempty (DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n)) := by
  sorry

noncomputable instance associatedGradedModule_gmodule
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
  Classical.choice (associatedGradedModule_gmodule_exists I)

/-- A graded linear equivalence between the direct-sum associated graded
modules.  The linear equivalence is over `Gr_I(A)` and the two component
conditions make degree preservation explicit. -/
structure AssociatedGradedLinearEquiv
    {R : Type u} [CommRing R]
    (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] where
  toLinearEquiv :
    associatedGradedModule (M := M) I ≃ₗ[associatedGradedRing I]
      associatedGradedModule (M := N) I
  map_component' : ∀ (n : ℕ) (x : associatedGradedModulePiece (M := M) I n),
    ∃ y : associatedGradedModulePiece (M := N) I n,
      toLinearEquiv (DirectSum.of _ n x) = DirectSum.of _ n y
  inv_component' : ∀ (n : ℕ) (y : associatedGradedModulePiece (M := N) I n),
    ∃ x : associatedGradedModulePiece (M := M) I n,
      toLinearEquiv.symm (DirectSum.of _ n y) = DirectSum.of _ n x

/-- The denominator occurring in the degree-`n` quotient description of
`Gr_I(Coker(g))`. -/
def gradedCokernelDenominator
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) : Submodule R N :=
  I ^ (n + 1) • (⊤ : Submodule R N) ⊔
    (LinearMap.range g ⊓ I ^ n • (⊤ : Submodule R N))

/-- The degree-`n` quotient appearing in the source's formula for the
associated graded cokernel. -/
abbrev gradedCokernelPiece
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) : Type _ :=
  submoduleQuotient (I ^ n • (⊤ : Submodule R N))
    (gradedCokernelDenominator I g n)

/-- The concrete module cokernel used for `Coker(g)`. -/
abbrev linearMapCokernel
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) : Type _ :=
  N ⧸ LinearMap.range g

/-- Degreewise form of the source's identity
`Gr_I(Coker(g))_n = I^n N/(I^(n+1)N + g(M) ∩ I^nN)`. -/
theorem associatedGraded_cokernel_piece_equiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (g : M →ₗ[R] N) (n : ℕ) :
    Nonempty (associatedGradedModulePiece (M := linearMapCokernel g) I n ≃ₗ[R]
      gradedCokernelPiece I g n) := by
  sorry

/-- The intersection inclusion used to compare the degreewise cokernel
quotients of two congruent maps. -/
theorem approximate_complex_graded_intersection_le
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (c : ℕ)
    (g : M →ₗ[A] N) (g' : M →ₗ[A] N)
    (hc : ArtinReesWorks I g c)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) (n : ℕ) :
    LinearMap.range g ⊓ I ^ n • (⊤ : Submodule A N) ≤
      I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g' ⊓ I ^ n • (⊤ : Submodule A N)) := by
  sorry

/-- The equality of the two degreewise denominator submodules obtained by
applying the preceding inclusion in both directions. -/
theorem approximate_complex_graded_denominator_eq
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (c : ℕ)
    (g : M →ₗ[A] N) (g' : M →ₗ[A] N)
    (hc : ArtinReesWorks I g c) (hc' : ArtinReesWorks I g' c)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g ⊓ I ^ n • (⊤ : Submodule A N)) =
      I ^ (n + 1) • (⊤ : Submodule A N) ⊔
        (LinearMap.range g' ⊓ I ^ n • (⊤ : Submodule A N)) := by
  sorry

/-- Congruent exact complexes have isomorphic associated graded cokernels as
graded `Gr_I(A)`-modules. -/
theorem approximate_complex_graded
    {A L M N : Type*} [CommRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsNoetherianRing A]
    [Module.Finite A L] [Module.Finite A M] [Module.Finite A N]
    (I : Ideal A) (c : ℕ)
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (f' : L →ₗ[A] M) (g' : M →ₗ[A] N)
    (hS : Function.Exact f g) (hS' : g'.comp f' = 0)
    (hI : I ≤ Ring.jacobson A)
    (hc_f : ArtinReesWorks I f c)
    (hc_g : ArtinReesWorks I g c)
    (hf : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A M)) f' f)
    (hg : LinearMap.CongruentModulo
      (I ^ (c + 1) • (⊤ : Submodule A N)) g' g) :
    Nonempty (AssociatedGradedLinearEquiv I
      (M := linearMapCokernel g) (N := linearMapCokernel g')) := by
  sorry

/-! ## Flat base change -/

/-- Extension of scalars identifies the base change of `I^n M` with the
corresponding power of `IB` acting on `B ⊗[A] M`. -/
theorem submodule_baseChange_ideal_pow
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A M)).baseChange B =
      (I.map (algebraMap A B)) ^ n •
        (⊤ : Submodule B (B ⊗[A] M)) := by
  sorry

/-- Flat base change commutes with the preimage of an ideal-power submodule.
This is the source's displayed kernel/preimage identity, with the tensor
submodule written using Mathlib's canonical `Submodule.baseChange`. -/
theorem flat_baseChange_preimage
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [Module.Flat A B]
    (I : Ideal A) (f : M →ₗ[A] N) (n : ℕ) :
    Submodule.comap (LinearMap.baseChange B f)
        ((I.map (algebraMap A B)) ^ n •
          (⊤ : Submodule B (B ⊗[A] N))) =
      (Submodule.comap f (I ^ n • (⊤ : Submodule A N))).baseChange B := by
  sorry

/-- A working Artin-Rees exponent remains valid after flat extension of the
Noetherian base ring.  `LinearMap.baseChange B f` uses the canonically
isomorphic convention `B ⊗[A] M` for the source's `M ⊗_A B`. -/
theorem artinReesWorks_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Flat A B]
    (I : Ideal A) (f : M →ₗ[A] N) (c : ℕ)
    (hc : ArtinReesWorks I f c) :
    ArtinReesWorks (I.map (algebraMap A B))
      (LinearMap.baseChange B f) c := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit04
