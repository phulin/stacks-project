import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat

namespace Formalization.Books.LocalCohomology.Unit17

noncomputable section

open scoped BigOperators TensorProduct

/-!
This file records the declarations from Chapter 17, “Frobenius action”.  The
proofs are intentionally deferred; the definitions use Mathlib's canonical
Frobenius, cotangent-module, tensor-product, length, and flatness APIs.
-/

/-- Frobenius base change of a module, with the scalar action on the second
factor restricted along the Frobenius endomorphism. -/
def frobeniusBaseChange
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (p : ℕ) [ExpChar A p] : Prop :=
  letI : Module A A := Module.compHom A (frobenius A p)
  Nonempty ((M ⊗[A] A) ≃ₗ[A] M)

/-- A finite Frobenius-stable module over a Noetherian local ring is free. -/
theorem finite_frobenius_base_change_is_free
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    (hM : frobeniusBaseChange (A := A) (M := M) p) :
    Module.Free A M := by
  sorry

/-- The conormal class represented by an entry of a list of generators. -/
def conormalGenerator
    {A : Type*} [CommRing A] (xs : List A) (i : Fin xs.length) :
    Ideal.Cotangent (Ideal.ofList xs) :=
  Ideal.toCotangent (Ideal.ofList xs)
    ⟨xs.get i, by
      apply Ideal.subset_span
      exact xs.get_mem i⟩

/-- Independence of a list of ring elements, as used in the chapter. -/
def independent {A : Type*} [CommRing A] (xs : List A) : Prop :=
  ∀ (a : Fin xs.length → A),
    (∑ i, a i * xs.get i = 0) →
      ∀ i, a i ∈ Ideal.ofList xs

/-- The list formulation of independence is equivalent to the conormal basis
formulation in the text. -/
theorem independent_iff_cotangent_has_basis
    {A : Type*} [CommRing A] (xs : List A) :
    independent xs ↔
      ∃ b : Module.Basis (Fin xs.length) (A ⧸ Ideal.ofList xs)
          (Ideal.Cotangent (Ideal.ofList xs)),
        ∀ i, b i = conormalGenerator xs i := by
  sorry

/-- Lemma 1: an independent product in the last position can be replaced by
its first factor. -/
theorem independent_append_mul_factor
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) :
    independent (xs ++ [f]) := by
  sorry

/-- The exact sequence used to split the length of a quotient after replacing
the last generator by a product.  The two maps are characterized on quotient
representatives by the displayed multiplication and quotient maps. -/
theorem independent_multiplication_exact
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) :
    ∃ (u : (A ⧸ Ideal.ofList (xs ++ [g])) →ₗ[A]
          (A ⧸ Ideal.ofList (xs ++ [f * g])))
      (v : (A ⧸ Ideal.ofList (xs ++ [f * g])) →ₗ[A]
          (A ⧸ Ideal.ofList (xs ++ [f]))),
      Function.Injective u ∧ Function.Surjective v ∧ Function.Exact u v ∧
        (∀ x : A,
          u (Ideal.Quotient.mk (Ideal.ofList (xs ++ [g])) x) =
            Ideal.Quotient.mk (Ideal.ofList (xs ++ [f * g])) (f * x)) ∧
        (∀ x : A,
          v (Ideal.Quotient.mk (Ideal.ofList (xs ++ [f * g])) x) =
            Ideal.Quotient.mk (Ideal.ofList (xs ++ [f])) x) := by
  sorry

/-- Length additivity for the independent product replacement in Lemma 2. -/
theorem independent_length_mul
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g]))
    (hfinite : IsFiniteLength A
      (A ⧸ Ideal.ofList (xs ++ [f * g]))) :
    Module.length A (A ⧸ Ideal.ofList (xs ++ [f * g])) =
      Module.length A (A ⧸ Ideal.ofList (xs ++ [f])) +
        Module.length A (A ⧸ Ideal.ofList (xs ++ [g])) := by
  sorry

/-- The list of powers appearing in Lemma 3. -/
def powerList {A : Type*} [CommRing A] (xs : List A)
    (e : Fin xs.length → ℕ) : List A :=
  List.ofFn (fun i => (xs.get i) ^ e i)

/-- The length of a quotient by independent powers of a system of generators. -/
theorem length_quotient_of_independent_powers
    {A : Type*} [CommRing A] [IsLocalRing A] (xs : List A)
    (hmax : Ideal.ofList xs = IsLocalRing.maximalIdeal A)
    (e : Fin xs.length → ℕ) (he : ∀ i, 0 < e i)
    (h : independent (powerList xs e)) :
    Module.length A (A ⧸ Ideal.ofList (powerList xs e)) =
      (↑(∏ i : Fin xs.length, e i) : ℕ∞) := by
  sorry

/-- Flat extension preserves the chapter's independence condition. -/
theorem independent_map_of_flat
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : RingHom.Flat φ) (xs : List A) (h : independent xs) :
    independent (xs.map φ) := by
  sorry

/-- Kunz's characterization of regular Noetherian rings by flat Frobenius. -/
theorem kunz_frobenius_flat_iff_regular
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : ℕ)
    [Fact p.Prime] [CharP A p] :
    IsRegularRing A ↔ RingHom.Flat (frobenius A p) := by
  sorry

end

end Formalization.Books.LocalCohomology.Unit17
