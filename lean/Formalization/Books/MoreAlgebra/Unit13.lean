import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# More on Algebra, Chapter 13: Lifting and henselian pairs

This file records the definitions and theorem interfaces in the section
“Lifting and henselian pairs”.  Base change of modules and finite étale
algebras uses the canonical Mathlib constructions.
-/

namespace Formalization.Books.MoreAlgebra.Unit13

open CategoryTheory
open Polynomial
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The henselian-pair prerequisite

The earlier source section on henselian pairs has no Lean file in the
assigned earlier chapters.  This is the source-faithful predicate needed by
the present section; its Jacobson-radical part reuses the earlier Zariski-pair
definition.
-/

/-- The monic coprime-factorization definition of a henselian pair. -/
abbrev HenselianPair (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ (f : Polynomial A), f.Monic →
      ∀ (g₀ h₀ : Polynomial (A ⧸ I)),
        Polynomial.map (Ideal.Quotient.mk I) f = g₀ * h₀ →
          g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
            ∃ g h : Polynomial A,
              g.Monic ∧ h.Monic ∧ f = g * h ∧
                Polynomial.map (Ideal.Quotient.mk I) g = g₀ ∧
                Polynomial.map (Ideal.Quotient.mk I) h = h₀

/-! ## Isomorphism classes of finite projective modules -/

/-- A finite projective module regarded as an object of `ModuleCat`. -/
def FiniteProjectiveModule (R : Type u) [CommRing R] :=
  {M : ModuleCat.{u} R //
    Formalization.Books.Algebra.Unit78.FiniteProjective R M}

/-- Isomorphism of finite projective modules, used to form isomorphism classes. -/
abbrev FiniteProjectiveModuleIso
    {R : Type u} [CommRing R]
    (P Q : FiniteProjectiveModule R) : Prop :=
  Nonempty (P.1 ≅ Q.1)

/-- The setoid of isomorphism classes of finite projective modules. -/
def finiteProjectiveModuleSetoid (R : Type u) [CommRing R] :
    Setoid (FiniteProjectiveModule R) where
  r := FiniteProjectiveModuleIso
  iseqv := {
    refl := fun P => ⟨Iso.refl P.1⟩
    symm := by
      intro P Q h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro P Q T hPQ hQT
      rcases hPQ with ⟨e⟩
      rcases hQT with ⟨f⟩
      exact ⟨e ≪≫ f⟩
  }

/-- The set of isomorphism classes of finite projective `R`-modules. -/
abbrev FiniteProjectiveModuleIsoClasses
    (R : Type u) [CommRing R] :=
  Quotient (finiteProjectiveModuleSetoid R)

/-- Tensor-product base change of a finite projective module.  This is the
canonical module-theoretic presentation of `P/IP`. -/
noncomputable def finiteProjectiveBaseChange
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : FiniteProjectiveModule R) : FiniteProjectiveModule S := by
  letI : Module.Finite R (P.1 : Type u) := P.2.1
  letI : Module.Projective R (P.1 : Type u) := P.2.2
  let Q := S ⊗[R] (P.1 : Type u)
  letI : Module.Finite S Q := inferInstance
  letI : Module.Projective S Q := inferInstance
  exact ⟨ModuleCat.of S Q, ⟨inferInstance, inferInstance⟩⟩

/-- Reduction of an isomorphism class of finite projective modules. -/
noncomputable def finiteProjectiveReduction
    {R : Type u} [CommRing R] (I : Ideal R) :
    FiniteProjectiveModuleIsoClasses R →
      FiniteProjectiveModuleIsoClasses (R ⧸ I) := by
  refine Quotient.lift
    (fun P => Quotient.mk (finiteProjectiveModuleSetoid (R ⧸ I))
      (finiteProjectiveBaseChange P)) ?_
  intro P Q h
  rcases h with ⟨e⟩
  exact Quotient.sound ⟨(e.toLinearEquiv.baseChange R (R ⧸ I)).toModuleIso⟩

/-- The finite-projective lifting bijection for a henselian pair. -/
theorem lift_finite_projective_module
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : HenselianPair R I) :
    Function.Bijective (finiteProjectiveReduction I) := by
  sorry

/-- In particular, every finite projective module over the quotient has a
finite projective lift over the henselian base. -/
theorem exists_finite_projective_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : HenselianPair R I)
    (Q : FiniteProjectiveModule (R ⧸ I)) :
    ∃ P : FiniteProjectiveModule R,
      finiteProjectiveReduction I (Quotient.mk _ P) = Quotient.mk _ Q := by
  sorry

/-! ## Finite étale algebras -/

/-- Finite étale algebras over a henselian pair are unchanged by reduction. -/
theorem finite_etale_equivalence
    {A : Type u} [CommRing A] (I : Ideal A)
    (hI : HenselianPair A I) :
    (CommAlgCat.FiniteEtale.baseChange A (A ⧸ I)).IsEquivalence := by
  sorry

/-! ## Lifting maps from smooth algebras -/

/-- A quotient map from a smooth algebra to a henselian pair lifts.  The
commutation equalities express the source's `R`-algebra-map hypotheses using
the underlying ring homomorphisms and the canonical quotient algebra map. -/
theorem lift_smooth_henselian
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra.Smooth R S]
    (I : Ideal A) (hI : HenselianPair A I)
    (τ : S →+* (A ⧸ I))
    (hτ : τ.comp (algebraMap R S) =
      (Ideal.Quotient.mk I).comp (algebraMap R A)) :
    ∃ lift : S →+* A,
      lift.comp (algebraMap R S) = algebraMap R A ∧
        (Ideal.Quotient.mk I).comp lift = τ := by
  sorry

/-! ## Inverse systems and finite projective limits -/

/-- A sequential inverse system of commutative rings with the transition
properties appearing in the source. -/
structure SequentialRingSystem where
  ring : ℕ → CommRingCat.{u}
  transition : ∀ n, (ring (n + 1) : Type u) →+* (ring n : Type u)
  surjective : ∀ n, Function.Surjective (transition n)
  locallyNilpotentKernel : ∀ n,
    ∀ x, x ∈ RingHom.ker (transition n) → IsNilpotent x

/-- A ring together with the universal cone expressing `A = lim Aₙ`. -/
structure SequentialRingLimit
    (S : SequentialRingSystem) where
  A : CommRingCat.{u}
  projection : ∀ n, (A : Type u) →+* (S.ring n : Type u)
  projection_compat : ∀ n,
    projection n = (S.transition n).comp (projection (n + 1))
  lift : ∀ (B : CommRingCat.{u})
    (p : ∀ n, (B : Type u) →+* (S.ring n : Type u)),
    (hp : ∀ n, p n = (S.transition n).comp (p (n + 1))) →
    ∃ f : (B : Type u) →+* (A : Type u),
      ∀ n, (projection n).comp f = p n
  lift_unique : ∀ (B : CommRingCat.{u})
    (p : ∀ n, (B : Type u) →+* (S.ring n : Type u))
    (hp : ∀ n, p n = (S.transition n).comp (p (n + 1)))
    (f g : (B : Type u) →+* (A : Type u)),
    (∀ n, (projection n).comp f = p n) →
    (∀ n, (projection n).comp g = p n) → f = g

/-- A sequential system of modules over the rings in a sequential ring
system. -/
structure SequentialModuleSystem (S : SequentialRingSystem) where
  carrier : ∀ n, ModuleCat.{u} (S.ring n : Type u)
  transition : ∀ n,
    letI : Module (S.ring (n + 1) : Type u) (carrier n : Type u) :=
      Module.compHom (carrier n : Type u) (S.transition n)
    (carrier (n + 1) : Type u) →ₗ[(S.ring (n + 1) : Type u)] (carrier n : Type u)

/-- The `A`-module obtained from the `Aₙ`-module at stage `n` by the
projection from the inverse-limit ring. -/
noncomputable def restrictedModule
    (S : SequentialRingSystem) (L : SequentialRingLimit S)
    (T : SequentialModuleSystem S) (n : ℕ) :
    ModuleCat.{u} (L.A : Type u) := by
  letI : Algebra (L.A : Type u) (S.ring n : Type u) := (L.projection n).toAlgebra
  letI : Module (L.A : Type u) (T.carrier n : Type u) :=
    Module.compHom (T.carrier n : Type u) (L.projection n)
  exact ModuleCat.of (L.A : Type u) (T.carrier n : Type u)

/-- A module system equipped with an actual inverse-limit module.  The
`limit` field is the universal cone in `ModuleCat` after restricting the
scalars along the ring-limit projections. -/
structure SequentialModuleLimit
    (S : SequentialRingSystem) (L : SequentialRingLimit S)
    (T : SequentialModuleSystem S) where
  M : ModuleCat.{u} (L.A : Type u)
  projection : ∀ n, M ⟶ restrictedModule S L T n
  transitionA : ∀ n, restrictedModule S L T (n + 1) ⟶ restrictedModule S L T n
  transitionA_apply : ∀ n (x : T.carrier (n + 1)), transitionA n x = T.transition n x
  projection_compat : ∀ n,
    projection (n + 1) ≫ transitionA n = projection n
  limit : ∀ (N : ModuleCat (L.A : Type u))
    (f : ∀ n, N ⟶ restrictedModule S L T n),
    (∀ n, f (n + 1) ≫ transitionA n = f n) →
    ∃! g : N ⟶ M, ∀ n, g ≫ projection n = f n

/-- The source's assertion that each module transition induces an
isomorphism after scalar extension. -/
abbrev TransitionInducesBaseChangeIso
    (S : SequentialRingSystem) (T : SequentialModuleSystem S) (n : ℕ) : Prop :=
  letI : Algebra (S.ring (n + 1) : Type u) (S.ring n : Type u) :=
    (S.transition n).toAlgebra
  letI : Module (S.ring (n + 1) : Type u) (S.ring n : Type u) :=
    Module.compHom (S.ring n : Type u) (S.transition n)
  ∃ e : (S.ring n : Type u) ⊗[(S.ring (n + 1) : Type u)]
      (T.carrier (n + 1) : Type u) ≃ₗ[(S.ring n : Type u)]
        (T.carrier n : Type u),
    ∀ (a : S.ring n) (m : T.carrier (n + 1)),
      e (a ⊗ₜ m) = a • T.transition n m

/-- Finite projective modules are preserved by the inverse-limit construction
under the hypotheses of the source lemma. -/
theorem lim_finite_projective_gives_finite_projective
    (S : SequentialRingSystem) (L : SequentialRingLimit S)
    (T : SequentialModuleSystem S) (U : SequentialModuleLimit S L T)
    (h₁ : Formalization.Books.Algebra.Unit78.FiniteProjective
      (S.ring 0 : Type u) (T.carrier 0 : Type u))
    (hfiniteflat : ∀ n,
      Module.Finite (S.ring n : Type u) (T.carrier n : Type u) ∧
        Module.Flat (S.ring n : Type u) (T.carrier n : Type u))
    (hbasechange : ∀ n, TransitionInducesBaseChangeIso S T n) :
    Formalization.Books.Algebra.Unit78.FiniteProjective
        (L.A : Type u) (U.M : Type u) ∧
      ∀ n, Nonempty (
        letI : Algebra (L.A : Type u) (S.ring n : Type u) :=
          (L.projection n).toAlgebra
        (S.ring n : Type u) ⊗[(L.A : Type u)] (U.M : Type u) ≃ₗ[(S.ring n : Type u)]
          (T.carrier n : Type u)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit13
