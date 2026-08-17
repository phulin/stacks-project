import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Formalization.Books.Algebra.Unit14.BaseChange

/-!
# More on Algebra, Chapter 81: Relatively finitely presented modules

The source section is formalized using Mathlib's canonical finiteness
predicates.  A presentation by `R[x₁, ..., xₙ]` is represented by a
surjective map from `MvPolynomial (Fin n) R`, and the induced module action is
made explicit with `Module.compHom`.
-/

namespace Formalization.Books.MoreAlgebra.Unit81

open scoped TensorProduct

noncomputable section

universe u v w

/-! ## The relative finite-presentation predicate -/

/--
An `A`-module is finitely presented relative to the ring map `f : R →+* A`
when it is finitely presented after restricting scalars along one finite
polynomial presentation of `A` over `R`.

This is condition (1) of the source lemma; the later equivalence theorem
records the source's conditions (2) and (3).
-/
def RelativelyFinitelyPresented
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  letI : Algebra R A := f.toAlgebra
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α ∧
      letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
      Module.FinitePresentation (MvPolynomial (Fin n) R) M

/-- The counterexample in the introduction: finite presentation over the
quotient does not imply finite presentation over the original polynomial
ring. -/
theorem intro_counterexample
    {k : Type u} [Field k] :
    let R := MvPolynomial ℕ k
    let I : Ideal R := Ideal.span (Set.range (MvPolynomial.X : ℕ → R))
    let q : R →+* (R ⧸ I) := Ideal.Quotient.mk I
    RingHom.Finite q ∧
      RingHom.FiniteType (RingHom.id R) ∧
        RingHom.FiniteType q ∧
          Module.Finite (R ⧸ I) (R ⧸ I) ∧
            Module.FinitePresentation (R ⧸ I) (R ⧸ I) ∧
              ¬ (letI : Module R (R ⧸ I) := Module.compHom (R ⧸ I) q
                Module.FinitePresentation R (R ⧸ I)) := by
  sorry

/-! ## The three equivalent presentations -/

/-- Relative finite presentation is independent of the chosen polynomial
presentation of the finite-type algebra. -/
theorem relativelyFinitelyPresented_iff_all_presentations
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) :
    letI : Algebra R A := f.toAlgebra
    RelativelyFinitelyPresented f M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α →
          letI : Module (MvPolynomial (Fin n) R) M :=
            Module.compHom M α.toRingHom
          Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  sorry

/-- The quotient-algebra formulation of relative finite presentation. -/
theorem relativelyFinitelyPresented_iff_surjective_from_finitelyPresented
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) :
    letI : Algebra R A := f.toAlgebra
    RelativelyFinitelyPresented f M ↔
      ∀ {A' : Type*} [CommRing A'] [Algebra R A']
        (q : A' →ₐ[R] A),
        Function.Surjective q →
          RingHom.FinitePresentation (algebraMap R A') →
            letI : Module A' M := Module.compHom M q.toRingHom
            Module.FinitePresentation A' M := by
  sorry

/-- A relatively finitely presented module is finitely presented over `A`. -/
theorem relativelyFinitelyPresented.finitePresentation
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f)
    (hM : RelativelyFinitelyPresented f M) :
    Module.FinitePresentation A M := by
  sorry

/-! ## The remarks following the definition -/

/-- If `R → A` is finitely presented, relative and absolute finite
presentation of an `A`-module coincide. -/
theorem relativelyFinitelyPresented_iff_finitePresentation
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FinitePresentation f) :
    RelativelyFinitelyPresented f M ↔ Module.FinitePresentation A M := by
  sorry

/-- `A` is relatively finitely presented over `R` exactly when the algebra
map `R → A` is finitely presented. -/
theorem relativelyFinitelyPresented_self_iff
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    RelativelyFinitelyPresented f A ↔ RingHom.FinitePresentation f := by
  sorry

/-- Over a Noetherian base, relative finite presentation reduces to finite
generation over the finite-type algebra. -/
theorem relativelyFinitelyPresented_iff_finite
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) [IsNoetherianRing R] :
    RelativelyFinitelyPresented f M ↔ Module.Finite A M := by
  sorry

/-! ## Stability under finite maps -/

/-- Relative finite presentation is unchanged on passing across a finite map
between finite-type `R`-algebras. -/
theorem relativelyFinitelyPresented_finite_extension_iff
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType (g.comp f))
    (hfinite : RingHom.Finite g) :
    (letI : Module A M := Module.compHom M g;
      RelativelyFinitelyPresented f M) ↔
      RelativelyFinitelyPresented (g.comp f) M := by
  sorry

/-! ## Localization, base change, pullback, and composition -/

/-- Localizing an `A`-module at `g` carries relative finite presentation from
`R_f` to `R`.  The target module is Mathlib's canonical `LocalizedModule`. -/
theorem relativelyFinitelyPresented_localize
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R)
    (h : Localization.Away f →+* A)
    (hh : RingHom.FiniteType h) (g : A)
    (hM : RelativelyFinitelyPresented h M) :
    RelativelyFinitelyPresented
      (((algebraMap A (Localization.Away g)).comp h).comp
        (algebraMap R (Localization.Away f)))
      (LocalizedModule.Away g M) := by
  sorry

/-- Relative finite presentation is preserved by arbitrary base change.  The
module is expressed with the earlier chapter's canonical extension-of-scalars
model for the source's `M ⊗[R] R'`. -/
theorem relativelyFinitelyPresented_baseChange
    {R A R' M : Type*} [CommRing R] [CommRing A] [CommRing R']
    [AddCommGroup M] [Module A M] (f : R →+* A) (g : R →+* R')
    (hf : RingHom.FiniteType f)
    (hM : RelativelyFinitelyPresented f M) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R' (A ⊗[R] R') :=
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
    RelativelyFinitelyPresented
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g) := by
  sorry

/-- Pulling an `A`-module along a finitely presented map `A → A'` preserves
relative finite presentation. -/
theorem relativelyFinitelyPresented_pull
    {R A A' M : Type*} [CommRing R] [CommRing A] [CommRing A']
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) (g : A →+* A')
    (hg : RingHom.FinitePresentation g)
    (hM : RelativelyFinitelyPresented f M) :
    RelativelyFinitelyPresented (g.comp f)
      ((ModuleCat.extendScalars g).obj (ModuleCat.of A M) : Type _) := by
  sorry

/-- Relative finite presentation composes with a finitely presented first
map. -/
theorem relativelyFinitelyPresented_comp
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] (f : R →+* A) (g : A →+* B)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType g)
    (hfp : RingHom.FinitePresentation f)
    (hM : RelativelyFinitelyPresented g M) :
    RelativelyFinitelyPresented (g.comp f) M := by
  sorry

/-! ## Gluing and exact sequences -/

/-- Relative finite presentation is local on a finite standard-open cover of
the target algebra. -/
theorem relativelyFinitelyPresented_glue_iff
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (f : R →+* A)
    (hf : RingHom.FiniteType f) (s : Finset A)
    (hs : Ideal.span (s : Set A) = ⊤) :
    (∀ x : s,
      RelativelyFinitelyPresented
        ((algebraMap A (Localization.Away (x : A))).comp f)
        (LocalizedModule.Away (x : A) M)) ↔
      RelativelyFinitelyPresented f M := by
  sorry

/-- The middle term of a short exact sequence is relatively finitely
presented when the ends are. -/
theorem relativelyFinitelyPresented_middle_of_shortExact
    {R A M' M M'' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
    [AddCommGroup M''] [Module A M''] (f : R →+* A)
    (hf : RingHom.FiniteType f) (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hi : Function.Injective i) (hex : Function.Exact i p)
    (hp : Function.Surjective p)
    (hM' : RelativelyFinitelyPresented f M')
    (hM'' : RelativelyFinitelyPresented f M'') :
    RelativelyFinitelyPresented f M := by
  sorry

/-- In a short exact sequence, a relatively finitely presented middle term
and a finite left term give a relatively finitely presented quotient. -/
theorem relativelyFinitelyPresented_right_of_shortExact
    {R A M' M M'' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
    [AddCommGroup M''] [Module A M''] (f : R →+* A)
    (hf : RingHom.FiniteType f) (i : M' →ₗ[A] M) (p : M →ₗ[A] M'')
    (hi : Function.Injective i) (hex : Function.Exact i p)
    (hp : Function.Surjective p) (hM'finite : Module.Finite A M')
    (hM : RelativelyFinitelyPresented f M) :
    RelativelyFinitelyPresented f M'' := by
  sorry

/-- Relative finite presentation passes to the two summands of a finite
direct sum. -/
theorem relativelyFinitelyPresented_of_prod
    {R A M M' : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (f : R →+* A) (hf : RingHom.FiniteType f)
    (h : RelativelyFinitelyPresented f (M × M')) :
    RelativelyFinitelyPresented f M ∧
      RelativelyFinitelyPresented f M' := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit81
