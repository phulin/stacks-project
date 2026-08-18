import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange

/-!
# Commutative Algebra, Chapter 126: Algebras and modules of finite presentation

This file records the definitions and theorem interfaces in the chapter.  The
localization of a quotient is represented by Mathlib's `Localization` and
`LocalizedModule` constructions, and module witnesses are bundled as
`ModuleCat` objects so that their additive and scalar structures remain part of
the declaration.
-/

open scoped TensorProduct

namespace Formalization.Books.Algebra.Unit126

universe u v w

noncomputable section

/-! ### Quotients and localizations -/

/-- The ring `S⁻¹(R/I)` occurring in the module-construction lemmas. -/
abbrev localizedQuotientRing {R : Type u} [CommRing R]
    (I : Ideal R) (S : Submonoid R) : Type u :=
  Localization (S.map (Ideal.Quotient.mk I))

/-- The localization of `M/IM` at the image of `S`, over `S⁻¹(R/I)`. -/
abbrev localizedQuotientModule {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (S : Submonoid R) : Type (max u v) :=
  LocalizedModule (S.map (Ideal.Quotient.mk I)) (M ⧸ I • (⊤ : Submodule R M))

/-- The ring map induced by localizing a ring map at a submonoid and its image. -/
noncomputable def localizedRingHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Submonoid A) :
    Localization M →+* Localization (M.map f) :=
  IsLocalization.map (Localization (M.map f)) f M.le_comap_map

/-! ### Descent of finite type and finite presentation -/

/-- Finite type descends and ascends along a faithfully flat base change. -/
theorem finite_type_descends {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingHom.FiniteType f ↔
      RingHom.FiniteType (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

/-- Finite presentation descends and ascends along a faithfully flat base change. -/
theorem finite_presentation_descends {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingHom.FinitePresentation f ↔
      RingHom.FinitePresentation (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

/-! ### Finite modules over localized quotients -/

/-- Finite and finitely presented modules over `S⁻¹(R/I)` descend to `R`. -/
theorem construct_fp_module {R : Type u} [CommRing R] (I : Ideal R) (S : Submonoid R) :
    (∀ M' : ModuleCat.{max u v} (localizedQuotientRing I S),
      Module.Finite (localizedQuotientRing I S) (M' : Type (max u v)) →
        ∃ M : ModuleCat.{max u v} R,
          Module.Finite R (M : Type (max u v)) ∧
            Nonempty
              (localizedQuotientModule I S (M := (M : Type (max u v))) ≃ₗ[
                localizedQuotientRing I S] (M' : Type (max u v)))) ∧
    (∀ M' : ModuleCat.{max u v} (localizedQuotientRing I S),
      Module.FinitePresentation (localizedQuotientRing I S) (M' : Type (max u v)) →
        ∃ M : ModuleCat.{max u v} R,
          Module.FinitePresentation R (M : Type (max u v)) ∧
            Nonempty
              (localizedQuotientModule I S (M := (M : Type (max u v))) ≃ₗ[
                localizedQuotientRing I S] (M' : Type (max u v)))) := by
  sorry

/-! ### Finite modules after localization -/

/-- Finite and finitely presented localized modules can be lifted to `R`. -/
theorem construct_fp_module_from_localization {R : Type u} [CommRing R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    (Module.Finite (Localization S) (LocalizedModule S (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.Finite R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) ∧
    (Module.FinitePresentation (Localization S) (LocalizedModule S (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.FinitePresentation R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) := by
  sorry

/-! ### The stalk case -/

/-- The preceding localization lifting result specialized to a prime stalk. -/
theorem construct_fp_module_from_stalk {R : Type u} [CommRing R]
    (p : Ideal R) [hp : p.IsPrime] (M : ModuleCat.{v} R) :
    (Module.Finite (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.Finite R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) ∧
    (Module.FinitePresentation (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.FinitePresentation R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) := by
  sorry

/-! ### Local isomorphisms and spreading out -/

/-- A finitely presented map which is an isomorphism at a prime spreads out
to a product decomposition after inverting an element away from that prime. -/
theorem local_isomorphism {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) (q : Ideal S) [hp : p.IsPrime] [hq : q.IsPrime]
    (hpq : p = q.comap f) :
    letI : Algebra R S := f.toAlgebra
    RingHom.FinitePresentation f →
      Function.Bijective (Localization.localRingHom p q f hpq) →
        ∃ a : R, a ∉ p ∧
          ∃ C : CommAlgCat (Localization.Away a),
            Nonempty
              (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) ≃ₐ[
                Localization.Away a]
                (Localization.Away a × (C : Type u))) := by
  sorry

/-- An isomorphism between finite-presentation local rings spreads out to an
isomorphism after inverting elements outside the corresponding primes. -/
theorem isomorphic_local_rings {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    (f : R →+* S) (f' : R →+* S') (q : Ideal S) (q' : Ideal S')
    [hq : q.IsPrime] [hq' : q'.IsPrime] :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R S' := f'.toAlgebra
    RingHom.FinitePresentation f →
      RingHom.FinitePresentation f' →
        Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q') →
          ∃ g : S, g ∉ q ∧
            ∃ g' : S', g' ∉ q' ∧
              Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := by
  sorry

/-! ### Nilpotent thickenings -/

/-- Finite type lifts across a nilpotent ideal. -/
theorem finite_type_mod_nilpotent {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : IsNilpotent I) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    RingHom.FiniteType (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) →
      RingHom.FiniteType f := by
  sorry

/-- Surjectivity lifts across a locally nilpotent thickening. -/
theorem surjective_mod_locally_nilpotent {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquot : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S'))).comp f.toRingHom))
    (hfinite : RingHom.FiniteType (algebraMap R S')) :
    Function.Surjective f := by
  sorry

/-! ### Isomorphisms modulo an ideal -/

/-- The localized quotient isomorphism in the next theorem is recorded by an
equivalence whose values on quotient representatives are the canonical local
map.  This avoids introducing a duplicate quotient-map definition. -/
def localQuotientIsomorphism {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S)
    [q.IsPrime]
    (e : (Localization q.primeCompl ⧸
        (I.map (algebraMap R (Localization q.primeCompl)))) ≃+*
      (Localization (q.primeCompl.map f.toRingHom) ⧸
        (I.map (algebraMap R (Localization (q.primeCompl.map f.toRingHom)))))) : Prop :=
  ∀ x : Localization q.primeCompl,
    e (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (localizedRingHom f.toRingHom q.primeCompl x)

/-- A surjective map satisfying the local quotient and flatness hypotheses is
an isomorphism after inverting an element outside the chosen prime. -/
theorem isomorphism_modulo_ideal {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (q : Ideal S) [hq : q.IsPrime]
    (hIq : I.map (algebraMap R S) ≤ q)
    (hsurj : Function.Surjective f)
    (hlocal : ∃ e :
      (Localization q.primeCompl ⧸
          (I.map (algebraMap R (Localization q.primeCompl)))) ≃+*
        (Localization (q.primeCompl.map f.toRingHom) ⧸
          (I.map (algebraMap R (Localization (q.primeCompl.map f.toRingHom))))),
      localQuotientIsomorphism f I q e)
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S'))
    (hflat : Module.Flat R (Localization (q.primeCompl.map f.toRingHom))) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (localizedRingHom f.toRingHom (Submonoid.powers g)) := by
  sorry

/-! ### Isomorphisms modulo a locally nilpotent ideal -/

/-- The quotient isomorphism in the final theorem is recorded by its action on
canonical quotient representatives. -/
def quotientIsomorphism {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (e : (S ⧸ I.map (algebraMap R S)) ≃+* (S' ⧸ I.map (algebraMap R S'))) : Prop :=
  ∀ x : S,
    e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x)

/-- Under the finite type, finite presentation, flatness, and local nilpotence
hypotheses, an isomorphism modulo the ideal is an isomorphism. -/
theorem isomorphism_modulo_locally_nilpotent {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquot : ∃ e : (S ⧸ I.map (algebraMap R S)) ≃+* (S' ⧸ I.map (algebraMap R S')),
      quotientIsomorphism f I e)
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S'))
    (hflat : Module.Flat R S') :
    Function.Bijective f := by
  sorry

end

end Formalization.Books.Algebra.Unit126
