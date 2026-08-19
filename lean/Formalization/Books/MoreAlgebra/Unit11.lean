import Formalization.Books.MoreAlgebra.Unit10
import Formalization.Books.MoreAlgebra.Unit09
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Formalization.Books.Algebra.Unit153
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# More on Algebra, Chapter 11: Henselian pairs

This file records the definitions and theorem interfaces in the section
“Henselian pairs”.  Pair and pair-morphism notation is reused from Chapter 10;
the quotient and integrality constructions are the canonical Mathlib ones.
-/

namespace Formalization.Books.MoreAlgebra.Unit11

open Set
open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit32
open Formalization.Books.Categories.Unit21
open scoped BigOperators TensorProduct

noncomputable section

universe u v

/-! ## Pairs and the henselian condition -/

abbrev Pair (A : Type u) [CommRing A] :=
  Formalization.Books.MoreAlgebra.Unit10.Pair A

abbrev PairHom {A B : Type u} [CommRing A] [CommRing B]
    (P : Pair A) (Q : Pair B) (f : A →+* B) : Prop :=
  Formalization.Books.MoreAlgebra.Unit10.PairHom P Q f

/-- Reduction of a pair along its distinguished ideal. -/
def pairReduction {A : Type u} [CommRing A] (P : Pair A) : A →+* A ⧸ P.ideal :=
  Ideal.Quotient.mk P.ideal

/-- A henselian pair, using the source's coprime monic factorization criterion. -/
def HenselianPair {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  P.ideal ≤ Ideal.jacobson (⊥ : Ideal A) ∧
    ∀ (f : Polynomial A), f.Monic →
      ∀ (g₀ h₀ : Polynomial (A ⧸ P.ideal)),
        g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
          Polynomial.map (Ideal.Quotient.mk P.ideal) f = g₀ * h₀ →
            ∃ g h : Polynomial A,
              g.Monic ∧ h.Monic ∧ f = g * h ∧
                Polynomial.map (Ideal.Quotient.mk P.ideal) g = g₀ ∧
                Polynomial.map (Ideal.Quotient.mk P.ideal) h = h₀

/-- The source's observation for local rings, with Mathlib's canonical
`HenselianLocalRing` class on the right. -/
theorem henselianPair_iff_henselianLocalRing
    {A : Type u} [CommRing A] [IsLocalRing A] :
    HenselianPair ({ ideal := IsLocalRing.maximalIdeal A } : Pair A) ↔
      HenselianLocalRing A := by
  sorry

/-! ## Étale reduction and the first permanence results -/

/-- The objectwise essential-surjectivity and fully-faithful content of the
étale reduction functor `B ↦ B/IB`.  The quotient map in the hom clause is
characterized by its universal commuting square, so no parallel quotient map
construction is introduced. -/
structure EtaleReductionEquivalence
    {A : Type u} [CommRing A] (P : Pair A) : Prop where
  essentially_surjective :
    ∀ {C : Type u} [CommRing C] [Algebra (A ⧸ P.ideal) C]
      [Algebra.Etale (A ⧸ P.ideal) C],
      Nonempty (Formalization.Books.Algebra.Unit143.EtaleLiftData A C P.ideal)
  fully_faithful :
    ∀ {B B' : Type u} [CommRing B] [CommRing B']
      [Algebra A B] [Algebra A B'] [Algebra.Etale A B] [Algebra.Etale A B'],
      ∀ (φ : B →ₐ[A] B'),
        ∃! q : (B ⧸ Ideal.map (algebraMap A B) P.ideal) →+*
            (B' ⧸ Ideal.map (algebraMap A B') P.ideal),
          q.comp (Ideal.Quotient.mk (Ideal.map (algebraMap A B) P.ideal)) =
            (Ideal.Quotient.mk (Ideal.map (algebraMap A B') P.ideal)).comp
              φ.toRingHom

theorem locally_nilpotent_henselian
    {A : Type u} [CommRing A] (P : Pair A)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal P.ideal) :
    EtaleReductionEquivalence P ∧ HenselianPair P := by
  sorry

/-- An inverse system whose transition maps are surjective with locally
nilpotent kernels. -/
def InverseSystemLocallyNilpotent
    {J : Type v} [Preorder J]
    (F : InverseSystem J CommRingCat.{u}) : Prop :=
  ∀ {i j : Jᵒᵖ} (f : i ⟶ j),
    Function.Surjective (F.map f).hom ∧
      Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal
        (RingHom.ker (F.map f).hom)

/-- The inverse-limit ideal at a stage is the kernel of the corresponding
limit projection. -/
theorem limit_henselian
    {J : Type v} [Preorder J]
    (F : InverseSystem J CommRingCat.{u}) [HasLimit F]
    (hF : InverseSystemLocallyNilpotent F) (j : J) :
    HenselianPair
      ({ ideal := RingHom.ker (limit.π F (Opposite.op j)).hom } :
        Pair ((limit F : CommRingCat.{u}) : Type u)) := by
  sorry

theorem complete_henselian
    {A : Type u} [CommRing A] (P : Pair A)
    [IsAdicComplete P.ideal A] : HenselianPair P := by
  sorry

/-! ## The finite-type helper -/

/-- Compatibility of a map with the first factor of two product
decompositions.  This is the source's “preserves product decompositions”
condition in a form that is directly usable with ring equivalences. -/
def PreservesFirstProductFactor
    {R T C₁ C₂ C₂' : Type u}
    [CommRing R] [CommRing T] [CommRing C₁] [CommRing C₂] [CommRing C₂']
    (e : R ≃+* C₁ × C₂') (e₀ : T ≃+* C₁ × C₂) (q : R →+* T) : Prop :=
  ∀ x, (e₀ (q x)).1 = (e x).1

/- The quotient algebra structure is induced by `f.toAlgebra`; spelling this
out once keeps the finite-helper interface independent of local instance
search. -/
def QuotientProductDecomposition
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B)
    (C₁ C₂ : Type u) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂] : Prop :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (A ⧸ I) (B ⧸ Ideal.map f I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  Nonempty ((B ⧸ Ideal.map f I) ≃ₐ[A ⧸ I] C₁ × C₂)

/- The varying complementary factor is quantified together with its ring and
algebra structures; this avoids making a noncanonical choice of a factor. -/
def FiniteTypeHelperConclusion
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B)
    (C₁ C₂ : Type u) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    (hdecomp : QuotientProductDecomposition I f C₁ C₂) : Prop :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (A ⧸ I) (B ⧸ Ideal.map f I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  ∃ (C₂' : Type u) (hC₂' : CommRing C₂')
    (hAlg₂' : Algebra (A ⧸ I) C₂'),
    letI : CommRing C₂' := hC₂'
    letI : Algebra (A ⧸ I) C₂' := hAlg₂'
    ∃ (e : (integralClosure A B ⧸
          Ideal.map (algebraMap A (integralClosure A B)) I) ≃ₐ[A ⧸ I]
          C₁ × C₂')
      (hIJ : Ideal.map (algebraMap A (integralClosure A B)) I ≤
        (Ideal.map f I).comap (integralClosure A B).val.toRingHom),
      let q := Ideal.quotientMap (Ideal.map f I)
        (integralClosure A B).val.toRingHom hIJ
      PreservesFirstProductFactor e.toRingEquiv
          (Classical.choice hdecomp).toRingEquiv q ∧
        ∃ g : integralClosure A B,
          e (Ideal.Quotient.mk
            (Ideal.map (algebraMap A (integralClosure A B)) I) g) = (1, 0) ∧
          Nonempty (Localization.Away g ≃+*
            Localization.Away (g : B))

theorem helper_finite_type
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (hfiniteType : RingHom.FiniteType f)
    (C₁ C₂ : Type u) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    (hdecomp : QuotientProductDecomposition I f C₁ C₂)
    (hfiniteC₁ : RingHom.Finite (algebraMap (A ⧸ I) C₁)) :
    FiniteTypeHelperConclusion I f C₁ C₂ hdecomp := by
  sorry

/-! ## Characterizations -/

def EtaleSectionLifting
    {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  ∀ {B : Type u} [CommRing B] (f : A →+* B), RingHom.Etale f →
    ∀ (σ : B →+* A ⧸ P.ideal),
      σ.comp f = Ideal.Quotient.mk P.ideal →
        ∃ s : B →+* A,
          s.comp f = RingHom.id A ∧
            (Ideal.Quotient.mk P.ideal).comp s = σ

def FiniteIdempotentLifting
    {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B],
    RingHom.Finite (algebraMap A B) →
      Function.Bijective
        (Formalization.Books.Algebra.Unit32.quotientIdempotentMap
          (Ideal.map (algebraMap A B) P.ideal))

def IntegralIdempotentLifting
    {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B],
    RingHom.IsIntegral (algebraMap A B) →
      Function.Bijective
        (Formalization.Books.Algebra.Unit32.quotientIdempotentMap
          (Ideal.map (algebraMap A B) P.ideal))

/-- The polynomial occurring in Gabber's root criterion. -/
def gabberPolynomial
    {A : Type u} [CommRing A] (n : ℕ)
    (a : Fin (n + 1) → A) : Polynomial A :=
  Polynomial.X ^ n * (Polynomial.X - Polynomial.C (1 : A)) +
    ∑ k : Fin (n + 1), Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)

def GabberRootCriterion
    {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  P.ideal ≤ Ideal.jacobson (⊥ : Ideal A) ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (a : Fin (n + 1) → A), (∀ k, a k ∈ P.ideal) →
        ∃ α : A, α - 1 ∈ P.ideal ∧
          (gabberPolynomial n a).IsRoot α

theorem characterize_henselian_pair
    {A : Type u} [CommRing A] (P : Pair A) :
    List.TFAE [HenselianPair P, EtaleSectionLifting P,
      FiniteIdempotentLifting P, IntegralIdempotentLifting P,
      GabberRootCriterion P] := by
  sorry

theorem gabber_root_unique
    {A : Type u} [CommRing A] (P : Pair A) (n : ℕ)
    (a : Fin (n + 1) → A) (ha : ∀ k, a k ∈ P.ideal)
    {α β : A} (hα : α - 1 ∈ P.ideal)
    (hαroot : (gabberPolynomial n a).IsRoot α)
    (hβ : β - 1 ∈ P.ideal)
    (hβroot : (gabberPolynomial n a).IsRoot β) : α = β := by
  sorry

/-! ## Changing ideals and extensions -/

theorem change_ideal_henselian_pair
    {A : Type u} [CommRing A] (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A)) :
    HenselianPair ({ ideal := I } : Pair A) ↔
      HenselianPair ({ ideal := J } : Pair A) := by
  sorry

theorem integral_over_henselian_pair
    {A B : Type u} [CommRing A] [CommRing B]
    (P : Pair A) [Algebra A B]
    (hIntegral : RingHom.IsIntegral (algebraMap A B)) :
    HenselianPair
      ({ ideal := Ideal.map (algebraMap A B) P.ideal } : Pair B) := by
  sorry

theorem henselian_henselian_pair
    {A : Type u} [CommRing A] (I J : Ideal A) (hIJ : I ≤ J) :
    (HenselianPair ({ ideal := I } : Pair A) ∧
      HenselianPair
        ({ ideal := Ideal.map (Ideal.Quotient.mk I) J } : Pair (A ⧸ I))) ↔
      HenselianPair ({ ideal := J } : Pair A) := by
  sorry

theorem sum_henselian
    {A : Type u} [CommRing A] (I I' : Ideal A)
    (hI : HenselianPair ({ ideal := I } : Pair A))
    (hI' : HenselianPair ({ ideal := I' } : Pair A)) :
    HenselianPair ({ ideal := I + I' } : Pair A) := by
  sorry

theorem product_henselian_pairs
    {J : Type v} {A : J → Type u} [∀ j, CommRing (A j)]
    (I : ∀ j, Ideal (A j)) :
    HenselianPair ({ ideal := Ideal.pi I } : Pair (∀ j, A j)) ↔
      ∀ j, HenselianPair ({ ideal := I j } : Pair (A j)) := by
  sorry

/-! ## Limits and filtered colimits -/

def InversePairSystem
    {J : Type v} [Preorder J]
    (F : InverseSystem J CommRingCat.{u})
    (I : ∀ i : Jᵒᵖ, Ideal (F.obj i)) : Prop :=
  ∀ {i j : Jᵒᵖ} (f : i ⟶ j),
    Ideal.map (F.map f).hom (I i) ≤ I j

def inverseLimitIdeal
    {J : Type v} [Preorder J]
    (F : InverseSystem J CommRingCat.{u}) [HasLimit F]
    (I : ∀ i : Jᵒᵖ, Ideal (F.obj i)) :
    Ideal ((limit F : CommRingCat.{u}) : Type u) :=
  ⨅ i, Ideal.comap (limit.π F i).hom (I i)

theorem limits_henselian
    {J : Type v} [Preorder J]
    (F : InverseSystem J CommRingCat.{u}) [HasLimit F]
    (I : ∀ i : Jᵒᵖ, Ideal (F.obj i))
    (hpair : ∀ i, HenselianPair ({ ideal := I i } : Pair (F.obj i)))
    (hI : InversePairSystem F I) :
    HenselianPair ({ ideal := inverseLimitIdeal F I } :
      Pair ((limit F : CommRingCat.{u}) : Type u)) := by
  sorry

def SystemPairSystem
    {J : Type v} [Preorder J]
    (F : System J CommRingCat.{u})
    (I : ∀ j : J, Ideal (F.obj j)) : Prop :=
  ∀ {i j : J} (f : i ⟶ j),
    Ideal.map (F.map f).hom (I i) ≤ I j

def filteredColimitIdeal
    {J : Type v} [Preorder J]
    (F : System J CommRingCat.{u}) [HasColimit F]
    (I : ∀ j : J, Ideal (F.obj j)) :
    Ideal ((colimit F : CommRingCat.{u}) : Type u) :=
  Ideal.span (⋃ j,
    (Ideal.map (colimit.ι F j).hom (I j) :
      Set ((colimit F : CommRingCat.{u}) : Type u)))

theorem filtered_colimits_henselian
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : System J CommRingCat.{u}) [HasColimit F]
    (I : ∀ j : J, Ideal (F.obj j))
    (hpair : ∀ j, HenselianPair ({ ideal := I j } : Pair (F.obj j)))
    (hI : SystemPairSystem F I) :
    HenselianPair ({ ideal := filteredColimitIdeal F I } :
      Pair ((colimit F : CommRingCat.{u}) : Type u)) := by
  sorry

/-! ## Moret--Bailly's non-filtered-colimit example -/

abbrev moretBaillyRing (p : ℕ) [Fact p.Prime] :=
  PadicInt p ⊗[ℤ] PadicInt p

def moretBaillyIdeal (p : ℕ) [Fact p.Prime] :
    Ideal (moretBaillyRing p) :=
  Ideal.map (algebraMap ℤ (moretBaillyRing p))
    (Ideal.span ({(p : ℤ)} : Set ℤ))

theorem moret_bailly_example
    (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    ¬ HenselianPair ({ ideal := moretBaillyIdeal p } : Pair (moretBaillyRing p)) ∧
      ∃ e : moretBaillyRing p,
        IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  sorry

/-! ## Largest henselian ideal and connectedness -/

theorem largest_henselian_ideal
    (A : Type u) [CommRing A] :
    ∃ I : Ideal A, HenselianPair ({ ideal := I } : Pair A) ∧
      ∀ J : Ideal A, HenselianPair ({ ideal := J } : Pair A) → J ≤ I := by
  sorry

theorem irreducible_henselian_pair_connected
    {A : Type u} [CommRing A] (P : Pair A)
    (hP : HenselianPair P) (p : Ideal A) (hp : p.IsPrime) :
    _root_.IsConnected (PrimeSpectrum.zeroLocus ((p ⊔ P.ideal : Ideal A) : Set A)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit11
