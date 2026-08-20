import Formalization.Books.MoreAlgebra.Unit115.AbhyankarTame
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.Basic

/-!
# More on Algebra, Chapter 117: Eliminating ramification, II

This file records the definitions and theorem interfaces in the section
“Eliminating ramification, II”.  The local DVR diagrams in the source's
construction remark are represented by `BaseChangePlaceData` from Chapter
115; the propositions below quantify over those places rather than choosing
particular localizations.
-/

namespace Formalization.Books.MoreAlgebra.Unit117

open Formalization.Books.Algebra.Unit162
open Formalization.Books.MoreAlgebra.Unit112
open Formalization.Books.MoreAlgebra.Unit115

noncomputable section

universe u v w z

/-! ## Solutions and their local places -/

/-- The local DVR map carried by a place in the base-change construction. -/
def localDVRMap (D : LocalDVRMap) :
    letI := D.sourceCommRing
    letI := D.targetCommRing
    letI := D.sourceDomain
    letI := D.targetDomain
    letI := D.sourceDVR
    letI := D.targetDVR
    DVRMap D.source D.target := by
  letI := D.sourceCommRing
  letI := D.targetCommRing
  letI := D.sourceDomain
  letI := D.targetDomain
  letI := D.sourceDVR
  letI := D.targetDVR
  exact D.map

/-- Weak unramifiedness of one local map in the construction remark. -/
def localWeaklyUnramified (D : LocalDVRMap) : Prop := by
  letI := D.sourceCommRing
  letI := D.targetCommRing
  letI := D.sourceDomain
  letI := D.targetDomain
  letI := D.sourceDVR
  letI := D.targetDVR
  exact WeaklyUnramified D.map

/-- Formal smoothness of one local map in the relevant adic topology. -/
def localFormallySmooth (D : LocalDVRMap) : Prop := D.formallySmooth

/-- A finite field extension together with the local places from the source's
construction remark. -/
structure FiniteSolution
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B)
    (F : FractionFieldExtension (K := K) (L := L) E) where
  finite : FiniteDimensional K K₁
  places : BaseChangePlaceData E

/-- The source's weak-solution predicate, with the construction remark
encoded by the supplied `BaseChangePlaceData`. -/
def IsWeakSolution
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} {F : FractionFieldExtension (K := K) (L := L) E}
    (S : FiniteSolution (K₁ := K₁) E F) : Prop :=
  ∀ i j, localWeaklyUnramified (S.places.localExtension i j)

/-- The source's solution predicate. -/
def IsSolution
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} {F : FractionFieldExtension (K := K) (L := L) E}
    (S : FiniteSolution (K₁ := K₁) E F) : Prop :=
  ∀ i j, localFormallySmooth (S.places.localExtension i j)

/-- A solution whose finite field extension is separable. -/
def IsSeparableSolution
    {A B K L K₁ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    {E : DVRMap A B} {F : FractionFieldExtension (K := K) (L := L) E}
    (S : FiniteSolution (K₁ := K₁) E F) : Prop :=
  IsSolution S ∧ Algebra.IsSeparable K K₁

/-- Existence of a finite solution for an extension of DVRs. -/
def HasFiniteSolution
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B)
    (F : FractionFieldExtension (K := K) (L := L) E) : Prop :=
  ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
    (hfinite : letI := hKK₁; FiniteDimensional K K₁),
    letI := hK₁
    letI := hKK₁
    letI := hfinite
    ∃ S : FiniteSolution (K₁ := K₁) E F, IsSolution S

/-- Existence of a finite separable solution. -/
def HasFiniteSeparableSolution
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B)
    (F : FractionFieldExtension (K := K) (L := L) E) : Prop :=
  ∃ (K₁ : Type*) (hK₁ : Field K₁) (hKK₁ : Algebra K K₁)
    (hfinite : letI := hKK₁; FiniteDimensional K K₁)
    (hsep : letI := hKK₁; Algebra.IsSeparable K K₁),
    letI := hK₁
    letI := hKK₁
    letI := hfinite
    letI := hsep
    ∃ S : FiniteSolution (K₁ := K₁) E F, IsSolution S

/-! ## The first two permanence lemmas -/

/-- Solutions remain solutions after a further finite field extension. -/
theorem solution_goes_up
    {A B K L K₁ K₂ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Field K₂] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (S : FiniteSolution (K₁ := K₁) E F)
    [FiniteDimensional K₁ K₂] (hS : IsSolution S) :
    ∃ T : FiniteSolution (K₁ := K₂) E F, IsSolution T := by
  sorry

/-- Nagata descends along a separable extension of fraction fields. -/
theorem nagata_goes_down
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hB : IsNagataRing B) (hsep : Algebra.IsSeparable K L) :
    IsNagataRing A := by
  sorry

/-! ## Finite extension of a congruence -/

/-- A finite injective ring extension, with the module-finiteness condition
expressed using the canonical algebra induced by its ring homomorphism. -/
structure FiniteRingExtension (R S : Type*) [CommRing R] [CommRing S] where
  hom : R →+* S
  injective : Function.Injective hom
  finite : letI := hom.toAlgebra; Module.Finite R S

/-- A commutative square of ring homomorphisms. -/
structure RingHomSquare
    {X₁ Y₁ X₂ Y₂ : Type*} [CommRing X₁] [CommRing Y₁]
    [CommRing X₂] [CommRing Y₂]
    (f : X₁ →+* Y₁) (g : X₂ →+* Y₂)
    (hX : X₁ →+* X₂) (hY : Y₁ →+* Y₂) : Prop where
  commutes : g.comp hX = hY.comp f

/-- The finite extension and quotient isomorphism produced by the source's
construction lemma.  The two quotient maps and the final square make the
compatibility with the input congruence explicit. -/
structure ConstructExtensionWitness
    {A' A B' B : Type*} [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    (I : FiniteRingExtension A' A) (f : A') (g : B') (n : ℕ)
    (φ' : A' ⧸ Ideal.span {f ^ n} ≃+* B' ⧸ Ideal.span {g ^ n}) where
  extension : FiniteRingExtension B' B
  quotientEquiv :
    A ⧸ Ideal.span {(I.hom f) ^ n} ≃+*
      B ⧸ Ideal.span {(extension.hom g) ^ n}
  mapA : A' ⧸ Ideal.span {f ^ n} →+* A ⧸ Ideal.span {(I.hom f) ^ n}
  mapB : B' ⧸ Ideal.span {g ^ n} →+* B ⧸ Ideal.span {(extension.hom g) ^ n}
  mapA_mk : ∀ x : A', mapA (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (I.hom x)
  mapB_mk : ∀ x : B', mapB (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (extension.hom x)
  commutes : quotientEquiv.toRingHom.comp mapA = mapB.comp φ'.toRingHom

/-- The congruence-square data used by the functoriality remark. -/
structure FunctorialConstructExtensionWitness
    {A'₁ A₁ A'₂ A₂ B'₁ B₁ B'₂ B₂ : Type*}
    [CommRing A'₁] [CommRing A₁] [CommRing A'₂] [CommRing A₂]
    [CommRing B'₁] [CommRing B₁] [CommRing B'₂] [CommRing B₂]
    (I₁ : FiniteRingExtension A'₁ A₁)
    (I₂ : FiniteRingExtension A'₂ A₂)
    (f : A'₁) (f₂ : A'₂) (g : B'₁) (n : ℕ) (h : B'₁ →+* B'₂) where
  extension₁ : FiniteRingExtension B'₁ B₁
  extension₂ : FiniteRingExtension B'₂ B₂
  quotientEquiv₁ :
    A₁ ⧸ Ideal.span {(I₁.hom f) ^ n} ≃+*
      B₁ ⧸ Ideal.span {(extension₁.hom g) ^ n}
  quotientEquiv₂ :
    A₂ ⧸ Ideal.span {(I₂.hom f₂) ^ n} ≃+*
      B₂ ⧸ Ideal.span {(extension₂.hom (h g)) ^ n}
  mapB : B₁ →+* B₂
  mapB_commutes : mapB.comp extension₁.hom = extension₂.hom.comp h
  mapAQuotient :
    A₁ ⧸ Ideal.span {(I₁.hom f) ^ n} →+*
      A₂ ⧸ Ideal.span {(I₂.hom f₂) ^ n}
  mapBQuotient :
    B₁ ⧸ Ideal.span {(extension₁.hom g) ^ n} →+*
      B₂ ⧸ Ideal.span {(extension₂.hom (h g)) ^ n}
  quotient_commutes :
    quotientEquiv₂.toRingHom.comp mapAQuotient =
      mapBQuotient.comp quotientEquiv₁.toRingHom

/-- The finite congruence-extension lemma. -/
theorem construct_extension
    {A' A : Type*} [CommRing A'] [CommRing A]
    (I : FiniteRingExtension A' A) (f : A') (hf : IsRegular f)
    (hlocal : Nonempty (Localization.Away f ≃+* Localization.Away (I.hom f))) :
    ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (n : ℕ), n₀ ≤ n →
        ∀ (B' : Type*) [CommRing B'] (g : B') (hg : IsRegular g)
          (φ' : A' ⧸ Ideal.span {f ^ n} ≃+* B' ⧸ Ideal.span {g ^ n}),
          φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g →
          ∃ (B : Type*) (hB : CommRing B),
            letI := hB
            Nonempty (ConstructExtensionWitness (B := B) I f g n φ') := by
  sorry

/-- The functoriality assertion for `construct_extension`, packaged as a
ring-hom square at the level of the resulting finite extensions and their
special fibres. -/
theorem construct_extension_functorial
    {A'₁ A₁ A'₂ A₂ B'₁ B'₂ : Type*}
    [CommRing A'₁] [CommRing A₁] [CommRing A'₂] [CommRing A₂]
    [CommRing B'₁] [CommRing B'₂]
    (I₁ : FiniteRingExtension A'₁ A₁)
    (I₂ : FiniteRingExtension A'₂ A₂)
    (u : A'₁ →+* A'₂) (v : A₁ →+* A₂)
    (hI : v.comp I₁.hom = I₂.hom.comp u)
    (f : A'₁) (f₂ : A'₂) (hf : IsRegular f) (hf₂ : IsRegular f₂)
    (hlocal₁ : Nonempty
      (Localization.Away f ≃+* Localization.Away (I₁.hom f)))
    (hlocal₂ : Nonempty
      (Localization.Away f₂ ≃+* Localization.Away (I₂.hom f₂)))
    (hu : u f = f₂) (hv : v (I₁.hom f) = I₂.hom f₂)
    (n₀₁ n₀₂ n : ℕ) (hn : max n₀₁ n₀₂ ≤ n)
    (B'₂map : B'₁ →+* B'₂) (g : B'₁)
    (hg₁ : IsRegular g) (hg₂ : IsRegular (B'₂map g))
    (φ'₁ : A'₁ ⧸ Ideal.span {f ^ n} ≃+* B'₁ ⧸ Ideal.span {g ^ n})
    (φ'₂ : A'₂ ⧸ Ideal.span {f₂ ^ n} ≃+* B'₂ ⧸ Ideal.span {(B'₂map g) ^ n})
    (mapA'Quotient :
      A'₁ ⧸ Ideal.span {f ^ n} →+* A'₂ ⧸ Ideal.span {f₂ ^ n})
    (mapB'Quotient :
      B'₁ ⧸ Ideal.span {g ^ n} →+* B'₂ ⧸ Ideal.span {(B'₂map g) ^ n})
    (hφSquare : RingHomSquare φ'₁.toRingHom φ'₂.toRingHom
      mapA'Quotient mapB'Quotient)
    (hφ₁ : φ'₁ (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hφ₂ : φ'₂ (Ideal.Quotient.mk _ f₂) = Ideal.Quotient.mk _ (B'₂map g)) :
    ∃ (B₁ : Type*) (hB₁ : CommRing B₁) (B₂ : Type*) (hB₂ : CommRing B₂),
      letI := hB₁
      letI := hB₂
      Nonempty (FunctorialConstructExtensionWitness
        (B₁ := B₁) (B₂ := B₂) I₁ I₂ f f₂ g n B'₂map) := by
  sorry

/-! ## Removing a degree-p purely inseparable step -/

theorem approximate_solution
    {A B K L K₁ K₂ : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K₁] [Field K₂] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (p : ℕ) (hp : Nat.Prime p)
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hchar : CharP K p) (hsep : Algebra.IsSeparable K L)
    (hB : IsNagataRing B) [FiniteDimensional K K₁]
    (S₂ : FiniteSolution (K₁ := K₂) E F)
    (hS₂ : IsSolution S₂) [FiniteDimensional K₁ K₂]
    (hPure : IsPurelyInseparable K₁ K₂)
    (hdegree : Module.finrank K₁ K₂ = p) :
    ∃ (K₃ : Type*) (hK₃ : Field K₃) (hK₁K₃ : Algebra K₁ K₃)
      (hKK₃ : Algebra K K₃)
      (hfinite : letI := hK₁K₃; FiniteDimensional K₁ K₃),
      letI := hK₃
      letI := hK₁K₃
      letI := hKK₃
      letI := hfinite
      ∃ S₃ : FiniteSolution (K₁ := K₃) E F,
        IsSolution S₃ ∧ Algebra.IsSeparable K₁ K₃ := by
  sorry

/-- A finite purely inseparable degree-one step has been removed in the
source's induction on inseparable degree. -/
theorem exists_separable_solution
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hsep : Algebra.IsSeparable K L) (hB : IsNagataRing B)
    (hsolution : HasFiniteSolution E F) :
    HasFiniteSeparableSolution E F := by
  sorry

/-! ## Arbitrary algebraic base extensions -/

/-- The residue-field part of the conclusion of the large-extension lemma:
the induced field maps are essentially of finite type. -/
def ResidueFieldExtensionsEssFiniteType
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    RingHom.EssFiniteType
      (Ideal.ResidueField.map (q.asIdeal.comap f) q.asIdeal f rfl)

/-- The integral closure of the upper DVR remains Noetherian after an
algebraic base extension, with the source and residue-field conclusions. -/
theorem big_extension_is_ok
    {A B K L K' : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Field K'] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K'] [Algebra A K'] [Algebra.IsAlgebraic K K']
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hfiniteType : E.hom.EssFiniteType)
    (hA' : IsNoetherianRing (integralClosureIn A K'))
    (hL' : CommRing (reducedTensorProduct K L K'))
    (hBL' : letI := hL'; Algebra B (reducedTensorProduct K L K')) :
    letI := hL'
    letI : Algebra B (reducedTensorProduct K L K') := hBL'
    let L' := reducedTensorProduct K L K'
    let B' := integralClosureIn B L'
    ∃ hA'B' : Algebra (integralClosureIn A K') B',
      letI := hA'B'
      IsNoetherianRing B' ∧
        Function.Surjective
          (PrimeSpectrum.comap (algebraMap (integralClosureIn A K') B')) ∧
        ResidueFieldExtensionsEssFiniteType
          (algebraMap (integralClosureIn A K') B') := by
  sorry

/-! ## The two Epp-type conclusions -/

/-- Essential finite type over the base DVR gives a finite solution. -/
theorem epp_essentially_finite_type
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hfiniteType : E.hom.EssFiniteType) :
    HasFiniteSolution E F := by
  sorry

/-- Under the source's Nagata and separability hypotheses, the solution can
be chosen separable. -/
theorem epp_essentially_finite_type_separable
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (E : DVRMap A B) (F : FractionFieldExtension (K := K) (L := L) E)
    (hfiniteType : E.hom.EssFiniteType)
    (hAorB : IsNagataRing A ∨ IsNagataRing B)
    (hsep : Algebra.IsSeparable K L) :
    HasFiniteSeparableSolution E F := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit117
