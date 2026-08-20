import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Commutative Algebra, Chapter 148: Formally unramified maps

The formally unramified predicate is Mathlib's canonical
`Algebra.FormallyUnramified` class.  The declarations below expose the
square-zero lifting, base-change, localization, local, and filtered-colimit
statements from the source section.
-/

namespace Formalization.Books.Algebra.Unit148

open scoped TensorProduct

noncomputable section

universe u v w x

/-! ## The lifting definition and the differential criterion -/

/-- The source's square-zero lifting definition of formal unramifiedness. -/
theorem formallyUnramified_iff_lifting
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ↔
      ∀ {A : Type max u v} [CommRing A] [Algebra R A]
        (I : Ideal A) (_hI : I ^ 2 = ⊥),
        Function.Injective
          ((Ideal.Quotient.mkₐ R I).comp :
            (S →ₐ[R] A) → S →ₐ[R] A ⧸ I) := by
  simpa using
    (Algebra.FormallyUnramified.iff_comp_injective_of_small.{max u v} (R := R) (A := S))

/-- Formal unramifiedness is stable under arbitrary base change. -/
theorem formallyUnramified_baseChange
    {R : Type v} {S : Type u} {R' : Type w} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (h : Algebra.FormallyUnramified R S) :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.FormallyUnramified R' (R' ⊗[R] S) := by
  let _ : Algebra.FormallyUnramified R S := h
  infer_instance

/-- Formal unramifiedness is equivalent to vanishing Kähler differentials. -/
theorem formallyUnramified_iff_differentials
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyUnramified R S ↔
      Subsingleton (KaehlerDifferential R S) :=
  Algebra.formallyUnramified_iff R S

/-! ## Local and localized forms -/

/-- The three local characterizations of a formally unramified map. -/
theorem formallyUnramified_iff_local
    {R : Type v} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [ Algebra.FormallyUnramified R S,
        ∀ q : PrimeSpectrum S, Algebra.IsUnramifiedAt R q.asIdeal,
        ∀ q : PrimeSpectrum S,
          letI : Algebra
              (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
              (Localization.AtPrime q.asIdeal) :=
            (Localization.localRingHom _ _ _ rfl).toAlgebra
          Algebra.FormallyUnramified
            (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
            (Localization.AtPrime q.asIdeal) ] := by
  tfae_have 1 ↔ 2 := by
    exact Algebra.formallyUnramified_iff_forall
  tfae_have 2 → 3 := by
    intro h q
    let _ : Algebra.IsUnramifiedAt R q.asIdeal := h q
    infer_instance
  tfae_have 3 → 2 := by
    intro h q
    change Algebra.FormallyUnramified R (Localization.AtPrime q.asIdeal)
    let _ : Algebra
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
        (Localization.AtPrime q.asIdeal) :=
      (Localization.localRingHom _ _ _ rfl).toAlgebra
    let _ : Algebra.FormallyUnramified
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
        (Localization.AtPrime q.asIdeal) := h q
    let _ : Algebra.FormallyUnramified R
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R S))) :=
      Algebra.FormallyUnramified.of_isLocalization
        (q.asIdeal.comap (algebraMap R S)).primeCompl
    exact (Algebra.FormallyUnramified.comp R
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
      (Localization.AtPrime q.asIdeal))
  tfae_finish

/-- Every canonical localization map is formally unramified. -/
theorem formallyUnramified_localization :
    RingHom.HoldsForLocalization RingHom.FormallyUnramified :=
  RingHom.FormallyUnramified.holdsForLocalization

/-- Formal unramifiedness is preserved by the canonical map between arbitrary
source and target localizations. -/
theorem formallyUnramified_localize_source_and_target
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {M : Submonoid A} {T : Submonoid B}
    [Algebra A A'] [IsLocalization M A']
    [Algebra B B'] [IsLocalization T B']
    {f : A →+* B} (hM : M ≤ Submonoid.comap f T)
    (hf : RingHom.FormallyUnramified f) :
    RingHom.FormallyUnramified
      (IsLocalization.map (S := A') B' f hM) := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra A B' := ((algebraMap B B').comp f).toAlgebra
  let _ : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Algebra.FormallyUnramified A B := by
    simpa [RingHom.FormallyUnramified] using hf
  let _ : Algebra.FormallyUnramified B B' :=
    Algebra.FormallyUnramified.of_isLocalization T
  let _ : Algebra.FormallyUnramified A B' :=
    Algebra.FormallyUnramified.comp A B B'
  let _ : Algebra A' B' := (IsLocalization.map (S := A') B' f hM).toAlgebra
  let _ : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change ((algebraMap B B').comp f) r =
        (IsLocalization.map B' f hM) (algebraMap A A' r)
      simp)
  change Algebra.FormallyUnramified A' B'
  exact Algebra.FormallyUnramified.localization_base (M := M)

/-! ## Directed colimits -/

private theorem formallyUnramified_directedColimit_aux
    {R S I : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [P : Preorder I]
    (diagram : Formalization.Books.Algebra.Unit127.AlgebraSystem R I)
    (cocone : CategoryTheory.Limits.Cocone diagram)
    (isColimit : CategoryTheory.Limits.IsColimit cocone)
    (targetIso : cocone.pt ≅
      Formalization.Books.Algebra.Unit127.underRingHom (algebraMap R S))
    (h : ∀ i, RingHom.FormallyUnramified (diagram.obj i).hom.hom) :
    Algebra.FormallyUnramified R S := by
  rw [formallyUnramified_iff_lifting]
  intro A _ _ I hI φ ψ hφψ
  let φbar : Formalization.Books.Algebra.Unit127.underRingHom
      (algebraMap R S) ⟶
      Formalization.Books.Algebra.Unit127.underRingHom (algebraMap R A) :=
    CategoryTheory.Under.homMk (CommRingCat.ofHom φ.toRingHom) (by
      ext r
      exact φ.commutes' r)
  let ψbar : Formalization.Books.Algebra.Unit127.underRingHom
      (algebraMap R S) ⟶
      Formalization.Books.Algebra.Unit127.underRingHom (algebraMap R A) :=
    CategoryTheory.Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by
      ext r
      exact ψ.commutes' r)
  let hCφ := CategoryTheory.CategoryStruct.comp targetIso.hom φbar
  let hCψ := CategoryTheory.CategoryStruct.comp targetIso.hom ψbar
  have hC : hCφ = hCψ := by
    apply isColimit.hom_ext
    intro i
    let _ : Algebra R (diagram.obj i).right :=
      (diagram.obj i).hom.hom.toAlgebra
    let stageToTarget : (diagram.obj i).right →ₐ[R] S := by
      let stageRingHom :=
        (CategoryTheory.CategoryStruct.comp (cocone.ι.app i) targetIso.hom).right.hom
      refine { toRingHom := stageRingHom, commutes' := ?_ }
      intro r
      have hw :
          stageRingHom.comp (diagram.obj i).hom.hom =
          algebraMap R S := by
        have hw0 := congrArg (fun q => q.hom)
          (CategoryTheory.Under.w (CategoryTheory.CategoryStruct.comp
            (cocone.ι.app i) targetIso.hom))
        change stageRingHom.comp (diagram.obj i).hom.hom =
          (Formalization.Books.Algebra.Unit127.underRingHom
            (algebraMap R S)).hom.hom at hw0
        change stageRingHom.comp (diagram.obj i).hom.hom =
          algebraMap R S at hw0
        exact hw0
      exact congrArg (fun g => g r) hw
    let φi := φ.comp stageToTarget
    let ψi := ψ.comp stageToTarget
    let _ : Algebra.FormallyUnramified R (diagram.obj i).right := by
      simpa [RingHom.FormallyUnramified] using h i
    have huniq := (formallyUnramified_iff_lifting
      (R := R) (S := (diagram.obj i).right)).mp
      inferInstance I hI
    have hqi : (Ideal.Quotient.mkₐ R I).comp φi =
        (Ideal.Quotient.mkₐ R I).comp ψi := by
      apply AlgHom.ext
      intro y
      exact congrArg (fun g => g (stageToTarget y)) hφψ
    have hφiψi : φi = ψi := huniq hqi
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change φi.toRingHom = ψi.toRingHom
    exact congrArg AlgHom.toRingHom hφiψi
  have hcancel := congrArg
    (fun g => CategoryTheory.CategoryStruct.comp targetIso.inv g) hC
  have hcancel' : φbar = ψbar := by
    simpa [hCφ, hCψ, CategoryTheory.Category.assoc] using hcancel
  have hring' : φ.toRingHom = ψ.toRingHom :=
    congrArg (fun g => g.right.hom) hcancel'
  apply AlgHom.ext
  intro y
  exact congrArg (fun g => g y) hring'

/-- A directed colimit of formally unramified algebras is formally unramified. -/
theorem formallyUnramified_directedColimit
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit
      (algebraMap R S))
    (h : ∀ i,
      letI : Preorder D.index := D.indexPreorder
      RingHom.FormallyUnramified (D.diagram.obj i).hom.hom) :
    Algebra.FormallyUnramified R S := by
  refine @formallyUnramified_directedColimit_aux R S D.index _ _ _ D.indexPreorder
    D.diagram D.cocone D.isColimit D.targetIso ?_
  intro i
  simpa using h i

end

end Formalization.Books.Algebra.Unit148
