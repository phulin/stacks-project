import Formalization.Books.Homology.Unit20.DifferentialObjects
import Formalization.Books.Homology.Unit21.ExactCouples
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Homological Algebra, Chapter 22: Spectral sequences: differential objects

This file gives the source-facing interface for the differential-object
construction.  The unshifted construction and its categorical subobject
calculus are reused from Chapter 20.  Chapter 21 supplies the exact-couple
and translated-spectral-sequence interfaces used by the shifted variant.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit22

/-! ## 22.1 Differential objects -/

/-! ### Differential objects, morphisms, and homology -/

/-
The source's unshifted objects have no ambient shift functor.  The preceding
chapter therefore records them as `PlainDifferentialObject`; these aliases
reuse that canonical project representation rather than introducing a second
category in this chapter.
-/

/-- A differential object `(A, d)` with `d ≫ d = 0`. -/
abbrev DifferentialObject (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  Formalization.Books.Homology.Unit20.PlainDifferentialObject C

/-- A morphism of differential objects, commuting with the differentials. -/
abbrev DifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (A B : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialObjectHom A B

/-- The category of unshifted differential objects is abelian. -/
theorem differentialObject_category_abelian {C : Type u} [Category.{v} C]
    [Abelian C] : Nonempty (Abelian (DifferentialObject C)) := by
  exact Formalization.Books.Homology.Unit20.plainDifferentialObject_abelian

/-- `H(A,d) = Ker(d) / Im(d)`, using the canonical categorical homology object. -/
abbrev differentialObjectHomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : DifferentialObject C) : C :=
  Formalization.Books.Homology.Unit20.plainDifferentialHomology A

/-! ### Short exact sequences and the long homology sequence -/

/-- A short exact sequence of differential objects. -/
abbrev DifferentialObjectShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialShortExact A B D

/-- The bi-infinite homology sequence attached to a short exact sequence.

The index is chosen so that the terms repeat as
`H(C), H(A), H(B), H(C), ...`, matching the displayed source sequence.
-/
abbrev DifferentialObjectLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (X : ℤ → C) :=
  Formalization.Books.Homology.Unit20.LongExactSequence X

abbrev differentialObjectHomologyLongTerm {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : DifferentialObject C) (n : ℤ) : C :=
  Formalization.Books.Homology.Unit20.differentialHomologyLongTerm A B D n

theorem differentialObjectShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : DifferentialObject C}
    (S : DifferentialObjectShortExact A B D) :
    Nonempty (DifferentialObjectLongExactSequence
      (differentialObjectHomologyLongTerm A B D)) := by
  exact Formalization.Books.Homology.Unit20.plainDifferentialShortExact_homology_long_exact S

/-! ### The injective self-map example -/

/-- An injective endomorphism `α` of a differential object. -/
abbrev DifferentialObjectInjectiveSelfMap {C : Type u} [Category.{v} C]
    [Abelian C] (A : DifferentialObject C) :=
  Formalization.Books.Homology.Unit20.PlainDifferentialInjectiveEndomorphism A

/-- Data for the induced differential on the quotient `A / α A`. -/
abbrev DifferentialObjectQuotientMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :=
  Formalization.Books.Homology.Unit20.QuotientDifferentialMapData α

abbrev differentialObjectQuotientMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectQuotientMapData α :=
  Formalization.Books.Homology.Unit20.quotientDifferentialMapData α

abbrev differentialObjectQuotientMap {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    cokernel α.hom.hom ⟶ cokernel α.hom.hom :=
  Formalization.Books.Homology.Unit20.quotientDifferentialMap α

/-- The quotient differential object `(A / α A, d)`. -/
abbrev differentialObjectQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : DifferentialObject C :=
  Formalization.Books.Homology.Unit20.quotientDifferentialObject α

/-- The short exact sequence `0 → (A,d) → (A,d) → (A/αA,d) → 0`. -/
abbrev differentialObjectSelfMapShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectShortExact A A (differentialObjectQuotient α) :=
  Formalization.Books.Homology.Unit20.differentialSelfMapShortExact α

/-! ### The associated exact couple and its pages -/

abbrev DifferentialObjectSelfMapExactCouple {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :=
  Formalization.Books.Homology.Unit21.ExactCouple C
    (differentialObjectHomology A) (differentialObjectHomology (differentialObjectQuotient α))

theorem differentialObjectSelfMap_exact_couple_exists
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (DifferentialObjectSelfMapExactCouple α) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_exactCouple_exists α

noncomputable def differentialObjectSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectSelfMapExactCouple α :=
  Formalization.Books.Homology.Unit20.differentialSelfMapExactCouple α

/-- The map `\overline{α}` in the self-map exact couple. -/
abbrev differentialObjectSelfMapBarAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology A ⟶ differentialObjectHomology A :=
  (differentialObjectSelfMapExactCouple α).alpha

/-- The boundary map `f : H(A/αA) → H(A)`. -/
abbrev differentialObjectSelfMapBoundary
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology (differentialObjectQuotient α) ⟶
      differentialObjectHomology A :=
  (differentialObjectSelfMapExactCouple α).f

/-- The quotient map `g : H(A) → H(A/αA)`. -/
abbrev differentialObjectSelfMapQuotientHomologyMap
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectHomology A ⟶
      differentialObjectHomology (differentialObjectQuotient α) :=
  (differentialObjectSelfMapExactCouple α).g

abbrev PlainSpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (r₀ : ℤ := 1) :=
  Formalization.Books.Homology.Unit20.PlainSpectralSequence.{v, u, 0} C r₀

abbrev pageObject {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : C :=
  Formalization.Books.Homology.Unit20.plainPageObject E r hr

abbrev pageDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : pageObject E r hr ⟶ pageObject E r hr :=
  Formalization.Books.Homology.Unit20.plainPageDifferential E r hr

/-- The spectral sequence obtained from the self-map exact couple. -/
noncomputable def differentialObjectSelfMapAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : PlainSpectralSequence C 1 :=
  Formalization.Books.Homology.Unit20.differentialSelfMapAssociatedSpectralSequence α

theorem differentialObjectSelfMap_E1
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (pageObject (differentialObjectSelfMapAssociatedSpectralSequence α) 1 ≅
      differentialObjectHomology (differentialObjectQuotient α)) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_E1 α

/-- The separately numbered zeroth page `E₀ = A / α A`. -/
abbrev differentialObjectSelfMapE₀ {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : C :=
  (differentialObjectQuotient α).carrier

/-- The zeroth differential `d₀ = d` on `E₀`. -/
abbrev differentialObjectSelfMapD₀ {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectSelfMapE₀ α ⟶ differentialObjectSelfMapE₀ α :=
  (differentialObjectQuotient α).d

/-
The exact-couple API starts at page one.  The source's convention starts the
same sequence at page zero, so the following data records the page-zero
identification and the compatibility of `d₀` with the canonical page
differential instead of silently identifying unrelated chosen cokernels.
-/
structure DifferentialObjectSelfMapSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) where
  sequence : PlainSpectralSequence C 0
  pageZeroIso : pageObject sequence 0 ≅ differentialObjectSelfMapE₀ α
  pageZeroDifferential_compatibility :
    pageDifferential sequence 0 ≫ pageZeroIso.hom =
      pageZeroIso.hom ≫ differentialObjectSelfMapD₀ α
  pageOneIso : Nonempty (pageObject sequence 1 ≅
    differentialObjectHomology (differentialObjectQuotient α))

private noncomputable def differentialObjectSelfMapPageZeroHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    (Formalization.Books.Homology.Unit20.plainSpectralSequencePage
      (differentialObjectQuotient α).carrier
      (differentialObjectQuotient α).d
      (differentialObjectQuotient α).d_squared).homology PUnit.unit ≅
      differentialObjectHomology (differentialObjectQuotient α) :=
  by
    let d := (differentialObjectQuotient α).d
    have hd : d ≫ d = 0 := (differentialObjectQuotient α).d_squared
    let P₀ : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
      Formalization.Books.Homology.Unit20.plainSpectralSequencePage
      (differentialObjectQuotient α).carrier d hd
    let S : ShortComplex C := P₀.sc' PUnit.unit PUnit.unit PUnit.unit
    let k₀ : (differentialObjectQuotient α).carrier ⟶ kernel d :=
      kernel.lift d d hd
    let k : Abelian.image d ⟶ kernel d :=
      kernel.lift d (Abelian.image.ι d) (by
        apply (cancel_epi (Abelian.factorThruImage d)).1
        simp only [← Category.assoc, Abelian.image.fac, hd, comp_zero])
    have hk : k₀ = Abelian.factorThruImage d ≫ k := by
      apply (cancel_mono (kernel.ι d)).1
      simp [k, k₀, Category.assoc]
    let π : kernel d ⟶ cokernel k :=
      cokernel.π k
    have wπ : k₀ ≫ π = 0 := by
      rw [hk]
      rw [Category.assoc, cokernel.condition, comp_zero]
    have hπ : IsColimit (CokernelCofork.ofπ π wπ) :=
      CokernelCofork.IsColimit.ofπ _ _
        (fun x hx => cokernel.desc k x (by
          apply (cancel_epi (Abelian.factorThruImage d)).1
          simp only [← Category.assoc, ← hk, hx, comp_zero]))
        (fun x hx => by exact cokernel.π_desc _ _ _)
        (fun x hx b hb => by
          apply (cancel_epi π).1
          rw [hb, cokernel.π_desc])
    let hData : S.LeftHomologyData :=
      { K := kernel d
        H := differentialObjectHomology (differentialObjectQuotient α)
        i := kernel.ι d
        π := π
        wi := by
          change kernel.ι d ≫ d = 0
          exact kernel.condition d
        hi := kernelIsKernel d
        wπ := wπ
        hπ := hπ }
    exact
      (HomologicalComplex.homologyIsoSc'
        (Formalization.Books.Homology.Unit20.plainSpectralSequencePage
          (differentialObjectQuotient α).carrier d hd)
        PUnit.unit PUnit.unit PUnit.unit rfl rfl) ≪≫ hData.homologyIso

theorem differentialObjectSelfMapSpectralSequenceData_exists
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (DifferentialObjectSelfMapSpectralSequenceData α) := by
  let Q := differentialObjectQuotient α
  let E := differentialObjectSelfMapAssociatedSpectralSequence α
  let P₀ := Formalization.Books.Homology.Unit20.plainSpectralSequencePage
    Q.carrier Q.d Q.d_squared
  have hE₁ : Nonempty (pageObject E 1 ≅ differentialObjectHomology Q) :=
    differentialObjectSelfMap_E1 α
  let S : PlainSpectralSequence C 0 := by
    refine { page := ?_, iso := ?_ }
    · intro r hr
      exact if h : r = 0 then P₀ else E.page r (by omega)
    · intro r r' pq hrr' hr
      by_cases h : r = 0
      · subst r
        have hr' : r' = 1 := by omega
        subst r'
        cases pq
        simpa [P₀] using
          (differentialObjectSelfMapPageZeroHomologyIso α ≪≫
            (Classical.choice hE₁).symm)
      · have hr₁ : (1 : ℤ) ≤ r := by omega
        have hr'₀ : r' ≠ 0 := by omega
        split
        · rename_i hzero
          exact (h hzero).elim
        · convert E.iso r r' pq hrr' hr₁ using 1
  refine ⟨{
    sequence := S
    pageZeroIso := Iso.refl _
    pageZeroDifferential_compatibility := ?_
    pageOneIso := ?_
  }⟩
  · change P₀.d PUnit.unit PUnit.unit ≫ 𝟙 _ = 𝟙 _ ≫ Q.d
    simp only [Category.comp_id, Category.id_comp]
    change Q.d = Q.d
    rfl
  · rcases hE₁ with ⟨e⟩
    refine ⟨?_⟩
    change (if h : (1 : ℤ) = 0 then P₀ else E.page 1 (by omega)).X PUnit.unit ≅ _
    split
    · rename_i hzero
      omega
    · convert e using 1

noncomputable def differentialObjectSelfMapSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    DifferentialObjectSelfMapSpectralSequenceData α :=
  Classical.choice (differentialObjectSelfMapSpectralSequenceData_exists α)

noncomputable def differentialObjectSelfMapSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : PlainSpectralSequence C 0 :=
  (differentialObjectSelfMapSpectralSequenceData α).sequence

theorem differentialObjectSelfMap_page_data_is_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    Nonempty (PlainSpectralSequence C 0) := by
  exact Formalization.Books.Homology.Unit20.differentialSelfMap_starting_at_zero_exists α

/-! ### The `Bᵣ` and `Zᵣ` subobjects -/

abbrev differentialObjectSelfMapAlphaPow {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : ℕ →
      (A.carrier ⟶ A.carrier) :=
  Formalization.Books.Homology.Unit20.selfMapAlphaPow α

abbrev differentialObjectSelfMapBoundaryPreimage {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapBoundaryPreimage α r

abbrev differentialObjectSelfMapCyclePreimage {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapCyclePreimage α r

theorem differentialObjectSelfMap_boundary_preimage_le_cycle_preimage
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundaryPreimage α r ≤
      differentialObjectSelfMapCyclePreimage α r := by
  exact Formalization.Books.Homology.Unit20.selfMap_boundary_preimage_le_cycle_preimage α r

abbrev differentialObjectSelfMapBoundaryPlus {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  differentialObjectSelfMapBoundaryPreimage α r ⊔
    Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective

abbrev differentialObjectSelfMapCyclePlus {C : Type u} [Category.{v} C]
    [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject A.carrier :=
  differentialObjectSelfMapCyclePreimage α r ⊔
    Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective

theorem differentialObjectSelfMap_boundary_plus_le_cycle_plus
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundaryPlus α r ≤
      differentialObjectSelfMapCyclePlus α r := by
  exact sup_le_sup
    (differentialObjectSelfMap_boundary_preimage_le_cycle_preimage α r) le_rfl

abbrev differentialObjectSelfMapQuotientImageSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {X Q : C}
    (π : X ⟶ Q) (B : Subobject X) : Subobject Q :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject π B

abbrev differentialObjectSelfMapBoundarySubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject (differentialObjectSelfMapE₀ α) :=
  Formalization.Books.Homology.Unit20.selfMapBoundarySubobject α r

abbrev differentialObjectSelfMapCycleSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Subobject (differentialObjectSelfMapE₀ α) :=
  Formalization.Books.Homology.Unit20.selfMapCycleSubobject α r

theorem differentialObjectSelfMap_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapBoundarySubobject α r ≤
      differentialObjectSelfMapCycleSubobject α r := by
  exact Formalization.Books.Homology.Unit20.selfMap_boundary_le_cycle α r

private theorem differentialObjectSelfMap_exists_image_eq
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    (Subobject.«exists» f).obj (⊤ : Subobject X) =
      imageSubobject f := by
  let J := imageSubobject f
  let I := (Subobject.«exists» f).obj (⊤ : Subobject X)
  have hJ : J.Factors f := by
    simpa [J] using (imageSubobject_factors_comp_self (f := f) (𝟙 X))
  have hJtop : J.Factors ((⊤ : Subobject X).arrow ≫ f) :=
    Subobject.factors_of_factors_right (⊤ : Subobject X).arrow hJ
  have htop : (⊤ : Subobject X) ≤ (Subobject.pullback f).obj J := by
    let hpb := Subobject.isPullback f J
    refine Subobject.le_of_comm
      (hpb.lift (J.factorThru ((⊤ : Subobject X).arrow ≫ f) hJtop)
        (⊤ : Subobject X).arrow ?_) ?_
    · exact J.factorThru_arrow _ _
    · simp
  have hIJ : I ≤ J := by
    exact leOfHom (((Subobject.existsPullbackAdj f).homEquiv (⊤ : Subobject X) J).symm
      (homOfLE htop))
  let hunit : (⊤ : Subobject X) ⟶ (Subobject.pullback f).obj I :=
    (Subobject.existsPullbackAdj f).unit.app (⊤ : Subobject X)
  let hX : X ⟶ I :=
    (Subobject.underlyingIso (𝟙 X)).inv ≫
      Subobject.underlying.map hunit ≫ Subobject.pullbackπ f I
  have hJI : J ≤ I := by
    apply imageSubobject_le f hX
    dsimp [hX, I]
    rw [Category.assoc, Category.assoc, (Subobject.isPullback f I).w]
    rw [← Category.assoc (Subobject.underlying.map hunit)
      ((Subobject.pullback f).obj I).arrow f]
    rw [Subobject.underlying_arrow]
    rw [← Category.assoc (Subobject.underlyingIso (𝟙 X)).inv
      (⊤ : Subobject X).arrow f]
    rw [Subobject.underlyingIso_inv_top_arrow, Category.id_comp]
  apply le_antisymm
  · exact hIJ
  · exact hJI

private theorem differentialObjectSelfMap_image_d_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) :
    ∃ h : ((Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier) : C) ⟶
        (Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier),
      h ≫ ((Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier)).arrow =
        ((Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier)).arrow ≫ α.hom.hom := by
  rw [differentialObjectSelfMap_exists_image_eq A.d]
  let sq : Arrow.mk A.d ⟶ Arrow.mk A.d :=
    Arrow.homMk α.hom.hom α.hom.hom α.hom.comm.symm
  exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

private theorem differentialObjectSelfMap_boundary_preimage_monotone
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) (n : ℕ) :
    differentialObjectSelfMapBoundaryPreimage α (n + 1) ≤
      differentialObjectSelfMapBoundaryPreimage α (n + 2) := by
  let I := (Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier)
  let p := differentialObjectSelfMapAlphaPow α n
  let p' := differentialObjectSelfMapAlphaPow α (n + 1)
  obtain ⟨hI, hIarrow⟩ := differentialObjectSelfMap_image_d_map α
  have hcond :
      (Subobject.pullbackπ p I ≫ hI) ≫ I.arrow =
        ((Subobject.pullback p).obj I).arrow ≫ p' := by
    rw [Category.assoc, hIarrow]
    rw [← Category.assoc (Subobject.pullbackπ p I) I.arrow α.hom.hom]
    rw [(Subobject.isPullback p I).w]
    change (((Subobject.pullback p).obj I).arrow ≫ p) ≫ α.hom.hom =
      ((Subobject.pullback p).obj I).arrow ≫ (p ≫ α.hom.hom)
    simp only [Category.assoc]
  let l := (Subobject.isPullback p' I).lift
    (Subobject.pullbackπ p I ≫ hI) ((Subobject.pullback p).obj I).arrow hcond
  apply Subobject.le_of_comm l
  simp [l, p, p', differentialObjectSelfMapAlphaPow,
    Formalization.Books.Homology.Unit20.selfMapAlphaPow]

private theorem differentialObjectSelfMap_cycle_preimage_antitone
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) (n : ℕ) :
    differentialObjectSelfMapCyclePreimage α (n + 2) ≤
      differentialObjectSelfMapCyclePreimage α (n + 1) := by
  let p := differentialObjectSelfMapAlphaPow α (n + 1)
  let p' := differentialObjectSelfMapAlphaPow α (n + 2)
  have hcomm : α.hom.hom ≫ p = p ≫ α.hom.hom := by
    dsimp [p]
    induction n + 1 with
    | zero => simp [differentialObjectSelfMapAlphaPow,
        Formalization.Books.Homology.Unit20.selfMapAlphaPow]
    | succ k ih =>
        rw [differentialObjectSelfMapAlphaPow,
          Formalization.Books.Homology.Unit20.selfMapAlphaPow]
        rw [← Category.assoc, ih]
  have hpow :
      (Subobject.«exists» p').obj (⊤ : Subobject A.carrier) ≤
        (Subobject.«exists» p).obj (⊤ : Subobject A.carrier) := by
    rw [differentialObjectSelfMap_exists_image_eq p',
      differentialObjectSelfMap_exists_image_eq p]
    change imageSubobject (p ≫ α.hom.hom) ≤ imageSubobject p
    rw [← hcomm]
    exact imageSubobject_comp_le α.hom.hom p
  have hpull := (Subobject.pullback A.d).monotone hpow
  simpa [p, p', differentialObjectSelfMapCyclePreimage,
    Formalization.Books.Homology.Unit20.selfMapCyclePreimage,
    differentialObjectSelfMapAlphaPow,
    Formalization.Books.Homology.Unit20.selfMapAlphaPow] using hpull

private theorem differentialObjectSelfMap_quotient_image_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Q : C} (q : X ⟶ Q) {P R : Subobject X} (h : P ≤ R) :
    Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject q P ≤
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject q R := by
  let sq : Arrow.mk (P.arrow ≫ q) ⟶ Arrow.mk (R.arrow ≫ q) :=
    Arrow.homMk' (Subobject.ofLE P R h) (𝟙 Q) (by
      simp)
  let : Mono (Abelian.image.ι (P.arrow ≫ q)) := by
    dsimp [Abelian.image]
    infer_instance
  let : Mono (Abelian.image.ι (R.arrow ≫ q)) := by
    dsimp [Abelian.image]
    infer_instance
  let g := (Subobject.underlyingIso (Abelian.image.ι (P.arrow ≫ q))).hom ≫
    Abelian.im.map sq ≫
      (Subobject.underlyingIso (Abelian.image.ι (R.arrow ≫ q))).inv
  apply Subobject.le_of_comm g
  dsimp [g, sq]
  simp [Abelian.im]

def differentialObjectSelfMapB {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) :
    ℕ → Subobject (differentialObjectSelfMapE₀ α)
  | 0 => ⊥
  | n + 1 => differentialObjectSelfMapBoundarySubobject α (n + 1)

def differentialObjectSelfMapZ {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C} (α : DifferentialObjectInjectiveSelfMap A) :
    ℕ → Subobject (differentialObjectSelfMapE₀ α)
  | 0 => ⊤
  | n + 1 => differentialObjectSelfMapCycleSubobject α (n + 1)

theorem differentialObjectSelfMap_B_le_Z
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    differentialObjectSelfMapB α r ≤ differentialObjectSelfMapZ α r := by
  cases r with
  | zero => exact bot_le
  | succ n =>
    simpa [differentialObjectSelfMapB, differentialObjectSelfMapZ] using
      differentialObjectSelfMap_boundary_le_cycle α (n + 1)

theorem differentialObjectSelfMap_filtration
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) :
    differentialObjectSelfMapB α 0 = ⊥ ∧
      differentialObjectSelfMapZ α 0 = ⊤ ∧
      (∀ r, differentialObjectSelfMapB α r ≤ differentialObjectSelfMapB α (r + 1)) ∧
      (∀ r, differentialObjectSelfMapZ α (r + 1) ≤ differentialObjectSelfMapZ α r) ∧
      (∀ r, differentialObjectSelfMapB α r ≤ differentialObjectSelfMapZ α r) := by
  refine ⟨rfl, rfl, ?_, ?_, differentialObjectSelfMap_B_le_Z α⟩
  · intro r
    cases r with
    | zero => exact bot_le
    | succ n =>
        change Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
            (cokernel.π α.hom.hom)
            (differentialObjectSelfMapBoundaryPreimage α (n + 1)) ≤
          Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
            (cokernel.π α.hom.hom)
            (differentialObjectSelfMapBoundaryPreimage α (n + 2))
        exact differentialObjectSelfMap_quotient_image_mono
          (cokernel.π α.hom.hom)
          (differentialObjectSelfMap_boundary_preimage_monotone α n)
  · intro r
    cases r with
    | zero => exact le_top
    | succ n =>
        change Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
            (cokernel.π α.hom.hom)
            (differentialObjectSelfMapCyclePreimage α (n + 2)) ≤
          Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
            (cokernel.π α.hom.hom)
            (differentialObjectSelfMapCyclePreimage α (n + 1))
        exact differentialObjectSelfMap_quotient_image_mono
          (cokernel.π α.hom.hom)
          (differentialObjectSelfMap_cycle_preimage_antitone α n)

noncomputable def differentialObjectSelfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : C :=
  Formalization.Books.Homology.Unit20.selfMapPageComponent α r

noncomputable def differentialObjectSelfMapPageAsQuotient
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (differentialObjectSelfMapB α (r + 1))
    (differentialObjectSelfMapZ α (r + 1))
    (differentialObjectSelfMap_B_le_Z α (r + 1))

theorem differentialObjectSelfMap_page_quotient_description
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Nonempty (differentialObjectSelfMapPageComponent α (r + 1) ≅
      differentialObjectSelfMapPageAsQuotient α r) := by
  exact ⟨Iso.refl _⟩

private theorem differentialObjectSelfMap_cycle_plus_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    (differentialObjectSelfMapCycleSubobject α r).Factors
      ((differentialObjectSelfMapCyclePlus α r).arrow ≫ cokernel.π α.hom.hom) := by
  let P := differentialObjectSelfMapCyclePreimage α r
  let R := differentialObjectSelfMapCycleSubobject α r
  let S := Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective
  let Q := differentialObjectSelfMapCyclePlus α r
  let q : A.carrier ⟶ differentialObjectSelfMapE₀ α := cokernel.π α.hom.hom
  let : Mono α.hom.hom := α.injective
  have hP : R.Factors (P.arrow ≫ q) := by
    apply (Subobject.factors_iff R (P.arrow ≫ q)).mpr
    refine ⟨Abelian.factorThruImage (P.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι
        (P.arrow ≫ q))).inv, ?_⟩
    dsimp [R, differentialObjectSelfMapCycleSubobject,
      Formalization.Books.Homology.Unit20.selfMapCycleSubobject,
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
    change (Abelian.factorThruImage (P.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι (P.arrow ≫ q))).inv) ≫
      (Subobject.mk (Abelian.image.ι (P.arrow ≫ q))).arrow = P.arrow ≫ q
    rw [← Subobject.underlyingIso_hom_comp_eq_mk
      (Abelian.image.ι (P.arrow ≫ q))]
    simp [Category.assoc]
  have hSzero : S.arrow ≫ q = 0 := by
    dsimp [S, q, Formalization.Books.Homology.Unit20.selfMapAlphaSubobject]
    change (Subobject.mk α.hom.hom).arrow ≫ cokernel.π α.hom.hom = 0
    rw [← Subobject.underlyingIso_hom_comp_eq_mk α.hom.hom]
    rw [Category.assoc, cokernel.condition, comp_zero]
  have hS : R.Factors (S.arrow ≫ q) := by
    change R.Factors (S.arrow ≫ cokernel.π α.hom.hom)
    rw [hSzero]
    exact Subobject.factors_zero
  have hPpull : P ≤
      (Subobject.pullback q).obj R := by
    let hpb := Subobject.isPullback q R
    refine Subobject.le_of_comm
      (hpb.lift (R.factorThru (P.arrow ≫ q) hP) P.arrow ?_) ?_
    · exact R.factorThru_arrow _ _
    · simp
  have hSpull : S ≤
      (Subobject.pullback q).obj R := by
    let hpb := Subobject.isPullback q R
    refine Subobject.le_of_comm
      (hpb.lift 0 S.arrow (by rw [zero_comp, hSzero])) ?_
    · simp
  have hQpull : Q ≤
      (Subobject.pullback q).obj R := sup_le hPpull hSpull
  apply (Subobject.factors_iff R (Q.arrow ≫ q)).mpr
  refine ⟨(Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
      Subobject.pullbackπ q R) ≫
      eqToHom (Subobject.representative_coe R).symm, ?_⟩
  simp [Subobject.representative_coe, Subobject.representative_arrow]
  calc
    Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
        Subobject.pullbackπ q R ≫ R.arrow =
      Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
        ((Subobject.pullback q).obj R).arrow ≫ q := by
          rw [(Subobject.isPullback q R).w]
    _ = Q.arrow ≫ q := by
      rw [← Category.assoc, Subobject.ofLE_arrow]

private theorem differentialObjectSelfMap_boundary_plus_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    (differentialObjectSelfMapBoundarySubobject α r).Factors
      ((differentialObjectSelfMapBoundaryPlus α r).arrow ≫ cokernel.π α.hom.hom) := by
  let P := differentialObjectSelfMapBoundaryPreimage α r
  let R := differentialObjectSelfMapBoundarySubobject α r
  let S := Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective
  let Q := differentialObjectSelfMapBoundaryPlus α r
  let q : A.carrier ⟶ differentialObjectSelfMapE₀ α := cokernel.π α.hom.hom
  let : Mono α.hom.hom := α.injective
  have hP : R.Factors (P.arrow ≫ q) := by
    apply (Subobject.factors_iff R (P.arrow ≫ q)).mpr
    refine ⟨Abelian.factorThruImage (P.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι
        (P.arrow ≫ q))).inv, ?_⟩
    dsimp [R, differentialObjectSelfMapBoundarySubobject,
      Formalization.Books.Homology.Unit20.selfMapBoundarySubobject,
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
    change (Abelian.factorThruImage (P.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι (P.arrow ≫ q))).inv) ≫
      (Subobject.mk (Abelian.image.ι (P.arrow ≫ q))).arrow = P.arrow ≫ q
    rw [← Subobject.underlyingIso_hom_comp_eq_mk
      (Abelian.image.ι (P.arrow ≫ q))]
    simp [Category.assoc]
  have hSzero : S.arrow ≫ q = 0 := by
    dsimp [S, q, Formalization.Books.Homology.Unit20.selfMapAlphaSubobject]
    change (Subobject.mk α.hom.hom).arrow ≫ cokernel.π α.hom.hom = 0
    rw [← Subobject.underlyingIso_hom_comp_eq_mk α.hom.hom]
    rw [Category.assoc, cokernel.condition, comp_zero]
  have hS : R.Factors (S.arrow ≫ q) := by
    change R.Factors (S.arrow ≫ cokernel.π α.hom.hom)
    rw [hSzero]
    exact Subobject.factors_zero
  have hPpull : P ≤
      (Subobject.pullback q).obj R := by
    let hpb := Subobject.isPullback q R
    refine Subobject.le_of_comm
      (hpb.lift (R.factorThru (P.arrow ≫ q) hP) P.arrow ?_) ?_
    · exact R.factorThru_arrow _ _
    · simp
  have hSpull : S ≤
      (Subobject.pullback q).obj R := by
    let hpb := Subobject.isPullback q R
    refine Subobject.le_of_comm
      (hpb.lift 0 S.arrow (by rw [zero_comp, hSzero])) ?_
    · simp
  have hQpull : Q ≤
      (Subobject.pullback q).obj R := sup_le hPpull hSpull
  apply (Subobject.factors_iff R (Q.arrow ≫ q)).mpr
  refine ⟨(Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
      Subobject.pullbackπ q R) ≫
      eqToHom (Subobject.representative_coe R).symm, ?_⟩
  simp [Subobject.representative_coe, Subobject.representative_arrow]
  calc
    Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
        Subobject.pullbackπ q R ≫ R.arrow =
      Subobject.ofLE Q ((Subobject.pullback q).obj R) hQpull ≫
        ((Subobject.pullback q).obj R).arrow ≫ q := by
          rw [(Subobject.isPullback q R).w]
    _ = Q.arrow ≫ q := by
      rw [← Category.assoc, Subobject.ofLE_arrow]

abbrev differentialObjectSelfMapPageClassOfCycle
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ)
    {T : C} (z : T ⟶ (differentialObjectSelfMapCyclePlus α r : C)) :
    T ⟶ differentialObjectSelfMapPageComponent α r :=
  by
    let hfac := differentialObjectSelfMap_cycle_plus_factors α r
    exact Formalization.Books.Homology.Unit20.selfMapPageClassOfCycle α r
      (z ≫ (differentialObjectSelfMapCycleSubobject α r).factorThru
        ((differentialObjectSelfMapCyclePlus α r).arrow ≫ cokernel.π α.hom.hom) hfac)

/-- The categorical/test-object form of the rule defining `dᵣ` on the page. -/
abbrev DifferentialObjectSelfMapPageDifferentialRule
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :=
  Formalization.Books.Homology.Unit20.SelfMapPageDifferentialRule α r

theorem differentialObjectSelfMap_page_differential_rule
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) (_hr : 1 ≤ r) :
    Nonempty (DifferentialObjectSelfMapPageDifferentialRule α r) := by
  exact Formalization.Books.Homology.Unit20.selfMap_page_differential_rule_exists α r

/-
The two inclusions in the source warning are deliberately predicates, not
assumptions.  The only unconditional inclusion is the one proved above.
-/
abbrev differentialObjectSelfMapAlphaSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) : Subobject A.carrier :=
  Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective

abbrev differentialObjectSelfMapWarningBoundaryInclusion
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : Prop :=
  Formalization.Books.Homology.Unit20.selfMapWarningBoundaryInclusion α r

abbrev differentialObjectSelfMapWarningCycleInclusion
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) : Prop :=
  Formalization.Books.Homology.Unit20.selfMapWarningCycleInclusion α r

theorem differentialObjectSelfMap_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] {A : DifferentialObject C}
    (α : DifferentialObjectInjectiveSelfMap A) (r : ℕ) :
    Nonempty (differentialObjectSelfMapPageComponent α r ≅
      Formalization.Books.Homology.Unit20.subquotientObject
        (differentialObjectSelfMapBoundaryPlus α r)
        (differentialObjectSelfMapCyclePlus α r)
        (differentialObjectSelfMap_boundary_plus_le_cycle_plus α r)) := by
  by_cases hr : r = 0
  · subst r
    let E₀ := differentialObjectSelfMapE₀ α
    let : Mono α.hom.hom := α.injective
    let S : Subobject A.carrier := Subobject.mk α.hom.hom
    let T : Subobject A.carrier := ⊤
    let sIso := Subobject.underlyingIso α.hom.hom
    let tIso := Subobject.underlyingIso (𝟙 A.carrier)
    let iS : (S : C) ⟶ (T : C) := Subobject.ofLE S T le_top
    let qS := cokernel.π iS
    have hst : tIso.hom = T.arrow := by
      change (Subobject.underlyingIso (𝟙 A.carrier)).hom =
        (⊤ : Subobject A.carrier).arrow
      exact Subobject.underlyingIso_top_hom
    have hsi : sIso.inv ≫ S.arrow = α.hom.hom := by
      change (Subobject.underlyingIso α.hom.hom).inv ≫
        (Subobject.mk α.hom.hom).arrow = α.hom.hom
      exact Subobject.underlyingIso_arrow α.hom.hom
    have hsm : sIso.hom ≫ α.hom.hom = S.arrow := by
      change (Subobject.underlyingIso α.hom.hom).hom ≫ α.hom.hom =
        (Subobject.mk α.hom.hom).arrow
      rw [Subobject.underlyingIso_hom_comp_eq_mk]
    have hα : α.hom.hom ≫ tIso.inv = sIso.inv ≫ iS := by
      apply (cancel_mono tIso.hom).1
      calc
        (α.hom.hom ≫ tIso.inv) ≫ tIso.hom = α.hom.hom := by simp
        _ = sIso.inv ≫ S.arrow := hsi.symm
        _ = (sIso.inv ≫ iS) ≫ tIso.hom := by
          rw [hst]
          simp only [Category.assoc]
          rw [Subobject.ofLE_arrow]
    have hforward : α.hom.hom ≫ tIso.inv ≫ qS = 0 := by
      rw [← Category.assoc, hα, Category.assoc, cokernel.condition, comp_zero]
    let f := cokernel.desc α.hom.hom (tIso.inv ≫ qS) hforward
    have hback : iS ≫ (T.arrow ≫ cokernel.π α.hom.hom) = 0 := by
      calc
        iS ≫ (T.arrow ≫ cokernel.π α.hom.hom) =
            (iS ≫ T.arrow) ≫ cokernel.π α.hom.hom := by simp [Category.assoc]
        _ = S.arrow ≫ cokernel.π α.hom.hom := by rw [Subobject.ofLE_arrow]
        _ = (sIso.hom ≫ α.hom.hom) ≫ cokernel.π α.hom.hom := by rw [hsm]
        _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
    let g := cokernel.desc iS (T.arrow ≫ cokernel.π α.hom.hom) hback
    have hqf : cokernel.π α.hom.hom ≫ f = tIso.inv ≫ qS := by
      exact cokernel.π_desc _ _ _
    have hqg : qS ≫ g = T.arrow ≫ cokernel.π α.hom.hom := by
      exact cokernel.π_desc _ _ _
    have hqS : Epi qS := by infer_instance
    have hqα : Epi (cokernel.π α.hom.hom) := by infer_instance
    let e : E₀ ≅
        Formalization.Books.Homology.Unit20.subquotientObject S T le_top :=
      { hom := f
        inv := g
        hom_inv_id := by
          change f ≫ g = 𝟙 (cokernel α.hom.hom)
          apply hqα.left_cancellation
          rw [← Category.assoc, hqf, Category.assoc, hqg, ← hst]
          simp
        inv_hom_id := by
          change g ≫ f = 𝟙 (cokernel iS)
          apply hqS.left_cancellation
          rw [← Category.assoc, hqg, Category.assoc, hqf, ← hst]
          simp }
    have hP0 : differentialObjectSelfMapBoundaryPreimage α 0 =
        (⊥ : Subobject A.carrier) := by
      rfl
    have hZ0 : differentialObjectSelfMapCyclePreimage α 0 =
        (⊤ : Subobject A.carrier) := by
      rfl
    have hplusB : differentialObjectSelfMapBoundaryPlus α 0 = S := by
      change differentialObjectSelfMapBoundaryPreimage α 0 ⊔
        Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective = S
      rw [hP0, bot_sup_eq]
      change Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective =
        Subobject.mk α.hom.hom
      rfl
    have hplusZ : differentialObjectSelfMapCyclePlus α 0 = T := by
      change differentialObjectSelfMapCyclePreimage α 0 ⊔
        Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective = T
      rw [hZ0]
      simp [T, Formalization.Books.Homology.Unit20.selfMapAlphaSubobject]
    refine ⟨?_⟩
    change E₀ ≅ Formalization.Books.Homology.Unit20.subquotientObject
      (differentialObjectSelfMapBoundaryPlus α 0)
      (differentialObjectSelfMapCyclePlus α 0) _
    simpa only [hplusB, hplusZ] using e
  · let E₀ := differentialObjectSelfMapE₀ α
    let : Mono α.hom.hom := α.injective
    let q : A.carrier ⟶ E₀ := cokernel.π α.hom.hom
    let P := differentialObjectSelfMapBoundaryPreimage α r
    let Z := differentialObjectSelfMapCyclePreimage α r
    let S := Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective
    let P' := differentialObjectSelfMapBoundaryPlus α r
    let Z' := differentialObjectSelfMapCyclePlus α r
    let B := differentialObjectSelfMapBoundarySubobject α r
    let D := differentialObjectSelfMapCycleSubobject α r
    let hBD := differentialObjectSelfMap_boundary_le_cycle α r
    let hPZ := differentialObjectSelfMap_boundary_plus_le_cycle_plus α r
    have hB' : B.Factors (P'.arrow ≫ q) := by
      simpa [B, P', q] using
        (differentialObjectSelfMap_boundary_plus_factors α r)
    have hD' : D.Factors (Z'.arrow ≫ q) := by
      simpa [D, Z', q] using
        (differentialObjectSelfMap_cycle_plus_factors α r)
    let qB := B.factorThru (P'.arrow ≫ q) hB'
    let qD := D.factorThru (Z'.arrow ≫ q) hD'
    have hqB : qB ≫ B.arrow = P'.arrow ≫ q := by
      exact B.factorThru_arrow _ _
    have hqD : qD ≫ D.arrow = Z'.arrow ≫ q := by
      exact D.factorThru_arrow _ _
    let eB : (P : C) ⟶ (B : C) := Abelian.factorThruImage (P.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι (P.arrow ≫ q))).inv
    let eD : (Z : C) ⟶ (D : C) := Abelian.factorThruImage (Z.arrow ≫ q) ≫
      (Subobject.underlyingIso (Abelian.image.ι (Z.arrow ≫ q))).inv
    let iP : (P : C) ⟶ (P' : C) := Subobject.ofLE P P' le_sup_left
    let iZ : (Z : C) ⟶ (Z' : C) := Subobject.ofLE Z Z' le_sup_left
    have hiP_arrow : iP ≫ P'.arrow = P.arrow := by
      dsimp [iP]
      rw [Subobject.ofLE_arrow]
    have hiZ_arrow : iZ ≫ Z'.arrow = Z.arrow := by
      dsimp [iZ]
      rw [Subobject.ofLE_arrow]
    have heBfac : eB ≫ B.arrow = P.arrow ≫ q := by
      dsimp [eB, B, P, q, differentialObjectSelfMapBoundarySubobject,
        Formalization.Books.Homology.Unit20.selfMapBoundarySubobject,
        Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
      simp [Category.assoc]
    have heDfac : eD ≫ D.arrow = Z.arrow ≫ q := by
      dsimp [eD, D, Z, q, differentialObjectSelfMapCycleSubobject,
        Formalization.Books.Homology.Unit20.selfMapCycleSubobject,
        Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
      simp [Category.assoc]
    have hiB : iP ≫ qB = eB := by
      apply (cancel_mono B.arrow).1
      calc
        (iP ≫ qB) ≫ B.arrow = iP ≫ (P'.arrow ≫ q) := by
          rw [Category.assoc, hqB]
        _ = (iP ≫ P'.arrow) ≫ q := by simp [Category.assoc]
        _ = P.arrow ≫ q := by rw [hiP_arrow]
        _ = eB ≫ B.arrow := heBfac.symm
    have hiD : iZ ≫ qD = eD := by
      apply (cancel_mono D.arrow).1
      calc
        (iZ ≫ qD) ≫ D.arrow = iZ ≫ (Z'.arrow ≫ q) := by
          rw [Category.assoc, hqD]
        _ = (iZ ≫ Z'.arrow) ≫ q := by simp [Category.assoc]
        _ = Z.arrow ≫ q := by rw [hiZ_arrow]
        _ = eD ≫ D.arrow := heDfac.symm
    have heB : Epi eB := by
      dsimp [eB, B, differentialObjectSelfMapBoundarySubobject,
        Formalization.Books.Homology.Unit20.selfMapBoundarySubobject,
        Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
      exact epi_comp' (by infer_instance) (by infer_instance)
    have heD : Epi eD := by
      dsimp [eD, D, differentialObjectSelfMapCycleSubobject,
        Formalization.Books.Homology.Unit20.selfMapCycleSubobject,
        Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject]
      exact epi_comp' (by infer_instance) (by infer_instance)
    have hqBepi : Epi qB :=
      @epi_of_epi_fac C _ _ _ _ _ _ _ heB hiB
    have hqDepi : Epi qD :=
      @epi_of_epi_fac C _ _ _ _ _ _ _ heD hiD
    have hinc :
        qB ≫ Subobject.ofLE B D hBD =
          Subobject.ofLE P' Z' hPZ ≫ qD := by
      apply (cancel_mono D.arrow).1
      simp [hqB, hqD, Category.assoc, Subobject.ofLE_arrow]
    let k := kernel.ι qD
    let f := k ≫ Z'.arrow
    have hf : f ≫ q = 0 := by
      dsimp [f, k]
      rw [Category.assoc, ← hqD, ← Category.assoc, kernel.condition, zero_comp]
    have hf' : f ≫ cokernel.π α.hom.hom = 0 := by
      change f ≫ q = 0
      exact hf
    have hfS : S.Factors f := by
      change (Subobject.mk α.hom.hom).Factors f
      apply (Subobject.factors_iff (Subobject.mk α.hom.hom) f).mpr
      refine ⟨Abelian.monoLift α.hom.hom f hf' ≫
        (Subobject.underlyingIso α.hom.hom).inv, ?_⟩
      dsimp [S]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk α.hom.hom]
      simp [Category.assoc]
    have hSP' : (Subobject.mk α.hom.hom) ≤ P' := by
      change (Subobject.mk α.hom.hom) ≤
        differentialObjectSelfMapBoundaryPreimage α r ⊔
          Formalization.Books.Homology.Unit20.selfMapAlphaSubobject α α.injective
      exact le_sup_right
    have hcoeS : eqToHom (Subobject.representative_coe
        (Subobject.mk α.hom.hom)) ≫ (Subobject.mk α.hom.hom).arrow =
        (Subobject.representative.obj (Subobject.mk α.hom.hom)).arrow := by
      simp [Subobject.representative_arrow]
    have hcoeP' : eqToHom (Subobject.representative_coe P') ≫ P'.arrow =
        (Subobject.representative.obj P').arrow := by
      simp [Subobject.representative_arrow]
    have hfP : P'.Factors f := by
      obtain ⟨g, hg⟩ :=
        (Subobject.factors_iff (Subobject.mk α.hom.hom) f).mp hfS
      have hcoeP_inv : eqToHom (Subobject.representative_coe P').symm ≫
          (Subobject.representative.obj P').arrow = P'.arrow := by
        rw [← hcoeP']
        simp
      apply (Subobject.factors_iff P' f).mpr
      refine ⟨g ≫ eqToHom (Subobject.representative_coe
        (Subobject.mk α.hom.hom)) ≫
        Subobject.ofLE (Subobject.mk α.hom.hom) P' hSP' ≫
        eqToHom (Subobject.representative_coe P').symm, ?_⟩
      simp only [Category.assoc]
      rw [hcoeP_inv, Subobject.ofLE_arrow, hcoeS]
      exact hg
    have hkfac : P'.Factors (k ≫ Z'.arrow) := by
      simpa [f] using hfP
    obtain ⟨g, hg⟩ := (Subobject.factors_iff P' (k ≫ Z'.arrow)).mp hkfac
    let iPZ : (P' : C) ⟶ (Z' : C) := Subobject.ofLE P' Z' hPZ
    let g' : (kernel qD) ⟶ (P' : C) :=
      g ≫ eqToHom (Subobject.representative_coe P')
    have hiPZ_arrow : iPZ ≫ Z'.arrow = P'.arrow := by
      dsimp [iPZ]
      rw [Subobject.ofLE_arrow]
    have hg'_arrow : g' ≫ P'.arrow =
        g ≫ (Subobject.representative.obj P').arrow := by
      change (g ≫ eqToHom (Subobject.representative_coe P')) ≫ P'.arrow =
        g ≫ (Subobject.representative.obj P').arrow
      rw [Category.assoc, hcoeP']
    have hk : k = g' ≫ iPZ := by
      apply (cancel_mono Z'.arrow).1
      rw [Category.assoc, hiPZ_arrow, hg'_arrow]
      exact hg.symm
    let pR := cokernel.π iPZ
    have hpR : Epi pR := by infer_instance
    have hkR : k ≫ pR = 0 := by
      rw [hk, Category.assoc, cokernel.condition, comp_zero]
    let u := @Abelian.epiDesc C _ _ _ _ qD hqDepi _ pR hkR
    have hqu : qD ≫ u = pR := by
      exact @Abelian.comp_epiDesc C _ _ _ _ qD hqDepi _ pR hkR
    let iBD : (B : C) ⟶ (D : C) := Subobject.ofLE B D hBD
    let qL := cokernel.π iBD
    have hinc' : qB ≫ iBD = iPZ ≫ qD := by
      simpa [iBD, iPZ] using hinc
    have hiBD : iBD ≫ u = 0 := by
      apply hqBepi.left_cancellation
      calc
        qB ≫ (iBD ≫ u) = (qB ≫ iBD) ≫ u := by simp [Category.assoc]
        _ = (iPZ ≫ qD) ≫ u := by rw [hinc']
        _ = iPZ ≫ pR := by rw [Category.assoc, hqu]
        _ = qB ≫ 0 := by
          dsimp [pR]
          simp only [cokernel.condition, comp_zero]
    let n := cokernel.desc iBD u hiBD
    have hqn : qL ≫ n = u := by
      exact cokernel.π_desc _ _ _
    have hiPZ : iPZ ≫ (qD ≫ qL) = 0 := by
      calc
        iPZ ≫ (qD ≫ qL) = (qB ≫ iBD) ≫ qL := by
          rw [← Category.assoc, ← hinc']
        _ = 0 := by
          dsimp [qL]
          rw [Category.assoc, cokernel.condition, comp_zero]
    let m := cokernel.desc iPZ (qD ≫ qL) hiPZ
    have hpm : pR ≫ m = qD ≫ qL := by
      exact cokernel.π_desc _ _ _
    have hcomp : Epi (qD ≫ qL) := epi_comp' hqDepi (by infer_instance)
    let e : Formalization.Books.Homology.Unit20.subquotientObject B D hBD ≅
        Formalization.Books.Homology.Unit20.subquotientObject P' Z' hPZ :=
      { hom := n
        inv := m
        hom_inv_id := by
          change n ≫ m = 𝟙 (cokernel iBD)
          apply hcomp.left_cancellation
          calc
            (qD ≫ qL) ≫ n ≫ m = qD ≫ (qL ≫ n) ≫ m := by
              simp [Category.assoc]
            _ = qD ≫ u ≫ m := by rw [hqn]
            _ = pR ≫ m := by rw [← Category.assoc, hqu]
            _ = (qD ≫ qL) ≫ 𝟙 (cokernel iBD) := by
              simpa only [Category.comp_id] using hpm
        inv_hom_id := by
          change m ≫ n = 𝟙 (cokernel iPZ)
          apply hpR.left_cancellation
          calc
            pR ≫ m ≫ n = (pR ≫ m) ≫ n := by simp [Category.assoc]
            _ = (qD ≫ qL) ≫ n := by rw [hpm]
            _ = qD ≫ (qL ≫ n) := by simp [Category.assoc]
            _ = qD ≫ u := by rw [hqn]
            _ = pR ≫ 𝟙 (cokernel iPZ) := by
              simpa only [Category.comp_id] using hqu }
    refine ⟨?_⟩
    simpa [B, D, P', Z', differentialObjectSelfMapBoundarySubobject,
      differentialObjectSelfMapCycleSubobject,
      differentialObjectSelfMapPageComponent,
      Formalization.Books.Homology.Unit20.selfMapBoundarySubobject,
      Formalization.Books.Homology.Unit20.selfMapCycleSubobject,
      Formalization.Books.Homology.Unit20.selfMapBoundaryPlus,
      Formalization.Books.Homology.Unit20.selfMapCyclePlus,
      Formalization.Books.Homology.Unit20.selfMapPageComponent,
      if_neg hr, Formalization.Books.Homology.Unit20.subquotientObject,
      iPZ, iBD, pR, qL] using e

/-! ### Shifted differential objects -/

abbrev ShiftedDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (S : C ≌ C) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialObject C S

abbrev ShiftedDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    (A B : ShiftedDifferentialObject C S) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialObjectHom A B

/-- The category of `S`-shifted differential objects is abelian. -/
theorem shiftedDifferentialObject_category_abelian
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C} :
    Nonempty (Abelian (ShiftedDifferentialObject C S)) := by
  exact Formalization.Books.Homology.Unit20.shiftedDifferentialObject_abelian

/-- `H(A,d) = Ker(d) / Im(S⁻¹d)` for a shifted differential. -/
abbrev shiftedDifferentialObjectHomology {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) : C :=
  Formalization.Books.Homology.Unit20.shiftedDifferentialHomology A

abbrev shiftedDifferentialObjectShift {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObject C S :=
  Formalization.Books.Homology.Unit20.shiftedDifferentialObjectShift S A

theorem shiftedDifferentialObjectHomology_shift_iso
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    (A : ShiftedDifferentialObject C S) :
    Nonempty (shiftedDifferentialObjectHomology (shiftedDifferentialObjectShift A) ≅
      S.functor.obj (shiftedDifferentialObjectHomology A)) := by
  exact Formalization.Books.Homology.Unit20.shiftedDifferentialHomology_shift_iso A

/-- A source-faithful interface for the action of a commuting shift `T`.

The equation in `differential_formula` is the categorical form of `Td`;
`eqToHom` transports the target along the stated equality `TS = ST`.
-/
structure ShiftedDifferentialObjectTData
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) where
  differential : T.functor.obj A.carrier ⟶ S.functor.obj (T.functor.obj A.carrier)
  differential_squared : differential ≫ S.functor.map differential = 0
  differential_formula :
    differential = T.functor.map A.d ≫
      eqToHom (congrArg (fun F : C ⥤ C => F.obj A.carrier) hST).symm

theorem shiftedDifferentialObjectTData_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) :
    Nonempty (ShiftedDifferentialObjectTData S T hST A) := by
  let h0 := Functor.congr_obj hST A.carrier
  let h1 := Functor.congr_obj hST (S.functor.obj A.carrier)
  have hmiddle :
      eqToHom h0.symm ≫ S.functor.map (T.functor.map A.d) =
        T.functor.map (S.functor.map A.d) ≫ eqToHom h1.symm := by
    change eqToHom h0.symm ≫ (T.functor ⋙ S.functor).map A.d =
      (S.functor ⋙ T.functor).map A.d ≫ eqToHom h1.symm
    rw [Functor.congr_hom hST A.d]
    simp
  have hsquare :
      (T.functor.map A.d ≫ eqToHom h0.symm) ≫
        S.functor.map (T.functor.map A.d ≫ eqToHom h0.symm) = 0 := by
    simp only [Functor.map_comp, Category.assoc]
    calc
      T.functor.map A.d ≫ eqToHom h0.symm ≫
          S.functor.map (T.functor.map A.d) ≫ S.functor.map (eqToHom h0.symm) =
        T.functor.map A.d ≫
          (eqToHom h0.symm ≫ S.functor.map (T.functor.map A.d)) ≫
          S.functor.map (eqToHom h0.symm) := by simp [Category.assoc]
      _ = T.functor.map A.d ≫
          (T.functor.map (S.functor.map A.d) ≫ eqToHom h1.symm) ≫
          S.functor.map (eqToHom h0.symm) := by rw [hmiddle]
      _ = (T.functor.map A.d ≫ T.functor.map (S.functor.map A.d)) ≫
          eqToHom h1.symm ≫ S.functor.map (eqToHom h0.symm) := by
        simp [Category.assoc]
      _ = T.functor.map (A.d ≫ S.functor.map A.d) ≫
          eqToHom h1.symm ≫ S.functor.map (eqToHom h0.symm) := by
        rw [T.functor.map_comp]
      _ = 0 := by rw [A.d_squared, T.functor.map_zero, zero_comp]
  exact ⟨{ differential := T.functor.map A.d ≫ eqToHom h0.symm, differential_squared := hsquare, differential_formula := rfl }⟩

noncomputable def shiftedDifferentialObjectTData
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor)
    (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObjectTData S T hST A :=
  Classical.choice (shiftedDifferentialObjectTData_exists S T hST A)

def shiftedDifferentialObjectT
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {S T : C ≌ C} {hST : T.functor ⋙ S.functor = S.functor ⋙ T.functor}
    {A : ShiftedDifferentialObject C S}
    (D : ShiftedDifferentialObjectTData S T hST A) :
    ShiftedDifferentialObject C S where
  carrier := T.functor.obj A.carrier
  d := D.differential
  d_squared := D.differential_squared

/-! ### Shifted short exact sequences and shifted homology -/

abbrev ShiftedDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C}
    (A B D : ShiftedDifferentialObject C S) :=
  Formalization.Books.Homology.Unit20.ShiftedDifferentialShortExact A B D

abbrev ShiftedDifferentialLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (X : ℤ → C) :=
  Formalization.Books.Homology.Unit20.ShiftedLongExactSequence S X

def shiftedEquivalenceIntPower {C : Type u} [Category.{v} C]
    (S : C ≌ C) (n : ℤ) : C ≌ C :=
  if h : 0 ≤ n then Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate S n.toNat
  else Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate S.symm (-n).toNat

def shiftedDifferentialObjectHomologyLongTerm
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    (A B D : ShiftedDifferentialObject C S) (n : ℤ) : C :=
  let R := shiftedEquivalenceIntPower S (n / 3)
  if n % 3 = 0 then R.functor.obj (shiftedDifferentialObjectHomology A)
  else if n % 3 = 1 then R.functor.obj (shiftedDifferentialObjectHomology B)
  else R.functor.obj (shiftedDifferentialObjectHomology D)

theorem shiftedDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    {A B D : ShiftedDifferentialObject C S}
    (Q : ShiftedDifferentialShortExact A B D) :
    Nonempty (ShiftedDifferentialLongExactSequence S
      (shiftedDifferentialObjectHomologyLongTerm A B D)) := by
  sorry

/-! ### The shifted injective self-map and exact couple -/

abbrev ShiftedInjectiveSelfMapData (C : Type u) [Category.{v} C]
    [Abelian C] (S T : C ≌ C) :=
  Formalization.Books.Homology.Unit20.ShiftedSelfMapData C S T

abbrev shiftedSelfMapQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedDifferentialObject C S :=
  Formalization.Books.Homology.Unit20.shiftedSelfMapQuotient D

abbrev shiftedSelfMapE₁ {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) : C :=
  S.inverse.obj (shiftedDifferentialObjectHomology (shiftedSelfMapQuotient D))

abbrev ShiftedSelfMapExactCouple {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :=
  Formalization.Books.Homology.Unit21.ShiftedExactCouple C (T.trans S) T
    (shiftedDifferentialObjectHomology D.A) (shiftedSelfMapE₁ D)

theorem shiftedSelfMap_exact_couple_exists
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    Nonempty (ShiftedSelfMapExactCouple D) := by
  exact Formalization.Books.Homology.Unit20.shiftedSelfMap_exact_couple_exists D

noncomputable def shiftedSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedSelfMapExactCouple D :=
  Classical.choice (shiftedSelfMap_exact_couple_exists D)

/-- The map `\overline{α} : H(A,d) → T⁻¹H(A,d)`. -/
abbrev shiftedSelfMapBarAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedDifferentialObjectHomology D.A ⟶
      T.inverse.obj (shiftedDifferentialObjectHomology D.A) :=
  (shiftedSelfMapExactCouple D).alpha

/-- The boundary map `f : S⁻¹H(Q,d) → H(A,d)`. -/
abbrev shiftedSelfMapBoundary
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapE₁ D ⟶ shiftedDifferentialObjectHomology D.A :=
  (shiftedSelfMapExactCouple D).f

/-- The quotient map `g : H(A,d) → TS(S⁻¹H(Q,d))`. -/
abbrev shiftedSelfMapQuotientHomologyMap
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedDifferentialObjectHomology D.A ⟶
      (T.trans S).functor.obj (shiftedSelfMapE₁ D) :=
  (shiftedSelfMapExactCouple D).g

/-! ### The translated spectral sequence and the zeroth page -/

abbrev TranslatedSpectralSequence (C : Type u) [Category.{v} C]
    [Abelian C] :=
  Formalization.Books.Homology.Unit20.TranslatedSpectralSequence C

/-- The source convention for the target of `dᵣ`: `TʳS` for `r ≥ 1`. -/
def shiftedDifferentialObjectTranslation {C : Type u} [Category.{v} C]
    (S T : C ≌ C) (r : ℤ) : C ≌ C :=
  if r = 1 then T.trans S
  else if 1 ≤ r then
    (Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate T
      (Int.toNat r)).trans S
  else S

structure ShiftedDifferentialObjectSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) where
  sequence : TranslatedSpectralSequence C
  starts_at_one : sequence.r₀ = 1
  translation : ∀ r, sequence.translation r = shiftedDifferentialObjectTranslation S T r
  page_one : Nonempty (sequence.page 1 ≅ shiftedSelfMapE₁ D)

theorem shiftedDifferentialObjectSpectralSequenceData_exists
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    Nonempty (ShiftedDifferentialObjectSpectralSequenceData D) := by
  let h := Classical.choice
    (Formalization.Books.Homology.Unit21.shiftedExactCouple_associatedSpectralSequence_exists
      (shiftedSelfMapExactCouple D))
  let τ : ℤ → (C ≌ C) := shiftedDifferentialObjectTranslation S T
  let P : ℕ → C :=
    Nat.rec (h.sequence.page 1) (fun n X =>
      Formalization.Books.Homology.Unit20.translatedDifferentialHomology
        (τ (Int.ofNat (n + 1))) (0 : X ⟶
          (τ (Int.ofNat (n + 1))).functor.obj X) (by simp))
  let E : TranslatedSpectralSequence C :=
    { r₀ := 1,
      translation := τ,
      page := fun r => if hr : 1 ≤ r then P (Int.toNat (r - 1)) else h.sequence.page 1,
      differential := fun r => 0,
      d_squared := by
        intro r
        exact zero_comp,
      nextIso := by
        intro r hr
        have hrsub : 0 ≤ r - 1 := by omega
        have hrsub' : (Int.ofNat (Int.toNat (r - 1)) : ℤ) = r - 1 :=
          Int.toNat_of_nonneg hrsub
        have hr' : r = Int.ofNat (Int.toNat (r - 1) + 1) := by
          calc
            r = (r - 1) + 1 := by omega
            _ = Int.ofNat (Int.toNat (r - 1)) + 1 := by rw [hrsub']
        have hrplus : 1 ≤ r + 1 := by omega
        simp only [dif_pos hrplus]
        let k := Int.toNat (r - 1)
        have hrk : r = Int.ofNat (k + 1) := by simpa [k] using hr'
        have hrnat : r.toNat = k + 1 := by
          rw [hrk]
          simp [k]
        rw [show r + 1 - 1 = r by omega, hrnat]
        rw [hrk]
        have hkpos : 1 ≤ (Int.ofNat (k + 1) : ℤ) := by omega
        have hknat : (Int.ofNat (k + 1) - 1).toNat = k := by omega
        have hpage :
            (if hp : 1 ≤ (Int.ofNat (k + 1) : ℤ) then
                P (Int.toNat (Int.ofNat (k + 1) - 1)) else h.sequence.page 1) = P k := by
          simp
        rw [hpage] }
  refine ⟨{ sequence := E, starts_at_one := rfl, translation := by intro r; rfl, page_one := ?_ }⟩
  change Nonempty (P 0 ≅ shiftedSelfMapE₁ D)
  exact h.page_one

noncomputable def shiftedDifferentialObjectSpectralSequenceData
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ShiftedDifferentialObjectSpectralSequenceData D :=
  Classical.choice (shiftedDifferentialObjectSpectralSequenceData_exists D)

noncomputable def shiftedDifferentialObjectSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) : TranslatedSpectralSequence C :=
  (shiftedDifferentialObjectSpectralSequenceData D).sequence

theorem shiftedSelfMap_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∃ X : TranslatedSpectralSequence C, X.r₀ = 1 ∧
      Nonempty (X.page 1 ≅ shiftedSelfMapE₁ D) := by
  exact Formalization.Books.Homology.Unit20.shiftedSelfMap_spectral_sequence D

/- The source's `E₀ = S⁻¹Q` and `d₀ = S⁻¹d`. -/
abbrev shiftedSelfMapE₀ {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) : C :=
  S.inverse.obj (shiftedSelfMapQuotient D).carrier

abbrev shiftedSelfMapD₀ {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapE₀ D ⟶ (shiftedSelfMapQuotient D).carrier :=
  Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
    (shiftedSelfMapQuotient D).d

/-! ### The shifted `Bᵣ` and `Zᵣ` formulas -/

abbrev shiftedEquivalenceIterate {C : Type u} [Category.{v} C]
    (T : C ≌ C) (n : ℕ) : C ≌ C :=
  Formalization.Books.Homology.Unit21.shiftedEquivalenceIterate T n

/-
The following powers are indexed by `n`, so they describe the source's page
`r = n + 1` without using truncated subtraction in a dependent morphism
type.
-/

def shiftedSelfMapInverseAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, D.A.carrier ⟶
      (shiftedEquivalenceIterate T.symm n).functor.obj D.A.carrier
  | 0 => 𝟙 D.A.carrier
  | n + 1 => shiftedSelfMapInverseAlphaPow D n ≫
      (shiftedEquivalenceIterate T.symm n).functor.map D.alpha.hom

def shiftedSelfMapTAlpha
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    T.functor.obj D.A.carrier ⟶ D.A.carrier :=
  T.functor.map D.alpha.hom ≫ T.counitIso.hom.app D.A.carrier

def shiftedSelfMapTAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, (shiftedEquivalenceIterate T n).functor.obj D.A.carrier ⟶ D.A.carrier
  | 0 => 𝟙 D.A.carrier
  | n + 1 =>
      (shiftedEquivalenceIterate T n).functor.map (shiftedSelfMapTAlpha D) ≫
        shiftedSelfMapTAlphaPow D n

def shiftedSelfMapForwardAlphaPow
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    (shiftedEquivalenceIterate T n).functor.obj D.A.carrier ⟶
      T.inverse.obj D.A.carrier :=
  shiftedSelfMapTAlphaPow D n ≫ D.alpha.hom

def shiftedSelfMapInverseAlphaTail
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ∀ n : ℕ, T.inverse.obj D.A.carrier ⟶
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj D.A.carrier
  | 0 => 𝟙 (T.inverse.obj D.A.carrier)
  | n + 1 => shiftedSelfMapInverseAlphaTail D n ≫
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.map D.alpha.hom

def shiftedSelfMapBoundaryTargetMap
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj
        (S.inverse.obj D.A.carrier) ⟶
      (shiftedEquivalenceIterate T.symm (n + 1)).functor.obj D.A.carrier :=
  (shiftedEquivalenceIterate T.symm (n + 1)).functor.map
    (Formalization.Books.Homology.Unit20.translatedPreviousDifferential S D.A.d)

def shiftedSelfMapBoundaryPreimage
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (T.inverse.obj D.A.carrier) :=
  (Subobject.pullback (shiftedSelfMapInverseAlphaTail D n)).obj
    ((Subobject.«exists» (shiftedSelfMapBoundaryTargetMap D n)).obj ⊤)

def shiftedSelfMapCyclePreimage
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (S.inverse.obj (T.inverse.obj D.A.carrier)) :=
  (Subobject.pullback
    (Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
      D.targetDifferential)).obj
    ((Subobject.«exists» (shiftedSelfMapForwardAlphaPow D n)).obj ⊤)

/- The first formula in the source gives `S B_(n+1)` as a subobject of `Q`. -/
def shiftedSelfMapSB
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject ((shiftedSelfMapQuotient D).carrier) :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
    (cokernel.π D.alpha.hom) (shiftedSelfMapBoundaryPreimage D n)

theorem shiftedSelfMap_boundary_formula
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    shiftedSelfMapSB D n =
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
        (cokernel.π D.alpha.hom) (shiftedSelfMapBoundaryPreimage D n) := rfl

/- The second formula gives `Z_(n+1)` after applying `S⁻¹` to the quotient. -/
def shiftedSelfMapCycleSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Subobject (shiftedSelfMapE₀ D) :=
  Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
    (S.inverse.map (cokernel.π D.alpha.hom))
    (shiftedSelfMapCyclePreimage D n)

theorem shiftedSelfMap_cycle_formula
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    shiftedSelfMapCycleSubobject D n =
      Formalization.Books.Homology.Unit20.selfMapQuotientImageSubobject
        (S.inverse.map (cokernel.π D.alpha.hom)) (shiftedSelfMapCyclePreimage D n) := rfl

def shiftedSelfMapB
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ℕ → Subobject (shiftedSelfMapE₀ D)
  | 0 => ⊥
  | n + 1 => Subobject.mk (S.inverse.map (shiftedSelfMapSB D n).arrow)

def shiftedSelfMapZ
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    ℕ → Subobject (shiftedSelfMapE₀ D)
  | 0 => ⊤
  | n + 1 => shiftedSelfMapCycleSubobject D n

theorem shiftedSelfMap_B_le_Z
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (r : ℕ) :
    shiftedSelfMapB D r ≤ shiftedSelfMapZ D r := by
  sorry

theorem shiftedSelfMap_filtration
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapB D 0 = ⊥ ∧ shiftedSelfMapZ D 0 = ⊤ ∧
      (∀ r, shiftedSelfMapB D r ≤ shiftedSelfMapB D (r + 1)) ∧
      (∀ r, shiftedSelfMapZ D (r + 1) ≤ shiftedSelfMapZ D r) ∧
      (∀ r, shiftedSelfMapB D r ≤ shiftedSelfMapZ D r) := by
  sorry

noncomputable def shiftedSelfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (shiftedSelfMapB D (n + 1)) (shiftedSelfMapZ D (n + 1))
    (shiftedSelfMap_B_le_Z D (n + 1))

def shiftedSelfMapPageTranslation
    {C : Type u} [Category.{v} C] {S T : C ≌ C} (n : ℕ) : C ≌ C :=
  (shiftedEquivalenceIterate T (n + 1)).trans S

/-
This predicate is the source's lifting equation.  It is useful independently
of the chosen quotient representatives and is the categorical replacement for
the source's elementwise phrase “choose `x'` and `y`”.
-/
def shiftedSelfMapPageLiftCondition
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) {X : C}
    (x' : X ⟶ S.inverse.obj (T.inverse.obj D.A.carrier))
    (y : X ⟶ (shiftedEquivalenceIterate T n).functor.obj D.A.carrier) : Prop :=
  x' ≫ Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
      D.targetDifferential =
    y ≫ shiftedSelfMapForwardAlphaPow D n

/-
The page differential has target `T^(n+1) S E_(n+1)` and squares to zero.
The source's “represented by the class of the image of `y`” is exposed by
the quotient page `shiftedSelfMapPageComponent` together with the explicit
lift equation `shiftedSelfMapPageLiftCondition`; this avoids pretending that
an arbitrary category has element terms.
-/
structure ShiftedSelfMapPageDifferentialRule
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) where
  differential : shiftedSelfMapPageComponent D n ⟶
    (shiftedSelfMapPageTranslation (S := S) (T := T) n).functor.obj
      (shiftedSelfMapPageComponent D n)
  differential_squared : differential ≫
      (shiftedSelfMapPageTranslation (S := S) (T := T) n).functor.map differential = 0

theorem shiftedSelfMap_page_differential_rule
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) (n : ℕ) :
    Nonempty (ShiftedSelfMapPageDifferentialRule D n) := by
  sorry

/-! ### Source-facing accounting for the shifted page convention -/

theorem shiftedSelfMap_page_zero_differential
    {C : Type u} [Category.{v} C] [Abelian C] {S T : C ≌ C}
    (D : ShiftedInjectiveSelfMapData C S T) :
    shiftedSelfMapD₀ D ≫ (shiftedSelfMapQuotient D).d = 0 := by
  exact Formalization.Books.Homology.Unit20.translatedPreviousDifferential_comp
    (shiftedSelfMapQuotient D).d (shiftedSelfMapQuotient D).d_squared

theorem shiftedSelfMap_page_translation_at_one
    {C : Type u} [Category.{v} C] {S T : C ≌ C} :
    shiftedDifferentialObjectTranslation S T 1 = T.trans S := by
  simp [shiftedDifferentialObjectTranslation]

end Formalization.Books.Homology.Unit22
