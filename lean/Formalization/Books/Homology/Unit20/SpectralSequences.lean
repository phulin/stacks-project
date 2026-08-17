import Formalization.Books.Homology.Unit19.Filtrations
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homological Algebra, Chapter 20: Spectral sequences

The source's ungraded spectral sequences are the one-object specialization of
Mathlib's `CategoryTheory.SpectralSequence`: the page is a homological complex
on `PUnit` with the reflexive complex shape.  The general Mathlib definition
is used for the page/next-page isomorphisms, so the source's quotient notation
is recorded by explicit subobject-filtration data below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.1 Spectral sequences -/

/- The reflexive shape is the canonical one-object complex shape in Mathlib. -/
abbrev PlainSpectralSequenceShape : ComplexShape PUnit := ComplexShape.refl PUnit

/-- An ungraded spectral sequence, allowing an arbitrary integral starting page. -/
abbrev PlainSpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (r₀ : ℤ := 1) :=
  CategoryTheory.SpectralSequence C (fun _ : ℤ => PlainSpectralSequenceShape) r₀

/-- The one-object page attached to an object and a square-zero endomorphism. -/
def plainSpectralSequencePage {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (A : C) (d : A ⟶ A) (hd : d ≫ d = 0) :
    HomologicalComplex C PlainSpectralSequenceShape where
  X := fun _ => A
  d := fun _ _ => d
  shape := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  d_comp_d' := by
    intro i j k _ _
    exact hd

/-- The object on a page of a plain spectral sequence. -/
abbrev plainPageObject {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : C :=
  (E.page r hr).X PUnit.unit

/-- The differential on a page of a plain spectral sequence. -/
abbrev plainPageDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    plainPageObject E r hr ⟶ plainPageObject E r hr :=
  (E.page r hr).d PUnit.unit PUnit.unit

theorem plainPageDifferential_sq {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    plainPageDifferential E r hr ≫ plainPageDifferential E r hr = 0 := by
  exact (E.page r hr).d_comp_d _ _ _

/-- A morphism of plain spectral sequences, using Mathlib's canonical notion. -/
abbrev PlainSpectralSequenceHom {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E E' : PlainSpectralSequence C r₀) := E ⟶ E'

/-- The component of a morphism of plain spectral sequences on page `r`. -/
abbrev plainSpectralSequenceHomComponent {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} {E E' : PlainSpectralSequence C r₀}
    (f : PlainSpectralSequenceHom E E') (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    plainPageObject E r hr ⟶ plainPageObject E' r hr :=
  (f.hom r hr).f PUnit.unit

/-! ### The `Zᵣ/Bᵣ` description -/

/-- The quotient of a subobject by a smaller subobject. -/
noncomputable def subquotientObject {C : Type u} [Category.{v} C] [Abelian C]
    {X : C} (B Z : Subobject X) (hBZ : B ≤ Z) : C :=
  cokernel (Subobject.ofLE B Z hBZ)

/-- The homology object of a square-zero endomorphism, written as the
categorical quotient `Ker(d)/Im(d)`. -/
noncomputable def differentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] {A : C} (d : A ⟶ A) (hd : d ≫ d = 0) : C :=
  cokernel (kernel.lift d (Abelian.image.ι d)
    (Abelian.image_ι_comp_eq_zero hd))

/-- The increasing/decreasing subobject filtration attached to a plain page.

`pageIso` records the source assertion `Eᵣ = Zᵣ/Bᵣ` up to the canonical
categorical notion of isomorphism. -/
structure SpectralSequencePageFiltration {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} (E : PlainSpectralSequence C r₀) where
  B : ℤ → Subobject (plainPageObject E r₀ (by lia))
  Z : ℤ → Subobject (plainPageObject E r₀ (by lia))
  B_one : B r₀ = ⊥
  Z_one : Z r₀ = ⊤
  B_le_Z : ∀ r, r₀ ≤ r → B r ≤ Z r
  B_mono : ∀ r, r₀ ≤ r → B r ≤ B (r + 1)
  Z_antitone : ∀ r, r₀ ≤ r → Z (r + 1) ≤ Z r
  pageIso : ∀ (r : ℤ) (hr : r₀ ≤ r),
    plainPageObject E r hr ≅ subquotientObject (B r) (Z r) (B_le_Z r hr)

/-- The subobject filtration described in the source exists for every plain
spectral sequence. -/
theorem spectralSequencePageFiltration_exists {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} (E : PlainSpectralSequence C r₀) :
    Nonempty (SpectralSequencePageFiltration E) := by
  sorry

/-- A chosen `Bᵣ/Zᵣ` filtration for a spectral sequence. -/
noncomputable def spectralSequencePageFiltration {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} (E : PlainSpectralSequence C r₀) :
    SpectralSequencePageFiltration E :=
  Classical.choice (spectralSequencePageFiltration_exists E)

/-- Data expressing existence of the union `B∞` and intersection `Z∞`. -/
structure SpectralSequenceLimitData {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} {E : PlainSpectralSequence C r₀}
    (F : SpectralSequencePageFiltration E) where
  Binf : Subobject (plainPageObject E r₀ (by lia))
  Zinf : Subobject (plainPageObject E r₀ (by lia))
  Binf_upper : ∀ r, r₀ ≤ r → F.B r ≤ Binf
  Binf_least : ∀ Y, (∀ r, r₀ ≤ r → F.B r ≤ Y) → Binf ≤ Y
  Zinf_lower : ∀ r, r₀ ≤ r → Zinf ≤ F.Z r
  Zinf_greatest : ∀ Y, (∀ r, r₀ ≤ r → Y ≤ F.Z r) → Y ≤ Zinf
  Binf_le_Zinf : Binf ≤ Zinf

/-- The limit object `E∞ = Z∞/B∞`. -/
noncomputable def spectralSequenceLimit {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} {E : PlainSpectralSequence C r₀}
    (F : SpectralSequencePageFiltration E)
    (L : SpectralSequenceLimitData F) : C :=
  subquotientObject L.Binf L.Zinf L.Binf_le_Zinf

/-- A spectral sequence degenerates at page `r` when all later differentials vanish. -/
def SpectralSequenceDegeneratesAt {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ) : Prop :=
  r₀ ≤ r ∧ ∀ (hr : r₀ ≤ r) (s : ℤ) (hs : r ≤ s),
    plainPageDifferential E s (le_trans hr hs) = 0

theorem degeneratesAt_page_isomorphic {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hE : SpectralSequenceDegeneratesAt E r) (s : ℤ) (hs : r ≤ s) :
    Nonempty (plainPageObject E r hE.1 ≅
      plainPageObject E s (le_trans hE.1 hs)) := by
  sorry

theorem degeneratesAt_limit_exists {C : Type u} [Category.{v} C]
    [Abelian C] {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hE : SpectralSequenceDegeneratesAt E r)
    (F : SpectralSequencePageFiltration E) :
    Nonempty (SpectralSequenceLimitData F) := by
  sorry

/-! ### Translation/shift functors -/

/-- A spectral sequence whose differential lands in a page-dependent
translation of the page.  `Equivalence` is Mathlib's canonical API for an
isomorphism of categories. -/
structure TranslatedSpectralSequence (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] where
  r₀ : ℤ
  translation : ℤ → (C ≌ C)
  page : ℤ → C
  differential : ∀ r, page r ⟶ (translation r).functor.obj (page r)
  d_squared : ∀ r,
    differential r ≫ (translation r).functor.map (differential r) = 0
  next : ∀ r, r₀ ≤ r → Prop

/- The following predicate is the source's page-to-page homology condition;
the explicit homology object is given below. -/
def translatedPreviousDifferential {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (T : C ≌ C) {A : C}
    (d : A ⟶ T.functor.obj A) : T.inverse.obj A ⟶ A :=
  T.inverse.map d ≫ T.unitIso.inv.app A

theorem translatedPreviousDifferential_comp {C : Type u} [Category.{v} C]
    [Abelian C] {T : C ≌ C} {A : C}
    (d : A ⟶ T.functor.obj A)
    (hd : d ≫ T.functor.map d = 0) :
    translatedPreviousDifferential T d ≫ d = 0 := by
  sorry

/-- `Ker(d)/Im(T⁻¹d)` for a translated differential. -/
noncomputable def translatedDifferentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] (T : C ≌ C) {A : C}
    (d : A ⟶ T.functor.obj A) (hd : d ≫ T.functor.map d = 0) : C :=
  cokernel (kernel.lift d (Abelian.image.ι (translatedPreviousDifferential T d))
    (by simpa using translatedPreviousDifferential_comp d hd))

/-! The source's translated spectral-sequence condition is recorded as a
separate structure so that the page-to-page isomorphisms remain explicit. -/
structure TranslatedSpectralSequenceData (C : Type u) [Category.{v} C]
    [Abelian C] extends TranslatedSpectralSequence C where
  nextIso : ∀ (r : ℤ) (_ : r₀ ≤ r),
    translatedDifferentialHomology (translation r) (differential r)
      (d_squared r) ≅ page (r + 1)

/-- The differential condition for a morphism of translated spectral sequences. -/
structure TranslatedSpectralSequenceHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (E E' : TranslatedSpectralSequence C) where
  pageHom : ∀ r, E.page r ⟶ E'.page r
  translation_eq : ∀ r, E.translation r = E'.translation r
  comm : ∀ r,
    E.differential r ≫ (E.translation r).functor.map (pageHom r) ≫
        eqToHom (by rw [translation_eq r]) =
      pageHom r ≫ E'.differential r

end Formalization.Books.Homology.Unit20
