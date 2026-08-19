import Formalization.Books.Homology.Unit20.ExactCouples
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Differential objects

The unshifted definition in the source has no ambient shift functor, so it is
represented by the small source-facing category below.  For shifted objects,
the translation is bundled as a Mathlib category equivalence and the homology
object uses the canonical inverse-shift differential.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.3 Spectral sequences: differential objects -/

/-- An unshifted differential object `(A,d)` with `d² = 0`. -/
structure PlainDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] where
  carrier : C
  d : carrier ⟶ carrier
  d_squared : d ≫ d = 0

/-- A morphism of unshifted differential objects. -/
structure PlainDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (A B : PlainDifferentialObject C) where
  hom : A.carrier ⟶ B.carrier
  comm : A.d ≫ hom = hom ≫ B.d

@[ext] theorem plainDifferentialObjectHom_ext {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {A B : PlainDifferentialObject C}
    {f g : PlainDifferentialObjectHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance plainDifferentialObjectCategory {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] : Category (PlainDifferentialObject C) where
  Hom A B := PlainDifferentialObjectHom A B
  id A := { hom := 𝟙 A.carrier, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc] }
  id_comp := by
    intro A B f
    apply plainDifferentialObjectHom_ext
    simp
  comp_id := by
    intro A B f
    apply plainDifferentialObjectHom_ext
    simp
  assoc := by
    intro A B D E f g h
    apply plainDifferentialObjectHom_ext
    simp [Category.assoc]

instance plainDifferentialObjectZeroMorphisms {C : Type u} [Category.{v} C]
    [Preadditive C] : HasZeroMorphisms (PlainDifferentialObject C) where
  zero := fun A B => ⟨{ hom := 0, comm := by simp }⟩
  comp_zero := by
    intro A B f D
    apply plainDifferentialObjectHom_ext
    change f.hom ≫ 0 = 0
    simp
  zero_comp := by
    intro A B D f
    apply plainDifferentialObjectHom_ext
    change 0 ≫ f.hom = 0
    simp

private def plainDifferentialObjectFunctor {C : Type u} [Category.{v} C]
    [Abelian C] : PlainDifferentialObject C ⥤
      HomologicalComplex C (ComplexShape.refl PUnit.{1}) where
  obj A :=
    { X := fun _ => A.carrier
      d := fun _ _ => A.d
      d_comp_d' := by
        intro i j k hij hjk
        exact A.d_squared }
  map f :=
    { f := fun _ => f.hom
      comm' := by
        intro i j hij
        exact f.comm.symm }
  map_id := by
    intro A
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  map_comp := by
    intro A B D f g
    apply HomologicalComplex.hom_ext
    intro i
    rfl

private noncomputable def plainDifferentialLeftHomologyData
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : PlainDifferentialObject C) :
    (((plainDifferentialObjectFunctor (C := C)).obj A).sc PUnit.unit).LeftHomologyData := by
  let d := A.d
  have hd : d ≫ d = 0 := by
    simpa [d] using A.d_squared
  let k₀ : A.carrier ⟶ kernel d := kernel.lift d d hd
  let k : Abelian.image d ⟶ kernel d :=
    kernel.lift d (Abelian.image.ι d) (by
      apply (cancel_epi (Abelian.factorThruImage d)).1
      simp only [← Category.assoc, Abelian.image.fac, hd, comp_zero, zero_comp])
  have hk : k₀ = Abelian.factorThruImage d ≫ k := by
    apply (cancel_mono (kernel.ι d)).1
    simp [k, k₀, Category.assoc, Abelian.image.fac]
  let π : kernel d ⟶ cokernel k := cokernel.π k
  have wπ : k₀ ≫ π = 0 := by
    rw [hk, Category.assoc, cokernel.condition, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ π wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun x hx => cokernel.desc k x (by
        apply (cancel_epi (Abelian.factorThruImage d)).1
        simp only [← Category.assoc, ← hk, hx, comp_zero]))
      (fun x hx => by exact cokernel.π_desc _ _ _)
      (fun x hx b hb => by
        apply (cancel_epi π).1
        rw [hb, cokernel.π_desc])
  exact
    { K := kernel d
      H := cokernel k
      i := kernel.ι d
      π := π
      wi := kernel.condition d
      hi := kernelIsKernel d
      wπ := wπ
      hπ := hπ }

/-- The source's assertion that the category of differential objects is
abelian. -/
theorem plainDifferentialObject_abelian {C : Type u} [Category.{v} C]
    [Abelian C] : Nonempty (Abelian (PlainDifferentialObject C)) := by
  let F := plainDifferentialObjectFunctor (C := C)
  let _ : F.Faithful := ⟨by
    intro A B f g h
    apply plainDifferentialObjectHom_ext
    have h' := congrArg (fun k => k.f PUnit.unit) h
    exact h'⟩
  let _ : F.Full := ⟨by
    intro A B f
    refine ⟨{ hom := f.f PUnit.unit, comm := (f.comm _ _).symm }, ?_⟩
    apply HomologicalComplex.hom_ext
    intro i
    cases i
    rfl⟩
  let _ : F.EssSurj := Functor.EssSurj.mk (by
    intro K
    let A : PlainDifferentialObject C :=
      { carrier := K.X PUnit.unit
        d := K.d PUnit.unit PUnit.unit
        d_squared := K.d_comp_d _ _ _ }
    refine ⟨A, Nonempty.intro ?_⟩
    let hom : F.obj A ⟶ K :=
      { f := fun i => 𝟙 (K.X i)
        comm' := by
          intro i j hij
          simp [F, plainDifferentialObjectFunctor, A] }
    let inv : K ⟶ F.obj A :=
      { f := fun i => 𝟙 (K.X i)
        comm' := by
          intro i j hij
          simp [F, plainDifferentialObjectFunctor, A] }
    refine { hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
    · apply HomologicalComplex.hom_ext
      intro i
      cases i
      simp [hom, inv, F, plainDifferentialObjectFunctor, A]
    · apply HomologicalComplex.hom_ext
      intro i
      cases i
      simp [hom, inv, F, plainDifferentialObjectFunctor, A])
  let _ : F.IsEquivalence :=
    { full := inferInstance
      faithful := inferInstance
      essSurj := inferInstance }
  letI : Preadditive (PlainDifferentialObject C) :=
    Preadditive.ofFullyFaithful (Functor.FullyFaithful.ofFullyFaithful F)
  let _ : HasFiniteProducts (PlainDifferentialObject C) :=
    ⟨fun n => Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact ⟨CategoryTheory.abelianOfEquivalence F⟩

noncomputable instance plainDifferentialObjectAbelian {C : Type u} [Category.{v} C]
    [Abelian C] : Abelian (PlainDifferentialObject C) :=
  Classical.choice (plainDifferentialObject_abelian (C := C))

/-- The homology object `H(A,d) = Ker(d)/Im(d)`. -/
abbrev plainDifferentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : PlainDifferentialObject C) : C :=
  differentialHomology A.d A.d_squared

private noncomputable def plainDifferentialHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : PlainDifferentialObject C) :
    (((plainDifferentialObjectFunctor (C := C)).obj A).homology PUnit.unit) ≅
      plainDifferentialHomology A :=
  (plainDifferentialLeftHomologyData A).homologyIso

/-- A short exact sequence of differential objects. -/
structure PlainDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : PlainDifferentialObject C) where
  f : PlainDifferentialObjectHom A B
  g : PlainDifferentialObjectHom B D
  complex : f.hom ≫ g.hom = 0
  exact : (ShortComplex.mk f.hom g.hom complex).ShortExact

/-- A long exact sequence interface, indexed by the integers. -/
structure LongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (X : ℤ → C) where
  differential : ∀ n, X n ⟶ X (n + 1)
  complex : ∀ n, differential n ≫ differential (n + 1) = 0
  exact : ∀ n,
    (ShortComplex.mk (differential n) (differential (n + 1)) (complex n)).Exact

def differentialHomologyLongTerm {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : PlainDifferentialObject C) (n : ℤ) : C :=
  if n % 3 = 0 then plainDifferentialHomology D
  else if n % 3 = 1 then plainDifferentialHomology A
  else plainDifferentialHomology B

theorem plainDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : PlainDifferentialObject C}
    (S : PlainDifferentialShortExact A B D) :
    Nonempty (LongExactSequence (differentialHomologyLongTerm A B D)) := by
  let F := plainDifferentialObjectFunctor (C := C)
  let T : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
    ShortComplex.mk (F.map S.f) (F.map S.g) (by
      apply HomologicalComplex.hom_ext
      intro i
      cases i
      dsimp [F, plainDifferentialObjectFunctor]
      exact S.complex)
  have hMono : Mono T.f := by
    dsimp [T]
    apply HomologicalComplex.mono_of_mono_f
    intro i
    cases i
    exact S.exact.mono_f
  have hEpi : Epi T.g := by
    dsimp [T]
    apply HomologicalComplex.epi_of_epi_f
    intro i
    cases i
    exact S.exact.epi_g
  have hExact : T.Exact :=
    HomologicalComplex.exact_of_degreewise_exact T (fun i => by
      cases i
      change (ShortComplex.mk S.f.hom S.g.hom S.complex).Exact
      exact S.exact.exact)
  have hT : T.ShortExact := { mono_f := hMono, epi_g := hEpi, exact := hExact }
  let eA := plainDifferentialHomologyIso A
  let eB := plainDifferentialHomologyIso B
  let eD := plainDifferentialHomologyIso D
  let δ := hT.δ PUnit.unit PUnit.unit (by rfl)
  let hf := HomologicalComplex.homologyMap T.f PUnit.unit
  let hg := HomologicalComplex.homologyMap T.g PUnit.unit
  let b : plainDifferentialHomology D ⟶ plainDifferentialHomology A :=
    eD.inv ≫ δ ≫ eA.hom
  let f : plainDifferentialHomology A ⟶ plainDifferentialHomology B :=
    eA.inv ≫ hf ≫ eB.hom
  let g : plainDifferentialHomology B ⟶ plainDifferentialHomology D :=
    eB.inv ≫ hg ≫ eD.hom
  let L : ℤ → C := fun n =>
    if n % 3 = 0 then plainDifferentialHomology D
    else if n % 3 = 1 then plainDifferentialHomology A
    else plainDifferentialHomology B
  let differential : ∀ (n : ℤ), L n ⟶ L (n + 1) := fun n => by
    by_cases h0 : n % 3 = 0
    · have h1 : (n + 1) % 3 = 1 := by omega
      have hn0 : (n + 1) % 3 ≠ 0 := by omega
      have u0 : L n = plainDifferentialHomology D := by
        dsimp [L]
        rw [if_pos h0]
      have u1 : L (n + 1) = plainDifferentialHomology A := by
        dsimp [L]
        rw [if_neg hn0, if_pos h1]
      exact eqToHom u0 ≫ b ≫ eqToHom u1.symm
    · by_cases h1 : n % 3 = 1
      · have h2 : (n + 1) % 3 = 2 := by omega
        have hn0 : (n + 1) % 3 ≠ 0 := by omega
        have hn1 : (n + 1) % 3 ≠ 1 := by omega
        have u0 : L n = plainDifferentialHomology A := by
          dsimp [L]
          rw [if_neg h0, if_pos h1]
        have u1 : L (n + 1) = plainDifferentialHomology B := by
          dsimp [L]
          rw [if_neg hn0, if_neg hn1]
        exact eqToHom u0 ≫ f ≫ eqToHom u1.symm
      · have h2 : n % 3 = 2 := by omega
        have hn0 : (n + 1) % 3 = 0 := by omega
        have u0 : L n = plainDifferentialHomology B := by
          dsimp [L]
          rw [if_neg h0, if_neg h1]
        have u1 : L (n + 1) = plainDifferentialHomology D := by
          dsimp [L]
          rw [if_pos hn0]
        exact eqToHom u0 ≫ g ≫ eqToHom u1.symm
  have hL : Nonempty (LongExactSequence L) := by
    refine ⟨{ differential := differential, complex := ?_, exact := ?_ }⟩
    · intro n
      dsimp [L]
      by_cases h0 : n % 3 = 0
      · have h1 : (n + 1) % 3 = 1 := by omega
        have h2 : (n + 1 + 1) % 3 = 2 := by omega
        have hn0 : (n + 1) % 3 ≠ 0 := by omega
        simp only [differential, dif_pos h0, dif_neg hn0, dif_pos h1,
          if_pos h0, if_neg hn0, if_pos h1]
        simp [b, f]
        have hδ : δ ≫ hf = 0 := by
          dsimp [δ, hf]
          exact hT.δ_comp PUnit.unit PUnit.unit (by rfl)
        rw [← Category.assoc, ← Category.assoc, hδ]
        simp
      · by_cases h1 : n % 3 = 1
        · have h2 : (n + 1) % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 ≠ 0 := by omega
          have hn1 : (n + 1) % 3 ≠ 1 := by omega
          simp only [differential, dif_neg h0, dif_pos h1, dif_neg hn0, dif_neg hn1,
            dif_pos h2, if_neg h0, if_pos h1, if_neg hn0, if_neg hn1, if_pos h2]
          simp [f, g]
          have hfg : hf ≫ hg = 0 := by
            dsimp [hf, hg]
            rw [← HomologicalComplex.homologyMap_comp]
            simp [T]
          rw [← Category.assoc, ← Category.assoc, hfg]
          simp
        · have h2 : n % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 = 0 := by omega
          simp only [differential, dif_neg h0, dif_neg h1, dif_pos hn0,
            if_neg h0, if_neg h1, if_pos hn0]
          simp [g, b]
          have hgd : hg ≫ δ = 0 := by
            dsimp [hg, δ]
            exact hT.comp_δ PUnit.unit PUnit.unit (by rfl)
          rw [← Category.assoc, ← Category.assoc, hgd]
          simp
    · intro n
      dsimp [L]
      by_cases h0 : n % 3 = 0
      · have h1 : (n + 1) % 3 = 1 := by omega
        simp only [differential, dif_pos h0, dif_neg (by omega : (n + 1) % 3 ≠ 0),
          dif_pos h1, if_pos h0, if_neg (by omega : (n + 1) % 3 ≠ 0), if_pos h1]
        simp [b, f]
        exact ShortComplex.exact_of_iso
          (ShortComplex.isoMk eD eA eB (by simp [b, δ]) (by simp [f, hf]))
          (hT.homology_exact₁ PUnit.unit PUnit.unit (by rfl))
      · by_cases h1 : n % 3 = 1
        · have h2 : (n + 1) % 3 = 2 := by omega
          simp only [differential, dif_neg h0, dif_pos h1,
            dif_neg (by omega : (n + 1) % 3 ≠ 0),
            dif_neg (by omega : (n + 1) % 3 ≠ 1), dif_pos h2,
            if_neg h0, if_pos h1, if_neg (by omega : (n + 1) % 3 ≠ 0),
            if_neg (by omega : (n + 1) % 3 ≠ 1), if_pos h2]
          simp [f, g]
          exact ShortComplex.exact_of_iso
            (ShortComplex.isoMk eA eB eD (by simp [f, hf]) (by simp [g, hg]))
            (hT.homology_exact₂ PUnit.unit)
        · have h2 : n % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 = 0 := by omega
          simp only [differential, dif_neg h0, dif_neg h1, dif_pos hn0,
            if_neg h0, if_neg h1, if_pos hn0]
          simp [g, b]
          exact ShortComplex.exact_of_iso
            (ShortComplex.isoMk eB eD eA (by simp [g, hg]) (by simp [b, δ]))
            (hT.homology_exact₃ PUnit.unit PUnit.unit (by rfl))
  simpa [L, differentialHomologyLongTerm] using hL

/-! ### The injective self-map example -/

/-- An injective endomorphism of a differential object. -/
structure PlainDifferentialInjectiveEndomorphism {C : Type u} [Category.{v} C]
    [Abelian C] (A : PlainDifferentialObject C) where
  hom : PlainDifferentialObjectHom A A
  injective : Mono hom.hom

structure QuotientDifferentialMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) where
  differential : cokernel α.hom.hom ⟶ cokernel α.hom.hom
  square_zero : differential ≫ differential = 0
  induced : cokernel.π α.hom.hom ≫ differential =
    A.d ≫ cokernel.π α.hom.hom

theorem quotientDifferentialMap_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (QuotientDifferentialMapData α) := by
  let q := cokernel.π α.hom.hom
  let dQ : cokernel α.hom.hom ⟶ cokernel α.hom.hom :=
    cokernel.desc α.hom.hom (A.d ≫ q) (by
      rw [← Category.assoc, ← α.hom.comm, Category.assoc, cokernel.condition,
        comp_zero])
  have hq : q ≫ dQ = A.d ≫ q := by
    dsimp [dQ]
    simp
  refine ⟨{ differential := dQ, square_zero := ?_, induced := hq }⟩
  apply (cancel_epi q).1
  rw [← Category.assoc, hq, Category.assoc, hq, ← Category.assoc,
    A.d_squared, zero_comp]

noncomputable def quotientDifferentialMapData
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    QuotientDifferentialMapData α :=
  Classical.choice (quotientDifferentialMap_exists α)

noncomputable def quotientDifferentialMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    cokernel α.hom.hom ⟶ cokernel α.hom.hom :=
  (quotientDifferentialMapData α).differential

/-- The differential object `(A/alpha A,d)` from the self-map example. -/
def quotientDifferentialObject
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : PlainDifferentialObject C where
  carrier := cokernel α.hom.hom
  d := quotientDifferentialMap α
  d_squared := (quotientDifferentialMapData α).square_zero

def differentialSelfMapShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    PlainDifferentialShortExact A A (quotientDifferentialObject α) where
  f := α.hom
  g := { hom := cokernel.π α.hom.hom
         comm := (quotientDifferentialMapData α).induced.symm }
  complex := cokernel.condition _
  exact := by
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)

theorem differentialSelfMap_exactCouple_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α))) := by
  sorry

noncomputable def differentialSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α)) :=
  Classical.choice (differentialSelfMap_exactCouple_exists α)

noncomputable def differentialSelfMapAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : PlainSpectralSequence C 1 :=
  exactCoupleAssociatedSpectralSequence (differentialSelfMapExactCouple α)

theorem differentialSelfMap_E1
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (plainPageObject (differentialSelfMapAssociatedSpectralSequence α) 1 ≅
      plainDifferentialHomology (quotientDifferentialObject α)) := by
  sorry

/-- The separately numbered zeroth page in the self-map example. -/
abbrev differentialSelfMapE₀
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : C :=
  (quotientDifferentialObject α).carrier

abbrev differentialSelfMapD₀
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    differentialSelfMapE₀ α ⟶ differentialSelfMapE₀ α :=
  (quotientDifferentialObject α).d

theorem differentialSelfMap_starting_at_zero_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (PlainSpectralSequence C 0) := by
  sorry

def selfMapAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : ℕ →
      (A.carrier ⟶ A.carrier)
  | 0 => 𝟙 A.carrier
  | n + 1 => selfMapAlphaPow α n ≫ α.hom.hom

def selfMapBoundaryPreimage {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  if r = 0 then ⊥ else
    (Subobject.pullback (selfMapAlphaPow α (r - 1))).obj
      ((Subobject.«exists» A.d).obj ⊤)

def selfMapCyclePreimage {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  if r = 0 then ⊤ else
    (Subobject.pullback A.d).obj
      ((Subobject.«exists» (selfMapAlphaPow α r)).obj ⊤)

theorem selfMap_boundary_preimage_le_cycle_preimage
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundaryPreimage α r ≤ selfMapCyclePreimage α r := by
  sorry

noncomputable def selfMapQuotientImageSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Q : C} (π : X ⟶ Q) (B : Subobject X) : Subobject Q :=
  Subobject.mk (Abelian.image.ι (B.arrow ≫ π))

noncomputable def selfMapBoundaryPlus {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapBoundaryPreimage α r)

noncomputable def selfMapCyclePlus {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapCyclePreimage α r)

theorem selfMap_boundary_plus_le_cycle_plus
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundaryPlus α r ≤ selfMapCyclePlus α r := by
  /- prior attempt: exact sup_le_sup
      (selfMap_boundary_preimage_le_cycle_preimage α r) le_rfl -/
  sorry

def selfMapBoundarySubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapBoundaryPreimage α r)

def selfMapCycleSubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapCyclePreimage α r)

theorem selfMap_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundarySubobject α r ≤ selfMapCycleSubobject α r := by
  sorry

noncomputable def selfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : C :=
  if r = 0 then differentialSelfMapE₀ α else
    subquotientObject (selfMapBoundaryPlus α r) (selfMapCyclePlus α r)
      (selfMap_boundary_plus_le_cycle_plus α r)

noncomputable def selfMapPageClassOfCycle
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ)
    {T : C} (z : T ⟶ (selfMapCyclePlus α r : C)) :
    T ⟶ selfMapPageComponent α r :=
  by
    by_cases hr : r = 0
    · subst r
      exact (z ≫ (selfMapCyclePlus α 0).arrow) ≫ eqToHom (by rfl)
    · exact (z ≫ cokernel.π (Subobject.ofLE (selfMapBoundaryPlus α r)
        (selfMapCyclePlus α r) (selfMap_boundary_plus_le_cycle_plus α r))) ≫
        eqToHom (by simp [selfMapPageComponent, hr, subquotientObject])

/-- The lift rule for the self-map spectral sequence, expressed on test-object
morphisms so it also makes sense in an arbitrary abelian category. -/
structure SelfMapPageDifferentialRule {C : Type u} [Category.{v} C]
    [Abelian C] {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) where
  differential : selfMapPageComponent α r ⟶ selfMapPageComponent α r
  differential_squared : differential ≫ differential = 0
  rule : ∀ {T : C}
    (z : T ⟶ (selfMapCyclePlus α r : C))
    (y : T ⟶ A.carrier)
    (yCycle : T ⟶ (selfMapCyclePlus α r : C))
    (_hy : yCycle ≫ (selfMapCyclePlus α r).arrow =
      y ≫ cokernel.π α.hom.hom)
    (_h : z ≫ (selfMapCyclePlus α r).arrow ≫ differentialSelfMapD₀ α =
      y ≫ selfMapAlphaPow α r ≫ cokernel.π α.hom.hom),
    selfMapPageClassOfCycle α r z ≫ differential =
      selfMapPageClassOfCycle α r yCycle

theorem selfMap_page_differential_rule_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Nonempty (SelfMapPageDifferentialRule α r) := by
  sorry

/- The warning in the source is recorded as two named assertions rather than
silently adding either false inclusion as a hypothesis. -/
def selfMapAlphaSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (hα : Mono α.hom.hom) :
    Subobject A.carrier :=
  letI := hα
  Subobject.mk α.hom.hom

def selfMapWarningBoundaryInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : Prop :=
  selfMapAlphaSubobject α α.injective ≤ selfMapBoundaryPreimage α r

def selfMapWarningCycleInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : Prop :=
  selfMapAlphaSubobject α α.injective ≤ selfMapCyclePreimage α r

theorem selfMap_page_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapPageComponent α r =
      if r = 0 then differentialSelfMapE₀ α else
        subquotientObject (selfMapBoundaryPlus α r)
          (selfMapCyclePlus α r) (selfMap_boundary_plus_le_cycle_plus α r) := rfl

/-! ### Shifted differential objects -/

/-- A differential object with differential `A ⟶ S A`. -/
structure ShiftedDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (S : C ≌ C) where
  carrier : C
  d : carrier ⟶ S.functor.obj carrier
  d_squared : d ≫ S.functor.map d = 0

/-- A morphism of shifted differential objects. -/
structure ShiftedDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    (A B : ShiftedDifferentialObject C S) where
  hom : A.carrier ⟶ B.carrier
  comm : A.d ≫ S.functor.map hom = hom ≫ B.d

@[ext] theorem shiftedDifferentialObjectHom_ext {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    {A B : ShiftedDifferentialObject C S}
    {f g : ShiftedDifferentialObjectHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance shiftedDifferentialObjectCategory {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C} :
    Category (ShiftedDifferentialObject C S) where
  Hom A B := ShiftedDifferentialObjectHom A B
  id A := { hom := 𝟙 A.carrier, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [S.functor.map_comp, ← Category.assoc, f.comm, Category.assoc, g.comm,
          Category.assoc] }
  id_comp := by
    intro A B f
    apply shiftedDifferentialObjectHom_ext
    simp
  comp_id := by
    intro A B f
    apply shiftedDifferentialObjectHom_ext
    simp
  assoc := by
    intro A B D E f g h
    apply shiftedDifferentialObjectHom_ext
    simp [Category.assoc]

abbrev shiftedDifferentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) : C :=
  translatedDifferentialHomology S A.d A.d_squared

def shiftedDifferentialObjectShift {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObject C S where
  carrier := S.functor.obj A.carrier
  d := S.functor.map A.d
  d_squared := by
    rw [← S.functor.map_comp, A.d_squared, S.functor.map_zero]

theorem shiftedDifferentialHomology_shift_iso {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) :
    Nonempty (shiftedDifferentialHomology (shiftedDifferentialObjectShift S A) ≅
      S.functor.obj (shiftedDifferentialHomology A)) := by
  sorry

structure ShiftedDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C}
    (A B D : ShiftedDifferentialObject C S) where
  f : ShiftedDifferentialObjectHom A B
  g : ShiftedDifferentialObjectHom B D
  complex : f.hom ≫ g.hom = 0
  exact : (ShortComplex.mk f.hom g.hom complex).ShortExact

structure ShiftedLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (X : ℤ → C) where
  differential : ∀ n, X n ⟶ X (n + 1)
  complex : ∀ n, differential n ≫ differential (n + 1) = 0
  exact : ∀ n,
    (ShortComplex.mk (differential n) (differential (n + 1)) (complex n)).Exact

theorem shiftedDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    {A B D : ShiftedDifferentialObject C S}
    (Q : ShiftedDifferentialShortExact A B D) :
    ∃ X : ℤ → C, Nonempty (ShiftedLongExactSequence S X) := by
  sorry

theorem shiftedDifferentialObject_abelian {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} :
    Nonempty (Abelian (ShiftedDifferentialObject C S)) := by
  sorry

noncomputable instance shiftedDifferentialObjectAbelian {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} : Abelian (ShiftedDifferentialObject C S) :=
  Classical.choice (shiftedDifferentialObject_abelian (C := C) (S := S))

/- The shift-family variant in the source is represented by a commuting pair
of equivalences and a shifted injective self-map. -/
structure ShiftedSelfMapData (C : Type u) [Category.{v} C]
    [Abelian C] (S T : C ≌ C) where
  commute : T.functor ⋙ S.functor = S.functor ⋙ T.functor
  A : ShiftedDifferentialObject C S
  targetDifferential : T.inverse.obj A.carrier ⟶ S.functor.obj (T.inverse.obj A.carrier)
  target_d_squared : targetDifferential ≫ S.functor.map targetDifferential = 0
  alpha : ShiftedDifferentialObjectHom A
    { carrier := T.inverse.obj A.carrier
      d := targetDifferential
      d_squared := target_d_squared }
  injective : Mono alpha.hom
  quotientDifferential :
    cokernel alpha.hom ⟶ S.functor.obj (cokernel alpha.hom)
  quotient_d_squared :
    quotientDifferential ≫ S.functor.map quotientDifferential = 0
  quotient_induced :
    cokernel.π alpha.hom ≫ quotientDifferential =
      targetDifferential ≫ S.functor.map (cokernel.π alpha.hom)

def shiftedSelfMapQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    ShiftedDifferentialObject C S where
  carrier := cokernel D.alpha.hom
  d := D.quotientDifferential
  d_squared := D.quotient_d_squared

theorem shiftedSelfMap_exact_couple_exists {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    Nonempty (ShiftedExactCouple C (T.trans S) T
      (shiftedDifferentialHomology D.A)
      (S.inverse.obj (shiftedDifferentialHomology (shiftedSelfMapQuotient D)))) := by
  sorry

theorem shiftedSelfMap_spectral_sequence {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    ∃ X : TranslatedSpectralSequenceData C,
      X.r₀ = 1 ∧ Nonempty (X.page 1 ≅
        S.inverse.obj (shiftedDifferentialHomology (shiftedSelfMapQuotient D))) := by
  sorry

end Formalization.Books.Homology.Unit20
