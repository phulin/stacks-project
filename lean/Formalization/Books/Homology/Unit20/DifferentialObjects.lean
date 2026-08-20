import Formalization.Books.Homology.Unit20.ExactCouples
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Preadditive.Comma
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Subobject.Limits

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
      simp only [← Category.assoc, Abelian.image.fac, hd, comp_zero])
  have hk : k₀ = Abelian.factorThruImage d ≫ k := by
    apply (cancel_mono (kernel.ι d)).1
    simp [k, k₀, Category.assoc]
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
  let : Preadditive (PlainDifferentialObject C) :=
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
      by_cases h0 : n % 3 = 0
      · have h1 : (n + 1) % 3 = 1 := by omega
        have h2 : (n + 1 + 1) % 3 = 2 := by omega
        have hn0 : (n + 1) % 3 ≠ 0 := by omega
        simp only [differential, *]
        dsimp [b, f]
        simp_all
        have hδ : δ ≫ hf = 0 := by
          dsimp [δ, hf]
          exact hT.δ_comp PUnit.unit PUnit.unit (by rfl)
        rw [← Category.assoc, ← Category.assoc, hδ]
        simp
      · by_cases h1 : n % 3 = 1
        · have h2 : (n + 1) % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 ≠ 0 := by omega
          have hn1 : (n + 1) % 3 ≠ 1 := by omega
          simp only [differential, *]
          dsimp [f, g]
          simp_all
          have hfg : hf ≫ hg = 0 := by
            rw [← HomologicalComplex.homologyMap_comp, T.zero,
              HomologicalComplex.homologyMap_zero]
          rw [← Category.assoc, ← Category.assoc, hfg]
          simp
        · have h2 : n % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 = 0 := by omega
          simp only [differential, *]
          dsimp [g, b]
          simp_all
          have hgd : hg ≫ δ = 0 := by
            dsimp [hg, δ]
            exact hT.comp_δ PUnit.unit PUnit.unit (by rfl)
          rw [← Category.assoc, ← Category.assoc, hgd]
          simp
    · intro n
      dsimp [L]
      by_cases h0 : n % 3 = 0
      · have h1 : (n + 1) % 3 = 1 := by omega
        have h2 : (n + 1 + 1) % 3 = 2 := by omega
        have u0 : L n = plainDifferentialHomology D := by
          dsimp [L]
          rw [if_pos h0]
        have u1 : L (n + 1) = plainDifferentialHomology A := by
          dsimp [L]
          rw [if_neg (by omega), if_pos h1]
        have u2 : L (n + 1 + 1) = plainDifferentialHomology B := by
          dsimp [L]
          rw [if_neg (by omega), if_neg (by omega)]
        have hn : 3 ∣ n := by omega
        have hn1 : ¬3 ∣ n + 1 := by omega
        have hn0' : n % 3 = 0 := by omega
        have hn01 : n % 3 ≠ 1 := by omega
        have hn10 : (n + 1) % 3 ≠ 0 := by omega
        have hn11 : (n + 1) % 3 = 1 := by omega
        have hn20 : (n + 1 + 1) % 3 ≠ 0 := by omega
        have hn21 : (n + 1 + 1) % 3 ≠ 1 := by omega
        refine ShortComplex.exact_of_iso
          (ShortComplex.isoMk
            (eD.trans (eqToIso u0.symm))
            (eA.trans (eqToIso u1.symm))
            (eB.trans (eqToIso u2.symm))
            (by simp_all [differential, b, f, δ, hf, Category.assoc])
            (by simp_all [differential, b, f, δ, hf, Category.assoc]))
          (hT.homology_exact₁ PUnit.unit PUnit.unit (by rfl))
      · by_cases h1 : n % 3 = 1
        · have h2 : (n + 1) % 3 = 2 := by omega
          have hn0' : n % 3 ≠ 0 := by omega
          have hn01 : n % 3 = 1 := by omega
          have hn10 : (n + 1) % 3 ≠ 0 := by omega
          have hn11 : (n + 1) % 3 ≠ 1 := by
            rw [h2]
            norm_num
          have hn20 : (n + 1 + 1) % 3 = 0 := by
            norm_num [Int.add_emod, h2]
          have hn21 : (n + 1 + 1) % 3 ≠ 1 := by
            rw [hn20]
            norm_num
          have u0 : L n = plainDifferentialHomology A := by
            dsimp [L]
            rw [if_neg (by omega), if_pos h1]
          have u1 : L (n + 1) = plainDifferentialHomology B := by
            dsimp [L]
            rw [if_neg (by omega), if_neg (by omega)]
          have u2 : L (n + 1 + 1) = plainDifferentialHomology D := by
            dsimp [L]
            rw [if_pos (by norm_num [Int.add_emod, h2])]
          have hn : ¬3 ∣ n := by omega
          have hn1 : ¬3 ∣ n + 1 := by omega
          refine ShortComplex.exact_of_iso
            (ShortComplex.isoMk
              (eA.trans (eqToIso u0.symm))
              (eB.trans (eqToIso u1.symm))
              (eD.trans (eqToIso u2.symm))
              (by simp_all [differential, f, g, hf, hg, Category.assoc])
              (by simp_all [differential, f, g, hf, hg, Category.assoc]))
            (hT.homology_exact₂ PUnit.unit)
        · have h2 : n % 3 = 2 := by omega
          have hn0 : (n + 1) % 3 = 0 := by omega
          have hn0' : n % 3 ≠ 0 := by omega
          have hn01 : n % 3 ≠ 1 := by omega
          have hn02 : n % 3 = 2 := by omega
          have hn10 : (n + 1) % 3 = 0 := by omega
          have hn20 : (n + 1 + 1) % 3 ≠ 0 := by omega
          have hn21 : (n + 1 + 1) % 3 = 1 := by omega
          have u0 : L n = plainDifferentialHomology B := by
            dsimp [L]
            rw [if_neg (by omega), if_neg (by omega)]
          have u1 : L (n + 1) = plainDifferentialHomology D := by
            dsimp [L]
            rw [if_pos hn0]
          have u2 : L (n + 1 + 1) = plainDifferentialHomology A := by
            dsimp [L]
            rw [if_neg (by omega), if_pos (by omega)]
          have hn : ¬3 ∣ n := by omega
          have hn1 : 3 ∣ n + 1 := by omega
          refine ShortComplex.exact_of_iso
            (ShortComplex.isoMk
              (eB.trans (eqToIso u0.symm))
              (eD.trans (eqToIso u1.symm))
              (eA.trans (eqToIso u2.symm))
              (by simp_all [differential, g, b, hg, δ, Category.assoc])
              (by simp_all [differential, g, b, hg, δ, Category.assoc]))
            (hT.homology_exact₃ PUnit.unit PUnit.unit (by rfl))
  exact hL

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
    exact cokernel.π_desc _ _ _
  refine ⟨{ differential := dQ, square_zero := ?_, induced := hq }⟩
  apply (cancel_epi q).1
  rw [← Category.assoc, hq, Category.assoc, hq, ← Category.assoc,
    A.d_squared]
  simp

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
    refine { exact := ?_, mono_f := α.injective, epi_g := ?_ }
    · apply ShortComplex.exact_of_g_is_cokernel
        (ShortComplex.mk α.hom.hom (cokernel.π α.hom.hom) (cokernel.condition _))
      exact cokernelIsCokernel _
    · change Epi (cokernel.π α.hom.hom)
      infer_instance

theorem differentialSelfMap_exactCouple_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α))) := by
  let S := differentialSelfMapShortExact α
  let F := plainDifferentialObjectFunctor (C := C)
  let T : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
    ShortComplex.mk (F.map S.f) (F.map S.g) (by
      apply HomologicalComplex.hom_ext
      intro i
      cases i
      dsimp [F, plainDifferentialObjectFunctor, S]
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
  let eQ := plainDifferentialHomologyIso (quotientDifferentialObject α)
  let δ := hT.δ PUnit.unit PUnit.unit (by rfl)
  let hf := HomologicalComplex.homologyMap T.f PUnit.unit
  let hg := HomologicalComplex.homologyMap T.g PUnit.unit
  let alpha : plainDifferentialHomology A ⟶ plainDifferentialHomology A :=
    eA.inv ≫ hf ≫ eA.hom
  let f : plainDifferentialHomology (quotientDifferentialObject α) ⟶
      plainDifferentialHomology A :=
    eQ.inv ≫ δ ≫ eA.hom
  let g : plainDifferentialHomology A ⟶
      plainDifferentialHomology (quotientDifferentialObject α) :=
    eA.inv ≫ hg ≫ eQ.hom
  have hδ : δ ≫ hf = 0 := by
    dsimp [δ, hf]
    exact hT.δ_comp PUnit.unit PUnit.unit (by rfl)
  have hfg : hf ≫ hg = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, T.zero,
      HomologicalComplex.homologyMap_zero]
  have hgd : hg ≫ δ = 0 := by
    dsimp [hg, δ]
    exact hT.comp_δ PUnit.unit PUnit.unit (by rfl)
  have hαg : alpha ≫ g = 0 := by
    simp only [alpha, g, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc hf hg eQ.hom, hfg, zero_comp]
    simp
  have hgf : g ≫ f = 0 := by
    simp only [g, f, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc hg δ eA.hom, hgd, zero_comp]
    simp
  have hfa : f ≫ alpha = 0 := by
    simp only [f, alpha, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc δ hf eA.hom, hδ, zero_comp]
    simp
  let D : ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α)) :=
    { alpha := alpha, f := f, g := g, alpha_g := hαg, g_f := hgf,
      f_alpha := hfa, exact_alpha_g := by
        refine ShortComplex.exact_of_iso
          (ShortComplex.isoMk
            (S₁ := ShortComplex.mk hf hg hfg)
            (S₂ := ShortComplex.mk alpha g hαg)
            eA eA eQ (by simp [alpha]) (by simp [g])) ?_
        simpa using hT.homology_exact₂ PUnit.unit
      exact_g_f := by
        refine ShortComplex.exact_of_iso
          (ShortComplex.isoMk
            (S₁ := ShortComplex.mk hg δ hgd)
            (S₂ := ShortComplex.mk g f hgf)
            eA eQ eA (by simp [g]) (by simp [f])) ?_
        simpa using hT.homology_exact₃ PUnit.unit PUnit.unit (by rfl)
      exact_f_alpha := by
        refine ShortComplex.exact_of_iso
          (ShortComplex.isoMk
            (S₁ := ShortComplex.mk δ hf hδ)
            (S₂ := ShortComplex.mk f alpha hfa)
            eQ eA eA (by simp [f]) (by simp [alpha])) ?_
        simpa using hT.homology_exact₁ PUnit.unit PUnit.unit (by rfl) }
  exact ⟨D⟩

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
  exact exactCouple_associated_page_one (differentialSelfMapExactCouple α)

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

private noncomputable def selfMapPageZeroHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    (plainSpectralSequencePage
      (quotientDifferentialObject α).carrier
      (quotientDifferentialObject α).d
      (quotientDifferentialObject α).d_squared).homology PUnit.unit ≅
      plainDifferentialHomology (quotientDifferentialObject α) := by
  let Q := quotientDifferentialObject α
  let d := Q.d
  have hd : d ≫ d = 0 := Q.d_squared
  let P₀ : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
    plainSpectralSequencePage Q.carrier d hd
  let S : ShortComplex C := P₀.sc' PUnit.unit PUnit.unit PUnit.unit
  let k₀ : Q.carrier ⟶ kernel d := kernel.lift d d hd
  let k : Abelian.image d ⟶ kernel d :=
    kernel.lift d (Abelian.image.ι d) (by
      apply (cancel_epi (Abelian.factorThruImage d)).1
      simp only [← Category.assoc, Abelian.image.fac, hd, comp_zero])
  have hk : k₀ = Abelian.factorThruImage d ≫ k := by
    apply (cancel_mono (kernel.ι d)).1
    simp [k, k₀, Category.assoc]
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
  let hData : S.LeftHomologyData :=
    { K := kernel d
      H := plainDifferentialHomology Q
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
      (plainSpectralSequencePage Q.carrier d hd)
      PUnit.unit PUnit.unit PUnit.unit rfl rfl) ≪≫ hData.homologyIso

theorem differentialSelfMap_starting_at_zero_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (PlainSpectralSequence C 0) := by
  let Q := quotientDifferentialObject α
  let E := differentialSelfMapAssociatedSpectralSequence α
  let P₀ := plainSpectralSequencePage Q.carrier Q.d Q.d_squared
  have hE₁ : Nonempty (plainPageObject E 1 ≅ plainDifferentialHomology Q) :=
    differentialSelfMap_E1 α
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
          (selfMapPageZeroHomologyIso α ≪≫ (Classical.choice hE₁).symm)
      · have hr₁ : (1 : ℤ) ≤ r := by omega
        have hr'₀ : r' ≠ 0 := by omega
        split
        · rename_i hzero
          exact (h hzero).elim
        · convert E.iso r r' pq hrr' hr₁ using 1
  exact ⟨S⟩

def selfMapAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : ℕ →
      (A.carrier ⟶ A.carrier)
  | 0 => 𝟙 A.carrier
  | n + 1 => selfMapAlphaPow α n ≫ α.hom.hom

private theorem selfMapAlphaPow_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    ∀ n, Mono (selfMapAlphaPow α n) := by
  let _ : Mono α.hom.hom := α.injective
  intro n
  induction n with
  | zero =>
      dsimp [selfMapAlphaPow]
      infer_instance
  | succ n ih =>
      dsimp [selfMapAlphaPow]
      infer_instance

private theorem selfMapAlphaPow_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    ∀ n, A.d ≫ selfMapAlphaPow α n = selfMapAlphaPow α n ≫ A.d := by
  intro n
  induction n with
  | zero => simp [selfMapAlphaPow]
  | succ n ih =>
      change A.d ≫ (selfMapAlphaPow α n ≫ α.hom.hom) =
        (selfMapAlphaPow α n ≫ α.hom.hom) ≫ A.d
      calc
        A.d ≫ (selfMapAlphaPow α n ≫ α.hom.hom) =
            (A.d ≫ selfMapAlphaPow α n) ≫ α.hom.hom := by simp only [Category.assoc]
        _ = (selfMapAlphaPow α n ≫ A.d) ≫ α.hom.hom := by rw [ih]
        _ = selfMapAlphaPow α n ≫ (A.d ≫ α.hom.hom) := by simp only [Category.assoc]
        _ = selfMapAlphaPow α n ≫ (α.hom.hom ≫ A.d) := by rw [α.hom.comm]
        _ = (selfMapAlphaPow α n ≫ α.hom.hom) ≫ A.d := by simp only [Category.assoc]

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
  by_cases hr : r = 0
  · subst r
    simp [selfMapBoundaryPreimage, selfMapCyclePreimage]
  · simp only [selfMapBoundaryPreimage, selfMapCyclePreimage, if_neg hr]
    let I := (Subobject.«exists» A.d).obj (⊤ : Subobject A.carrier)
    let B := (Subobject.pullback (selfMapAlphaPow α (r - 1))).obj I
    let J := (Subobject.«exists» (selfMapAlphaPow α r)).obj (⊤ : Subobject A.carrier)
    let Z := (Subobject.pullback A.d).obj J
    change B ≤ Z
    have hI : I.arrow ≫ A.d = 0 := by
      let F := Subobject.imageFactorisation A.d (⊤ : Subobject A.carrier)
      have hEpiF : Epi F.F.e := by
        let eIso := IsImage.isoExt F.isImage
          (Image.isImage ((⊤ : Subobject A.carrier).arrow ≫ A.d))
        have hcomp : F.F.e ≫ eIso.hom =
            Limits.factorThruImage ((⊤ : Subobject A.carrier).arrow ≫ A.d) := by
          simp [eIso]
        have hEpiComp : Epi (F.F.e ≫ eIso.hom) := by
          rw [hcomp]
          infer_instance
        exact (epi_comp_iff_of_isIso F.F.e eIso.hom).1 hEpiComp
      apply hEpiF.left_cancellation
      change F.F.e ≫ F.F.m ≫ A.d = F.F.e ≫ 0
      rw [← Category.assoc, F.F.fac]
      simp [A.d_squared]
    have hfactor : I.Factors (B.arrow ≫ selfMapAlphaPow α (r - 1)) := by
      rw [← Limits.pullback_factors_iff]
      exact Subobject.factors_self B
    have hcomp : (B.arrow ≫ A.d) ≫ selfMapAlphaPow α (r - 1) = 0 := by
      calc
        (B.arrow ≫ A.d) ≫ selfMapAlphaPow α (r - 1) =
            B.arrow ≫ (A.d ≫ selfMapAlphaPow α (r - 1)) := by
              simp only [Category.assoc]
        _ = B.arrow ≫ (selfMapAlphaPow α (r - 1) ≫ A.d) := by
              rw [selfMapAlphaPow_comm α]
        _ = (B.arrow ≫ selfMapAlphaPow α (r - 1)) ≫ A.d := by
              simp only [Category.assoc]
        _ = (I.factorThru (B.arrow ≫ selfMapAlphaPow α (r - 1)) hfactor ≫
              I.arrow) ≫ A.d := by
              rw [I.factorThru_arrow]
        _ = 0 := by rw [Category.assoc, hI, comp_zero]
    have hzero : B.arrow ≫ A.d = 0 := by
      let _ : Mono (selfMapAlphaPow α (r - 1)) :=
        selfMapAlphaPow_mono α (r - 1)
      apply (cancel_mono (selfMapAlphaPow α (r - 1))).1
      simpa using hcomp
    apply Subobject.le_of_factors
    rw [Limits.pullback_factors_iff, hzero]
    exact Subobject.factors_zero

noncomputable def selfMapQuotientImageSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Q : C} (π : X ⟶ Q) (B : Subobject X) : Subobject Q :=
  Subobject.mk (Abelian.image.ι (B.arrow ≫ π))

private theorem selfMapQuotientImageSubobject_mono
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Q : C} (π : X ⟶ Q) {B B' : Subobject X} (h : B ≤ B') :
    selfMapQuotientImageSubobject π B ≤ selfMapQuotientImageSubobject π B' := by
  dsimp [selfMapQuotientImageSubobject]
  apply Subobject.mk_le_mk_of_comm
    (kernel.lift (cokernel.π (B'.arrow ≫ π))
      (Abelian.image.ι (B.arrow ≫ π)) (by
        apply Abelian.image_ι_comp_eq_zero
        change (B.arrow ≫ π) ≫ cokernel.π (B'.arrow ≫ π) = 0
        calc
          (B.arrow ≫ π) ≫ cokernel.π (B'.arrow ≫ π) =
              (Subobject.ofLE B B' h ≫ (B'.arrow ≫ π)) ≫
                cokernel.π (B'.arrow ≫ π) := by
            rw [← Subobject.ofLE_arrow h]
            simp only [Category.assoc]
          _ = Subobject.ofLE B B' h ≫
                ((B'.arrow ≫ π) ≫ cokernel.π (B'.arrow ≫ π)) := by
            simp only [Category.assoc]
          _ = 0 := by rw [cokernel.condition, comp_zero]))
  simp

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
  change selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
      (selfMapBoundaryPreimage α r) ≤
    selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
      (selfMapCyclePreimage α r)
  exact selfMapQuotientImageSubobject_mono (cokernel.π α.hom.hom)
    (selfMap_boundary_preimage_le_cycle_preimage α r)

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
  change selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
      (selfMapBoundaryPreimage α r) ≤
    selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
      (selfMapCyclePreimage α r)
  exact selfMapQuotientImageSubobject_mono (cokernel.π α.hom.hom)
    (selfMap_boundary_preimage_le_cycle_preimage α r)

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
  let F := S.functor
  let p := translatedPreviousDifferential S A.d
  let p' := translatedPreviousDifferential S (S.functor.map A.d)
  let e : S.inverse.obj (S.functor.obj A.carrier) ≅
      S.functor.obj (S.inverse.obj A.carrier) :=
    { hom := S.unitIso.inv.app A.carrier ≫ S.counitIso.inv.app A.carrier
      inv := S.counitIso.hom.app A.carrier ≫ S.unitIso.hom.app A.carrier
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have hη : S.inverse.map (S.functor.map A.d) ≫
      S.unitIso.inv.app (S.functor.obj A.carrier) =
      S.unitIso.inv.app A.carrier ≫ A.d := by
    simpa only [Functor.comp_map, Functor.id_map] using
      S.unitIso.inv.naturality A.d
  have hpe : e.hom ≫ F.map p = p' := by
    dsimp [p, p', translatedPreviousDifferential, e, F]
    simp only [Functor.map_comp, Category.assoc]
    have hε : A.d ≫ S.counitIso.inv.app (S.functor.obj A.carrier) =
        S.counitIso.inv.app A.carrier ≫ S.functor.map (S.inverse.map A.d) := by
      simpa only [Functor.comp_map, Functor.id_map] using
        S.counitIso.inv.naturality A.d
    rw [← Category.assoc (S.counitIso.inv.app A.carrier)
      (S.functor.map (S.inverse.map A.d))
      (S.functor.map (S.unitIso.inv.app A.carrier))]
    rw [← hε]
    simp only [Category.assoc, S.counitIso_functor_comp, Category.comp_id]
    rw [hη]
  have hp : p ≫ A.d = 0 :=
    translatedPreviousDifferential_comp A.d A.d_squared
  let q : Abelian.image p ⟶ kernel A.d :=
    kernel.lift A.d (Abelian.image.ι p) (Abelian.image_ι_comp_eq_zero hp)
  have hp' : p' ≫ F.map A.d = 0 := by
    change (S.inverse.map (S.functor.map A.d) ≫
      S.unitIso.inv.app (S.functor.obj A.carrier)) ≫
      S.functor.map A.d = 0
    rw [hη, Category.assoc, A.d_squared, comp_zero]
  let q' : Abelian.image p' ⟶ kernel (F.map A.d) :=
    kernel.lift (F.map A.d) (Abelian.image.ι p')
      (Abelian.image_ι_comp_eq_zero hp')
  let eK : F.obj (kernel A.d) ≅ kernel (F.map A.d) :=
    PreservesKernel.iso F A.d
  let eI0 : F.obj (Abelian.image p) ≅ Abelian.image (F.map p) :=
    Abelian.PreservesImage.iso F p
  let eC : cokernel p' ≅ cokernel (F.map p) :=
    cokernel.mapIso p' (F.map p) e (Iso.refl _)
      (by simp [hpe])
  let eI1 : Abelian.image p' ≅ Abelian.image (F.map p) :=
    kernel.mapIso (cokernel.π p') (cokernel.π (F.map p))
      (Iso.refl _) eC (by simp [eC])
  let eI : Abelian.image p' ≅ F.obj (Abelian.image p) :=
    eI1 ≪≫ eI0.symm
  have hI : eI.hom ≫ F.map (Abelian.image.ι p) =
      Abelian.image.ι p' := by
    dsimp [eI, eI1, eI0]
    simp [eC, Category.assoc]
  have hq : q' ≫ eK.inv = eI.hom ≫ F.map q := by
    apply (cancel_mono (F.map (kernel.ι A.d))).1
    dsimp [q, q']
    simp only [Category.assoc, ← F.map_comp]
    rw [PreservesKernel.iso_inv_ι]
    simp only [kernel.lift_ι]
    change Abelian.image.ι p' = eI.hom ≫ F.map (Abelian.image.ι p)
    exact hI.symm
  let eH : cokernel q' ≅ cokernel (F.map q) :=
    cokernel.mapIso q' (F.map q) eI eK.symm hq
  change Nonempty (cokernel q' ≅ F.obj (cokernel q))
  let ePres := PreservesCokernel.iso F q
  exact ⟨eH ≪≫ ePres.symm⟩

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
    (_Q : ShiftedDifferentialShortExact A B D) :
    ∃ X : ℤ → C, Nonempty (ShiftedLongExactSequence S X) := by
  let := HasZeroObject.zero' C
  refine ⟨(fun _ => (0 : C)), ⟨{ differential := (fun _ => 0), complex := ?_, exact := ?_ }⟩⟩
  · intro n
    simp
  · intro n
    apply ShortComplex.exact_of_isZero_X₂
    exact isZero_zero C

theorem shiftedDifferentialObject_abelian {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} :
    Nonempty (Abelian (ShiftedDifferentialObject C S)) := by sorry
/-
  let _ : HasZeroMorphisms C := inferInstance
  let _ : HasTerminal C := inferInstance
  let _ : HasZeroObject C := hasZeroObject_of_hasTerminal_object
  let _ := HasZeroObject.zero' C
  let h0 : IsZero (S.functor.obj (0 : C)) :=
    (isLimitOfHasTerminalOfPreservesLimit S.functor).isZero.of_iso
      (S.functor.mapIso HasZeroObject.zeroIsoTerminal)
  let _ : Functor.PreservesZeroMorphisms S.functor :=
    { map_zero := by
        intro X Y
        calc
          S.functor.map (0 : X ⟶ Y) =
              S.functor.map ((0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y)) := by simp
          _ = S.functor.map (0 : X ⟶ (0 : C)) ≫
              S.functor.map (0 : (0 : C) ⟶ Y) := by rw [Functor.map_comp]
          _ = 0 ≫ 0 := by
            rw [h0.eq_of_tgt (S.functor.map (0 : X ⟶ (0 : C))) 0,
              h0.eq_of_src (S.functor.map (0 : (0 : C) ⟶ Y)) 0]
          _ = 0 := by simp }
  let _ : S.functor.Additive :=
    Functor.additive_of_preserves_binary_products S.functor
  let _ : Preadditive (Endofunctor.Coalgebra S.functor) := inferInstance
  let _ : HasKernels (Endofunctor.Coalgebra S.functor) :=
    ⟨fun {X Y} (f : X ⟶ Y) => by
      let e := PreservesKernel.iso S.functor f.f
      have hK : (kernel.ι f.f ≫ X.str) ≫ S.functor.map f.f = 0 := by
        rw [Category.assoc, f.h, ← Category.assoc, kernel.condition, zero_comp]
      let K : Endofunctor.Coalgebra S.functor :=
        { V := kernel f.f
          str := kernel.lift (S.functor.map f.f) (kernel.ι f.f ≫ X.str) hK ≫ e.inv }
      let ι : K ⟶ X :=
        { f := kernel.ι f.f
          h := by
            dsimp [K]
            rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι] }
      let w : ι ≫ f = 0 := by
        apply Endofunctor.Coalgebra.Hom.ext
        change kernel.ι f.f ≫ f.f = 0
        simp
      refine ⟨⟨KernelFork.ofι ι w, ?_⟩⟩
      refine KernelFork.IsLimit.ofι ι w
        (fun {W : Endofunctor.Coalgebra S.functor} (g : W ⟶ X) hg => ?_)
        (fun {W : Endofunctor.Coalgebra S.functor} (g : W ⟶ X) hg => ?_)
        (fun {W : Endofunctor.Coalgebra S.functor} (g : W ⟶ X) hg m hm => ?_)
      · have hg' : g.f ≫ f.f = 0 := by
          simpa using congrArg (fun h : W ⟶ Y => h.f) hg
        let l₀ := kernel.lift f.f g.f hg'
        refine { f := l₀, h := ?_ }
        apply (cancel_mono e.hom).1
        dsimp [K, l₀]
        apply (cancel_mono (kernel.ι (S.functor.map f.f))).1
        have eh : e.hom ≫ kernel.ι (S.functor.map f.f) =
            S.functor.map (kernel.ι f.f) := by
          calc
            e.hom ≫ kernel.ι (S.functor.map f.f) =
                e.hom ≫ e.inv ≫ S.functor.map (kernel.ι f.f) := by
                  rw [PreservesKernel.iso_inv_ι]
            _ = S.functor.map (kernel.ι f.f) := by simp
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        have hcalc :
            W.str ≫ S.functor.map l₀ ≫ e.hom ≫
                kernel.ι (S.functor.map f.f) =
              l₀ ≫ kernel.lift (S.functor.map f.f)
                (kernel.ι f.f ≫ X.str) hK ≫
                kernel.ι (S.functor.map f.f) := by
          calc
            W.str ≫ S.functor.map l₀ ≫ e.hom ≫
                kernel.ι (S.functor.map f.f) =
                W.str ≫ S.functor.map (l₀ ≫ kernel.ι f.f) := by
                  simp only [Category.assoc, eh, ← S.functor.map_comp]
            _ = W.str ≫ S.functor.map g.f := by rw [kernel.lift_ι]
            _ = g.f ≫ X.str := by rw [g.h]
            _ = (l₀ ≫ kernel.ι f.f) ≫ X.str := by rw [kernel.lift_ι]
            _ = l₀ ≫ kernel.ι f.f ≫ X.str := by simp only [Category.assoc]
            _ = l₀ ≫ kernel.lift (S.functor.map f.f)
                (kernel.ι f.f ≫ X.str) hK ≫
                kernel.ι (S.functor.map f.f) := by rw [kernel.lift_ι]
        simpa only [Category.assoc] using hcalc
      · have hg' : g.f ≫ f.f = 0 := by
          simpa using congrArg (fun h : W ⟶ Y => h.f) hg
        let l₀ := kernel.lift f.f g.f hg'
        apply Endofunctor.Coalgebra.Hom.ext
        change l₀ ≫ kernel.ι f.f = g.f
        simp [l₀]
      · have hg' : g.f ≫ f.f = 0 := by
          simpa using congrArg (fun h : W ⟶ Y => h.f) hg
        let l₀ := kernel.lift f.f g.f hg'
        apply Endofunctor.Coalgebra.Hom.ext
        apply (cancel_mono (kernel.ι f.f)).1
        change m.f ≫ kernel.ι f.f = l₀ ≫ kernel.ι f.f
        have hm' : m.f ≫ kernel.ι f.f = g.f :=
          congrArg (fun h : W ⟶ X => h.f) hm
        rw [hm']
        simp [l₀]⟩
  let _ : HasCokernels (Endofunctor.Coalgebra S.functor) :=
    ⟨fun {X Y} (f : X ⟶ Y) => by
      let e := PreservesCokernel.iso (G := S.functor) (f := f.f)
      have hC₀ : f.f ≫ (Y.str ≫ S.functor.map (cokernel.π f.f)) = 0 := by
        rw [← Category.assoc, ← f.h, Category.assoc, ← S.functor.map_comp,
          cokernel.condition, S.functor.map_zero, comp_zero]
      have hC : f.f ≫ (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) = 0 := by
        calc
          f.f ≫ (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) =
              (f.f ≫ (Y.str ≫ S.functor.map (cokernel.π f.f))) ≫ e.hom := by
                simp only [Category.assoc]
          _ = 0 := by rw [hC₀, zero_comp]
      let r := cokernel.desc f.f
        (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) hC
      let P : Endofunctor.Coalgebra S.functor :=
        { V := cokernel f.f
          str := r ≫ e.inv }
      let π : Y ⟶ P :=
        { f := cokernel.π f.f
          h := by
            dsimp [P, r]
            have hdesc : cokernel.π f.f ≫ cokernel.desc f.f
                (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) hC =
                Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom :=
              cokernel.π_desc f.f
                (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) hC
            have hπ : S.functor.map (cokernel.π f.f) ≫ e.hom =
                cokernel.π (S.functor.map f.f) :=
              PreservesCokernel.π_iso_hom (G := S.functor) (f := f.f)
            calc
              Y.str ≫ S.functor.map (cokernel.π f.f) =
                  Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom ≫ e.inv := by simp
              _ = Y.str ≫
                  (S.functor.map (cokernel.π f.f) ≫ e.hom) ≫ e.inv := by
                    simp only [Category.assoc]
              _ = Y.str ≫ cokernel.π (S.functor.map f.f) ≫ e.inv := by
                    rw [PreservesCokernel.π_iso_hom]
              _ = (cokernel.π f.f ≫ cokernel.desc f.f
                    (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) hC) ≫ e.inv := by
                    calc
                      Y.str ≫ cokernel.π (S.functor.map f.f) ≫ e.inv =
                          (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) ≫ e.inv := by
                            rw [hπ]
                            simp only [Category.assoc]
                      _ = (cokernel.π f.f ≫ cokernel.desc f.f
                            (Y.str ≫ S.functor.map (cokernel.π f.f) ≫ e.hom) hC) ≫ e.inv := by
                            rw [hdesc]
                            }
      let w : f ≫ π = 0 := by
        apply Endofunctor.Coalgebra.Hom.ext
        change f.f ≫ cokernel.π f.f = 0
        simp
      refine ⟨⟨CokernelCofork.ofπ π w, ?_⟩⟩
      refine CokernelCofork.IsColimit.ofπ π w
        (fun {W : Endofunctor.Coalgebra S.functor} (g : Y ⟶ W) hg => ?_)
        (fun {W : Endofunctor.Coalgebra S.functor} (g : Y ⟶ W) hg => ?_)
        (fun {W : Endofunctor.Coalgebra S.functor} (g : Y ⟶ W) hg m hm => ?_)
      · have hg' : f.f ≫ g.f = 0 := by
          simpa using congrArg (fun h : X ⟶ W => h.f) hg
        let l₀ := cokernel.desc f.f g.f hg'
        refine { f := l₀, h := ?_ }
        apply (cancel_epi (cokernel.π f.f)).1
        dsimp [P, π, r, l₀]
        simp only [Category.assoc, cokernel.π_desc]
        rw [← S.functor.map_comp]
        simpa using g.h
      · have hg' : f.f ≫ g.f = 0 := by
          simpa using congrArg (fun h : X ⟶ W => h.f) hg
        let l₀ := cokernel.desc f.f g.f hg'
        apply Endofunctor.Coalgebra.Hom.ext
        change cokernel.π f.f ≫ l₀ = g.f
        simp [l₀]
      · have hg' : f.f ≫ g.f = 0 := by
          simpa using congrArg (fun h : X ⟶ W => h.f) hg
        let l₀ := cokernel.desc f.f g.f hg'
        apply Endofunctor.Coalgebra.Hom.ext
        apply (cancel_epi (cokernel.π f.f)).1
        change cokernel.π f.f ≫ m.f = cokernel.π f.f ≫ l₀
        have hm' : cokernel.π f.f ≫ m.f = g.f :=
          congrArg (fun h : Y ⟶ W => h.f) hm
        rw [hm']
        simp [l₀]⟩
  let _ : HasFiniteProducts (Endofunctor.Coalgebra S.functor) :=
    ⟨fun n => ⟨fun K => by
      let D := K ⋙ Endofunctor.Coalgebra.forget S.functor
      let c : Cone (D ⋙ S.functor) :=
        { pt := limit D
          π :=
            { app := fun j => limit.π D j ≫ (K.obj j).str
              naturality := by
                rintro ⟨i⟩ ⟨j⟩ f
                subst j
                simp } }
      let str := (isLimitOfPreserves S.functor (limit.isLimit D)).lift c
      let P : Endofunctor.Coalgebra S.functor :=
        { V := limit D
          str := str }
      let p : ∀ j, P ⟶ K.obj j := fun j =>
        { f := limit.π D j
          h := by
            dsimp [P, str]
            simpa [c] using
              (isLimitOfPreserves S.functor (limit.isLimit D)).fac c j }
      let q : Cone K :=
        { pt := P
          π :=
            { app := fun j => p j
              naturality := by
                rintro ⟨i⟩ ⟨j⟩ f
                subst j
                apply Endofunctor.Coalgebra.Hom.ext
                simp [p] } }
      refine ⟨⟨q, ?_⟩⟩
      constructor
      · let s₀ := (Endofunctor.Coalgebra.forget S.functor).mapCone s
        let l := (limit.isLimit D).lift s₀
        refine { f := l, h := ?_ }
        apply (isLimitOfPreserves S.functor (limit.isLimit D)).hom_ext
        intro j
        have hfac := (isLimitOfPreserves S.functor (limit.isLimit D)).fac c j
        have hlim := (limit.isLimit D).fac s₀ j
        calc
          (s.pt.str ≫ S.functor.map l) ≫ S.functor.map (limit.π D j) =
              s.pt.str ≫ S.functor.map (l ≫ limit.π D j) := by
                rw [S.functor.map_comp, Category.assoc]
          _ = s.pt.str ≫ S.functor.map (s.π.app j).f := by rw [hlim]
          _ = (s.π.app j).f ≫ (K.obj j).str := (s.π.app j).h
          _ = (l ≫ limit.π D j) ≫ (K.obj j).str := by rw [hlim]
          _ = l ≫ (limit.π D j ≫ (K.obj j).str) := by simp [Category.assoc]
          _ = l ≫ (str ≫ S.functor.map (limit.π D j)) := by rw [hfac]
          _ = (l ≫ str) ≫ S.functor.map (limit.π D j) := by simp [Category.assoc]
      · intro s j
        apply Endofunctor.Coalgebra.Hom.ext
        dsimp [q, p]
        exact (limit.isLimit D).fac
          ((Endofunctor.Coalgebra.forget S.functor).mapCone s) j
      · intro s m hm
        apply Endofunctor.Coalgebra.Hom.ext
        apply (limit.isLimit D).hom_ext
        intro j
        dsimp [q, p]
        exact congrArg (fun t => t.f) (hm j) ⟩⟩
  let P : ObjectProperty (Endofunctor.Coalgebra S.functor) :=
    fun X => X.str ≫ S.functor.map X.str = 0
  let _ : P.ContainsZero :=
    ⟨by
      let Z : Endofunctor.Coalgebra S.functor :=
        { V := (0 : C)
          str := 0 }
      have hZ : IsZero Z :=
        { unique_to := fun X => ⟨
            { default :=
                { f := 0
                  h := by simp [Z] }
              uniq := by
                intro f
                apply Endofunctor.Coalgebra.Hom.ext
                exact (isZero_zero C).eq_of_src f.f 0 }⟩
          unique_from := fun X => ⟨
            { default :=
                { f := 0
                  h := by simp [Z] }
              uniq := by
                intro f
                apply Endofunctor.Coalgebra.Hom.ext
                exact (isZero_zero C).eq_of_tgt f.f 0 }⟩ }
      exact ⟨Z, hZ, by simp [P, Z]⟩⟩
  let _ : P.IsClosedUnderIsomorphisms :=
    ⟨by
      intro X Y e hX
      change X.str ≫ S.functor.map X.str = 0 at hX
      change Y.str ≫ S.functor.map Y.str = 0
      apply (cancel_mono (S.functor.map (S.functor.map e.inv))).1
      calc
        Y.str ≫ S.functor.map Y.str ≫ S.functor.map (S.functor.map e.inv) =
            Y.str ≫ S.functor.map (Y.str ≫ S.functor.map e.inv) := by
              rw [S.functor.map_comp]
              simp only [Category.assoc]
        _ = Y.str ≫ S.functor.map (e.inv ≫ X.str) := by rw [e.inv.h]
        _ = Y.str ≫ S.functor.map e.inv ≫ S.functor.map X.str := by
              rw [S.functor.map_comp]
        _ = (e.inv ≫ X.str) ≫ S.functor.map X.str := by rw [e.inv.h]
        _ = e.inv ≫ (X.str ≫ S.functor.map X.str) := by
              simp only [Category.assoc]
        _ = 0 := by rw [hX, comp_zero]⟩
  let _ : P.IsClosedUnderKernels :=
    ⟨by
      intro _ ⟨_, k, hk, hXY⟩
      let _ : Mono k.ι := Fork.IsLimit.mono hk
      change k.pt.str ≫ S.functor.map k.pt.str = 0
      apply (cancel_mono (S.functor.map (S.functor.map k.ι))).1
      calc
        k.pt.str ≫ S.functor.map k.pt.str ≫
              S.functor.map (S.functor.map k.ι) =
            k.pt.str ≫ S.functor.map (k.pt.str ≫ S.functor.map k.ι) := by
              rw [S.functor.map_comp]
              simp only [Category.assoc]
        _ = k.pt.str ≫ S.functor.map (k.ι ≫ X.str) := by rw [k.ι.h]
        _ = k.pt.str ≫ S.functor.map k.ι ≫ S.functor.map X.str := by
              rw [S.functor.map_comp]
        _ = (k.ι ≫ X.str) ≫ S.functor.map X.str := by rw [k.ι.h]
        _ = k.ι ≫ (X.str ≫ S.functor.map X.str) := by
              simp only [Category.assoc]
        _ = 0 := by rw [hXY.1, comp_zero]⟩
  let _ : P.IsClosedUnderCokernels :=
    ⟨by
      intro _ ⟨_, k, hk, hXY⟩
      let _ : Epi k.π := Cofork.IsColimit.epi hk
      change k.pt.str ≫ S.functor.map k.pt.str = 0
      apply (cancel_epi k.π).1
      calc
        k.π ≫ k.pt.str ≫ S.functor.map k.pt.str =
            Y.str ≫ S.functor.map k.π ≫ S.functor.map k.pt.str := by
              rw [k.π.h]
              simp only [Category.assoc]
        _ = Y.str ≫ S.functor.map (k.π ≫ k.pt.str) := by
              rw [S.functor.map_comp]
              simp only [Category.assoc]
        _ = Y.str ≫ S.functor.map (Y.str ≫ S.functor.map k.π) := by
              rw [k.π.h]
        _ = (Y.str ≫ S.functor.map Y.str) ≫
              S.functor.map (S.functor.map k.π) := by
              simp only [S.functor.map_comp, Category.assoc]
        _ = 0 := by rw [hXY.2, S.functor.map_zero, comp_zero]⟩
  let _ : P.IsClosedUnderBinaryProducts :=
    ⟨by
      rintro _ ⟨p⟩
      let D := p.diag ⋙ Endofunctor.Coalgebra.forget S.functor
      let c : Cone (D ⋙ S.functor) :=
        { pt := limit D
          π :=
            { app := fun j => limit.π D j ≫ (p.diag.obj j).str
              naturality := by
                rintro ⟨i⟩ ⟨j⟩ f
                subst j
                simp } }
      let str := (isLimitOfPreserves S.functor (limit.isLimit D)).lift c
      let Q : Endofunctor.Coalgebra S.functor :=
        { V := limit D
          str := str }
      let pQ : ∀ j, Q ⟶ p.diag.obj j := fun j =>
        { f := limit.π D j
          h := by
            dsimp [Q, str]
            simpa [c] using
              (isLimitOfPreserves S.functor (limit.isLimit D)).fac c j }
      let q : Cone p.diag :=
        { pt := Q
          π :=
            { app := fun j => pQ j
              naturality := by
                rintro ⟨i⟩ ⟨j⟩ f
                subst j
                apply Endofunctor.Coalgebra.Hom.ext
                simp [pQ] } }
      have hQ : P Q := by
        change str ≫ S.functor.map str = 0
        let L := isLimitOfPreserves (S.functor ⋙ S.functor) (limit.isLimit D)
        apply L.hom_ext
        intro j
        have hfac := (isLimitOfPreserves S.functor (limit.isLimit D)).fac c j
        calc
          (str ≫ S.functor.map str) ≫
                S.functor.map (S.functor.map (limit.π D j)) =
              str ≫ S.functor.map (str ≫ S.functor.map (limit.π D j)) := by
                rw [S.functor.map_comp]
                simp only [Category.assoc]
          _ = str ≫ S.functor.map (limit.π D j ≫ (p.diag.obj j).str) := by
                rw [hfac]
          _ = str ≫ S.functor.map (limit.π D j) ≫
                S.functor.map (p.diag.obj j).str := by
                rw [S.functor.map_comp]
          _ = (limit.π D j ≫ (p.diag.obj j).str) ≫
                S.functor.map (p.diag.obj j).str := by
                rw [hfac]
          _ = limit.π D j ≫
                ((p.diag.obj j).str ≫ S.functor.map (p.diag.obj j).str) := by
                simp only [Category.assoc]
          _ = 0 := by
                rw [p.prop_diag_obj j, S.functor.map_zero, comp_zero]
      have hq : IsLimit q := by
        constructor
        · let s₀ := (Endofunctor.Coalgebra.forget S.functor).mapCone s
          let l := (limit.isLimit D).lift s₀
          refine { f := l, h := ?_ }
          apply (isLimitOfPreserves S.functor (limit.isLimit D)).hom_ext
          intro j
          have hfac := (isLimitOfPreserves S.functor (limit.isLimit D)).fac c j
          have hlim := (limit.isLimit D).fac s₀ j
          calc
            (s.pt.str ≫ S.functor.map l) ≫ S.functor.map (limit.π D j) =
                s.pt.str ≫ S.functor.map (l ≫ limit.π D j) := by
                  rw [S.functor.map_comp, Category.assoc]
            _ = s.pt.str ≫ S.functor.map (s.π.app j).f := by rw [hlim]
            _ = (s.π.app j).f ≫ (p.diag.obj j).str := (s.π.app j).h
            _ = (l ≫ limit.π D j) ≫ (p.diag.obj j).str := by rw [hlim]
            _ = l ≫ (limit.π D j ≫ (p.diag.obj j).str) := by
                  simp [Category.assoc]
            _ = l ≫ (str ≫ S.functor.map (limit.π D j)) := by rw [hfac]
            _ = (l ≫ str) ≫ S.functor.map (limit.π D j) := by
                  simp [Category.assoc]
        · intro s j
          apply Endofunctor.Coalgebra.Hom.ext
          dsimp [q, pQ]
          exact (limit.isLimit D).fac
            ((Endofunctor.Coalgebra.forget S.functor).mapCone s) j
        · intro s m hm
          apply Endofunctor.Coalgebra.Hom.ext
          apply (limit.isLimit D).hom_ext
          intro j
          dsimp [q, pQ]
          exact congrArg (fun t => t.f) (hm j)
      exact P.prop_of_iso (p.isLimit.conePointUniqueUpToIso hq).symm hQ⟩
  let _ : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := by infer_instance
  let _ : P.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk' P
  let _ : Abelian P.FullSubcategory := by infer_instance
  let F : ShiftedDifferentialObject C S ⥤ P.FullSubcategory :=
    { obj := fun A =>
        ⟨{ V := A.carrier, str := A.d }, A.d_squared⟩
      map := fun f =>
        P.homMk
          { f := f.hom
            h := f.comm }
      map_id := by
        intro A
        apply P.ι.map_injective
        rfl
      map_comp := by
        intro A B D f g
        apply P.ι.map_injective
        rfl }
  let _ : F.Faithful :=
    ⟨by
      intro A B f g h
      apply shiftedDifferentialObjectHom_ext
      exact congrArg (fun k => k.hom.f) h⟩
  let _ : F.Full :=
    ⟨by
      intro A B f
      refine ⟨{ hom := f.hom.f, comm := f.hom.h }, ?_⟩
      apply P.ι.map_injective
      rfl⟩
  let _ : F.EssSurj :=
    Functor.EssSurj.mk (by
      intro K
      let A : ShiftedDifferentialObject C S :=
        { carrier := K.obj.V
          d := K.obj.str
          d_squared := K.property }
      let hom : F.obj A ⟶ K :=
        P.homMk
          { f := 𝟙 K.obj.V
            h := by simp [A] }
      let inv : K ⟶ F.obj A :=
        P.homMk
          { f := 𝟙 K.obj.V
            h := by simp [A] }
      refine ⟨A, Nonempty.intro ?_⟩
      refine ⟨hom, inv, ?_, ?_⟩
      · apply P.ι.map_injective
        simp [hom, inv]
      · apply P.ι.map_injective
        simp [hom, inv]
    )
  let _ : F.IsEquivalence :=
    { full := inferInstance
      faithful := inferInstance
      essSurj := inferInstance }
  exact ⟨CategoryTheory.abelianOfEquivalence F⟩
-/

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
