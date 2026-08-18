import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Categories.Unit19.FilteredColimits
import Formalization.Books.Homology.Unit04.KaroubianCategories
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# Homological Algebra, Chapter 30: Essentially constant systems

This file records the three statements in the `Essentially constant systems`
section.  The category-theoretic notion of essential constancy is reused from
Categories, Chapter 22.  A direct-sum decomposition is represented by
Mathlib's `BinaryBiproductData`, and a cofinal or initial subcategory is
represented by the canonical full-subcategory inclusion.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit22

universe u v u' v'

namespace Formalization.Books.Homology.Unit30

/-! ## Splittings of essentially constant diagrams -/

/-- The filtered colimit-and-splitting condition in the first part of the
source lemma.  The cocone `c` is the source's object `X = colim M`. -/
def IndColimitSplitting
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    (M : I ⥤ A) : Prop :=
  ∃ (c : Cocone M),
    Nonempty (IsColimit c) ∧
      ∃ (P : ObjectProperty I),
        IsFiltered P.FullSubcategory ∧
          Functor.Final P.ι ∧
            ∀ i' : P.FullSubcategory,
              ∃ (X' Z' : A) (b : BinaryBiproductData X' Z')
                (e : b.bicone.pt ≅ M.obj (P.ι.obj i')),
                IsIso (b.bicone.inl ≫ e.hom ≫ c.ι.app (P.ι.obj i')) ∧
                  ∃ (i'' : P.FullSubcategory) (f : i' ⟶ i''),
                    b.bicone.inr ≫ e.hom ≫ M.map (P.ι.map f) = 0

/-- The cofiltered limit-and-splitting condition in the second part of the
source lemma.  The cone `c` is the source's object `X = lim M`. -/
def ProLimitSplitting
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    (M : I ⥤ A) : Prop :=
  ∃ (c : Cone M),
    Nonempty (IsLimit c) ∧
      ∃ (P : ObjectProperty I),
        IsCofiltered P.FullSubcategory ∧
          Functor.Initial P.ι ∧
            ∀ i' : P.FullSubcategory,
              ∃ (X' Z' : A) (b : BinaryBiproductData X' Z')
                (e : b.bicone.pt ≅ M.obj (P.ι.obj i')),
                IsIso (c.π.app (P.ι.obj i') ≫ e.inv ≫ b.bicone.fst) ∧
                  ∃ (i'' : P.FullSubcategory) (f : i'' ⟶ i'),
                    M.map (P.ι.map f) ≫ e.inv ≫ b.bicone.snd = 0

/-- A filtered essentially constant diagram in a preadditive Karoubian
category is characterized by a colimit and a cofinal filtered splitting. -/
theorem essentiallyConstantInd_iff_indColimitSplitting
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantIndDiagram M ↔ IndColimitSplitting M := by
  constructor
  · intro hM
    obtain ⟨c, hc, hconst⟩ := essentiallyConstantInd_hasColimit hM
    rcases hconst with ⟨i, s, hs, hfactor⟩
    let P : ObjectProperty I := fun j => Nonempty (i ⟶ j)
    have hP : ∀ j : I, ∃ j' : P.FullSubcategory,
        Nonempty (j ⟶ P.ι.obj j') := by
      intro j
      rcases hfactor j with ⟨k, f, g, _⟩
      exact ⟨⟨k, ⟨f⟩⟩, ⟨g⟩⟩
    have hPF :=
      Formalization.Books.Categories.Unit19.filtered_full_subcategory_isFiltered_and_isFinal P hP
    refine ⟨c, hc, P, hPF.1, hPF.2, ?_⟩
    intro i'
    let j : I := i'.obj
    change ∃ (X' Z' : A) (b : BinaryBiproductData X' Z')
      (e : b.bicone.pt ≅ M.obj j),
      IsIso (b.bicone.inl ≫ e.hom ≫ c.ι.app j) ∧
        ∃ (i'' : P.FullSubcategory) (f : i' ⟶ i''),
          b.bicone.inr ≫ e.hom ≫ M.map (P.ι.map f) = 0
    rcases i'.property with ⟨a⟩
    change i ⟶ j at a
    let q : M.obj j ⟶ M.obj j := c.ι.app j ≫ s ≫ M.map a
    have ha : M.map a ≫ c.ι.app j = c.ι.app i := by
      simpa using c.ι.naturality a
    have hq : q ≫ q = q := by
      calc
        q ≫ q = c.ι.app j ≫ s ≫ (M.map a ≫ c.ι.app j) ≫ s ≫ M.map a := by
          simp [q, Category.assoc]
        _ = c.ι.app j ≫ s ≫ c.ι.app i ≫ s ≫ M.map a := by
          simpa only [Category.assoc] using
            congrArg (fun z => c.ι.app j ≫ s ≫ z ≫ s ≫ M.map a) ha
        _ = c.ι.app j ≫ (s ≫ c.ι.app i) ≫ s ≫ M.map a := by
          simp only [Category.assoc]
        _ = q := by rw [hs]; simp [q]
    let p := Formalization.Books.Homology.Unit03.idempotentComplement q
    have hp : p ≫ p = p :=
      (Formalization.Books.Homology.Unit03.idempotent_complement_relations q hq).2.2
    obtain ⟨X', Z', b, e, he⟩ :=
      (Formalization.Books.Homology.Unit04.karoubian_iff_idempotent_direct_sum_decomposition
        (C := A)).mp
        ‹IsIdempotentComplete A› _ _ hp
    have hconj : e.inv ≫ q ≫ e.hom = b.bicone.fst ≫ b.bicone.inl := by
      have hqp : q = 𝟙 _ - p := by
        simp [p, Formalization.Books.Homology.Unit03.idempotentComplement]
      apply b.isBilimit.isLimit.hom_ext
      intro j
      rcases j with ⟨⟨⟩⟩
      · change (e.inv ≫ q ≫ e.hom) ≫ b.bicone.fst =
          (b.bicone.fst ≫ b.bicone.inl) ≫ b.bicone.fst
        simp [hqp, Category.assoc, he]
      · change (e.inv ≫ q ≫ e.hom) ≫ b.bicone.snd =
          (b.bicone.fst ≫ b.bicone.inl) ≫ b.bicone.snd
        simp [hqp, Category.assoc, he]
    let u : X' ⟶ c.pt :=
      b.bicone.inl ≫ e.inv ≫ c.ι.app j
    let v : c.pt ⟶ X' :=
      s ≫ M.map a ≫ e.hom ≫ b.bicone.fst
    have huv : u ≫ v = 𝟙 X' := by
      dsimp [u, v]
      calc
        (b.bicone.inl ≫ e.inv ≫ c.ι.app j) ≫
            (s ≫ M.map a ≫ e.hom ≫ b.bicone.fst) =
            b.bicone.inl ≫ (e.inv ≫ q ≫ e.hom) ≫ b.bicone.fst := by
              simp [q, Category.assoc]
        _ = 𝟙 X' := by rw [hconj]; simp [Category.assoc]
    have hvu : v ≫ u = 𝟙 c.pt := by
      dsimp [u, v]
      have hconj' : e.hom ≫ b.bicone.fst ≫ b.bicone.inl ≫ e.inv = q := by
        calc
          e.hom ≫ b.bicone.fst ≫ b.bicone.inl ≫ e.inv =
              e.hom ≫ (b.bicone.fst ≫ b.bicone.inl) ≫ e.inv := by
                simp only [Category.assoc]
          _ = e.hom ≫ (e.inv ≫ q ≫ e.hom) ≫ e.inv := by rw [hconj]
          _ = q := by simp [Category.assoc]
      have hqc : q ≫ c.ι.app j = c.ι.app j := by
        change (c.ι.app j ≫ s ≫ M.map a) ≫ c.ι.app j = c.ι.app j
        simp only [Category.assoc]
        rw [ha, hs]
        simp
      calc
        (s ≫ M.map a ≫ e.hom ≫ b.bicone.fst) ≫ b.bicone.inl ≫ e.inv ≫
            c.ι.app j =
            s ≫ M.map a ≫
              (e.hom ≫ b.bicone.fst ≫ b.bicone.inl ≫ e.inv) ≫
                c.ι.app j := by simp only [Category.assoc]
        _ = s ≫ M.map a ≫ q ≫ c.ι.app j := by rw [hconj']
        _ = 𝟙 c.pt := by
          rw [hqc]
          simp [q, Category.assoc, ha, hs]
    refine ⟨X', Z', b, e.symm, ?_, ?_⟩
    · exact ⟨⟨v, huv, hvu⟩⟩
    · obtain ⟨k, f, g, hfg⟩ := hfactor j
      refine ⟨⟨k, ⟨f⟩⟩, P.homMk g, ?_⟩
      have hzero : q ≫ M.map g = M.map g := by
        rw [hfg]
        change (c.ι.app j ≫ s ≫ M.map a) ≫ c.ι.app j ≫ s ≫ M.map f = _
        calc
          (c.ι.app j ≫ s ≫ M.map a) ≫ c.ι.app j ≫ s ≫ M.map f =
              c.ι.app j ≫ s ≫ (M.map a ≫ c.ι.app j) ≫ s ≫ M.map f := by
                simp only [Category.assoc]
          _ = c.ι.app j ≫ s ≫ c.ι.app i ≫ s ≫ M.map f := by
            simpa only [Category.assoc] using
              congrArg (fun z => c.ι.app j ≫ s ≫ z ≫ s ≫ M.map f) ha
          _ = c.ι.app j ≫ (s ≫ c.ι.app i) ≫ s ≫ M.map f := by
            simp only [Category.assoc]
          _ = c.ι.app j ≫ s ≫ M.map f := by rw [hs]; simp
      have hmap : p ≫ M.map g = 0 := by
        dsimp [p]
        change (𝟙 _ - q) ≫ M.map g = 0
        simp [Category.assoc, hzero]
      have hsecond : b.bicone.inr ≫ e.inv = b.bicone.inr ≫ e.inv ≫ p := by
        apply (cancel_mono e.hom).1
        simp only [Category.assoc, he, Iso.inv_hom_id_assoc]
        simp
      change b.bicone.inr ≫ e.inv ≫ M.map g = 0
      rw [← Category.assoc, hsecond]
      simp only [Category.assoc, hmap, comp_zero]

  · rintro ⟨c, hc, P, hP, hfinal, hdata⟩
    letI : IsFiltered P.FullSubcategory := hP
    letI : Functor.Final P.ι := hfinal
    let d : Cocone (P.ι ⋙ M) := Cocone.whisker P.ι c
    let i' : P.FullSubcategory :=
      Classical.choice (IsFiltered.nonempty (C := P.FullSubcategory))
    obtain ⟨X', Z', b, e, hu, _⟩ := hdata i'
    let u : X' ⟶ c.pt := b.bicone.inl ≫ e.hom ≫ c.ι.app (P.ι.obj i')
    let s : c.pt ⟶ M.obj (P.ι.obj i') :=
      inv u ≫ b.bicone.inl ≫ e.hom
    letI : IsIso u := hu
    have hs : s ≫ c.ι.app (P.ι.obj i') = 𝟙 c.pt := by
      dsimp [s, u]
      simp [Category.assoc]
    have hess : IsEssentiallyConstantInd (P.ι ⋙ M) d := by
      refine ⟨i', s, ?_, ?_⟩
      · change s ≫ c.ι.app (P.ι.obj i') = 𝟙 c.pt
        exact hs
      · intro j'
        change ∃ (k : P.FullSubcategory) (f : i' ⟶ k) (g : j' ⟶ k),
          M.map (P.ι.map g) =
            c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map f)
        obtain ⟨X₀, Z₀, b₀, e₀, hu₀, hkill₀s⟩ := hdata j'
        obtain ⟨k₀, f₀, hkill₀⟩ := hkill₀s
        obtain ⟨k, f, g, _⟩ := hP.cocone_objs i' k₀
        have hs' : s ≫ c.ι.app i'.obj = 𝟙 c.pt := by
          simpa using hs
        let h := f₀ ≫ g
        let d₀ : M.obj (P.ι.obj j') ⟶ M.obj (P.ι.obj k) :=
          M.map (P.ι.map h) -
            c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map f)
        have hcoc₁ : M.map (P.ι.map h) ≫ c.ι.app (P.ι.obj k) =
            c.ι.app (P.ι.obj j') := by
          simpa using c.ι.naturality (P.ι.map h)
        have hcoc₂ :
            (c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map f)) ≫
                c.ι.app (P.ι.obj k) = c.ι.app (P.ι.obj j') := by
          calc
            (c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map f)) ≫
                c.ι.app (P.ι.obj k) =
                c.ι.app (P.ι.obj j') ≫ s ≫
                  (M.map (P.ι.map f) ≫ c.ι.app (P.ι.obj k)) := by
                    simp only [Category.assoc]
            _ = c.ι.app (P.ι.obj j') ≫ s ≫
                  (c.ι.app (P.ι.obj i') ≫
                    ((Functor.const I).obj c.pt).map (P.ι.map f)) := by
                    rw [c.ι.naturality (P.ι.map f)]
            _ = c.ι.app (P.ι.obj j') := by
              simp only [Functor.const_obj_map, Functor.const_obj_obj,
                Category.comp_id, Category.assoc]
              rw [hs]
              simp
        have hd₀c : d₀ ≫ c.ι.app (P.ι.obj k) = 0 := by
          dsimp [d₀]
          rw [Preadditive.sub_comp]
          exact sub_eq_zero.mpr (hcoc₁.trans hcoc₂.symm)
        obtain ⟨X₁, Z₁, b₁, e₁, hu₁, hkill₁s⟩ := hdata k
        obtain ⟨l₁, t₁, hkill₁⟩ := hkill₁s
        let u₁ : X₁ ⟶ c.pt := b₁.bicone.inl ≫ e₁.hom ≫ c.ι.app (P.ι.obj k)
        letI : IsIso u₁ := hu₁
        have hck : b₁.bicone.inr ≫ e₁.hom ≫ c.ι.app (P.ι.obj k) = 0 := by
          have hn : M.map (P.ι.map t₁) ≫ c.ι.app (P.ι.obj l₁) =
              c.ι.app (P.ι.obj k) := by
            simpa using c.ι.naturality (P.ι.map t₁)
          calc
            b₁.bicone.inr ≫ e₁.hom ≫ c.ι.app (P.ι.obj k) =
                b₁.bicone.inr ≫ e₁.hom ≫
                  (M.map (P.ι.map t₁) ≫ c.ι.app (P.ι.obj l₁)) := by rw [hn]
            _ = (b₁.bicone.inr ≫ e₁.hom ≫ M.map (P.ι.map t₁)) ≫
                c.ι.app (P.ι.obj l₁) := by simp only [Category.assoc]
            _ = 0 := by rw [hkill₁]; simp
        have hproj : e₁.inv ≫ b₁.bicone.fst =
            c.ι.app (P.ι.obj k) ≫ inv u₁ := by
          apply (cancel_mono u₁).1
          dsimp [u₁]
          have hprojc : b₁.bicone.fst ≫ b₁.bicone.inl ≫ e₁.hom ≫
              c.ι.app (P.ι.obj k) = e₁.hom ≫ c.ι.app (P.ι.obj k) := by
            have ht := congrArg
              (fun z => z ≫ e₁.hom ≫ c.ι.app (P.ι.obj k))
              (CategoryTheory.Limits.IsBilimit.binary_total b₁.isBilimit)
            have hz : b₁.bicone.snd ≫ b₁.bicone.inr ≫ e₁.hom ≫
                c.ι.app (P.ι.obj k) = 0 := by
              calc
                b₁.bicone.snd ≫ b₁.bicone.inr ≫ e₁.hom ≫
                    c.ι.app (P.ι.obj k) =
                    b₁.bicone.snd ≫
                      (b₁.bicone.inr ≫ e₁.hom ≫ c.ι.app (P.ι.obj k)) := by
                        simp only [Category.assoc]
                _ = 0 := by rw [hck]; simp
            simp only [Preadditive.add_comp, hz, add_zero, Category.assoc,
              Category.comp_id, Category.id_comp] at ht
            simpa only [Category.assoc] using ht
          calc
            (e₁.inv ≫ b₁.bicone.fst) ≫ b₁.bicone.inl ≫ e₁.hom ≫
                c.ι.app (P.ι.obj k) =
                e₁.inv ≫ (b₁.bicone.fst ≫ b₁.bicone.inl ≫ e₁.hom ≫
                  c.ι.app (P.ι.obj k)) := by simp only [Category.assoc]
            _ = e₁.inv ≫ e₁.hom ≫ c.ι.app (P.ι.obj k) := by rw [hprojc]
            _ = c.ι.app (P.ι.obj k) := by simp
            _ = (c.ι.app (P.ι.obj k) ≫ inv
                  (b₁.bicone.inl ≫ e₁.hom ≫ c.ι.app (P.ι.obj k))) ≫
                    b₁.bicone.inl ≫ e₁.hom ≫ c.ι.app (P.ι.obj k) := by
              simp [Category.assoc]
        have hd₀fst : d₀ ≫ e₁.inv ≫ b₁.bicone.fst = 0 := by
          rw [hproj]
          rw [← Category.assoc, hd₀c]
          simp
        have hd₀split : d₀ ≫ e₁.inv =
            d₀ ≫ e₁.inv ≫ b₁.bicone.snd ≫ b₁.bicone.inr := by
          apply b₁.isBilimit.isLimit.hom_ext
          intro q
          rcases q with ⟨⟨⟩⟩
          · change (d₀ ≫ e₁.inv) ≫ b₁.bicone.fst =
              (d₀ ≫ e₁.inv ≫ b₁.bicone.snd ≫ b₁.bicone.inr) ≫
                b₁.bicone.fst
            simp [Category.assoc, hd₀fst]
          · change (d₀ ≫ e₁.inv) ≫ b₁.bicone.snd =
              (d₀ ≫ e₁.inv ≫ b₁.bicone.snd ≫ b₁.bicone.inr) ≫
                b₁.bicone.snd
            simp [Category.assoc]
        have hd₀t : d₀ ≫ M.map (P.ι.map t₁) = 0 := by
          calc
            d₀ ≫ M.map (P.ι.map t₁) =
                d₀ ≫ e₁.inv ≫ e₁.hom ≫ M.map (P.ι.map t₁) := by
                  simp
            _ = (d₀ ≫ e₁.inv ≫ b₁.bicone.snd) ≫
                (b₁.bicone.inr ≫ e₁.hom ≫ M.map (P.ι.map t₁)) := by
                  simpa only [Category.assoc] using
                    congrArg (fun z => z ≫ e₁.hom ≫ M.map (P.ι.map t₁)) hd₀split
            _ = 0 := by
              simp only [Category.assoc]
              rw [hkill₁]
              simp
        have heq : M.map (P.ι.map (h ≫ t₁)) =
            c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map (f ≫ t₁)) := by
          have hsub :
              M.map (P.ι.map h) ≫ M.map (P.ι.map t₁) -
                (c.ι.app (P.ι.obj j') ≫ s ≫ M.map (P.ι.map f)) ≫
                  M.map (P.ι.map t₁) = 0 := by
            simpa [d₀, Category.assoc] using hd₀t
          have hEq := sub_eq_zero.mp hsub
          simpa [Functor.map_comp, Category.assoc] using hEq
        exact ⟨l₁, f ≫ t₁, h ≫ t₁, heq⟩
    apply (isEssentiallyConstantInd_comp_final_iff P.ι M).mpr
    exact ⟨d, hess⟩

/-- The dual characterization for cofiltered essentially constant diagrams. -/
theorem essentiallyConstantPro_iff_proLimitSplitting
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {A : Type u'} [Category.{v'} A] [Preadditive A]
    [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantProDiagram M ↔ ProLimitSplitting M := by
  have hdiagram : IsEssentiallyConstantProDiagram M ↔
      IsEssentiallyConstantIndDiagram M.op := by
    constructor
    · rintro ⟨c, hc⟩
      rcases hc with ⟨i, r, hr, hfactor⟩
      refine ⟨c.op, ?_⟩
      refine ⟨Opposite.op i, r.op, ?_, ?_⟩
      · simpa using congrArg Quiver.Hom.op hr
      · intro j
        rcases hfactor j.unop with ⟨k, f, g, hfg⟩
        refine ⟨Opposite.op k, f.op, g.op, ?_⟩
        simpa using congrArg Quiver.Hom.op hfg
    · rintro ⟨d, hd⟩
      let c := d.unop
      refine ⟨c, ?_⟩
      rcases hd with ⟨i, s, hs, hfactor⟩
      refine ⟨i.unop, s.unop, ?_, ?_⟩
      · dsimp [c]
        simpa using congrArg Quiver.Hom.unop hs
      · intro j
        rcases hfactor (Opposite.op j) with ⟨k, f, g, hfg⟩
        refine ⟨k.unop, f.unop, g.unop, ?_⟩
        dsimp [c]
        simpa using congrArg Quiver.Hom.unop hfg
  have hsplit : ProLimitSplitting M ↔ IndColimitSplitting M.op := by
    constructor
    · rintro ⟨c, hc, P, hP, hinitial, hdata⟩
      letI : IsCofiltered P.FullSubcategory := hP
      obtain ⟨hc⟩ := hc
      have hinitial' := (Functor.initial_iff_of_isCofiltered P.ι).mp hinitial
      let Q : ObjectProperty Iᵒᵖ := P.op
      have hQ : ∀ j : Iᵒᵖ, ∃ j' : Q.FullSubcategory,
          Nonempty (j ⟶ Q.ι.obj j') := by
        intro j
        obtain ⟨p, hp⟩ := hinitial'.1 j.unop
        let q : Q.FullSubcategory := ⟨Opposite.op p.obj, p.property⟩
        exact ⟨q, ⟨(Classical.choice hp).op⟩⟩
      have hQF :=
        Formalization.Books.Categories.Unit19.filtered_full_subcategory_isFiltered_and_isFinal Q hQ
      refine ⟨c.op, ⟨hc.op⟩, Q, hQF.1, hQF.2, ?_⟩
      intro q
      let p : P.FullSubcategory := ⟨q.obj.unop, q.property⟩
      obtain ⟨X', Z', b, e, hu, hkill⟩ := hdata p
      refine ⟨Opposite.op X', Opposite.op Z', b.op, e.op.symm, ?_, ?_⟩
      · letI := hu
        dsimp [BinaryBiproductData.op, BinaryBicone.op, Iso.symm]
        have hi0 : IsIso (c.π.app p.obj ≫ e.inv ≫ b.bicone.fst) := hu
        letI := hi0
        have hi : IsIso ((c.π.app p.obj ≫ e.inv ≫ b.bicone.fst).op) := inferInstance
        simpa [p, Iso.op, Iso.symm, ← op_comp] using hi
      · obtain ⟨p', f, hzero⟩ := hkill
        let q' : Q.FullSubcategory := ⟨Opposite.op p'.obj, p'.property⟩
        refine ⟨q', ?_, ?_⟩
        · have hqobj : q.obj = Opposite.op p.obj := by simp [p]
          have hqobj' : q'.obj = Opposite.op p'.obj := by rfl
          exact ObjectProperty.homMk
            (eqToHom hqobj ≫ f.hom.op ≫ eqToHom hqobj'.symm)
        · simpa [q', BinaryBiproductData.op, BinaryBicone.op] using
            congrArg Quiver.Hom.op hzero
    · rintro ⟨d, hd, Q, hQ, hfinal, hdata⟩
      letI : IsFiltered Q.FullSubcategory := hQ
      obtain ⟨hd⟩ := hd
      have hfinal' := (Functor.final_iff_of_isFiltered Q.ι).mp hfinal
      let P : ObjectProperty I := Q.unop
      have hP₁ : ∀ j : I, ∃ j' : P.FullSubcategory,
          Nonempty (P.ι.obj j' ⟶ j) := by
        intro j
        obtain ⟨q, hq⟩ := hfinal'.1 (Opposite.op j)
        let p : P.FullSubcategory := ⟨q.obj.unop, q.property⟩
        exact ⟨p, ⟨(Classical.choice hq).unop⟩⟩
      letI : IsCofiltered P.FullSubcategory := by
        let E := ObjectProperty.opEquivalence P
        letI : IsFiltered P.op.FullSubcategory := by
          dsimp [P]
          exact hQ
        letI : IsFiltered P.FullSubcategoryᵒᵖ :=
          IsFiltered.of_equivalence E
        exact isCofiltered_of_isFiltered_op _
      have hinitial : Functor.Initial P.ι := by
        apply Functor.initial_of_exists_of_isCofiltered P.ι hP₁
        intro d' p s s'
        let q : Q.FullSubcategory := ⟨Opposite.op p.obj, p.property⟩
        obtain ⟨q', t, ht⟩ :=
          hfinal'.2 (d := Opposite.op d') (c := q)
            (Quiver.Hom.op s) (Quiver.Hom.op s')
        let p' : P.FullSubcategory := ⟨q'.obj.unop, q'.property⟩
        refine ⟨p', ObjectProperty.homMk (by
          change q'.obj.unop ⟶ q.obj.unop
          exact t.hom.unop), ?_⟩
        change t.hom.unop ≫ s = t.hom.unop ≫ s'
        simpa only [ObjectProperty.ι_map, ObjectProperty.ι_obj, unop_comp,
          Quiver.Hom.unop_op] using
          congrArg Quiver.Hom.unop ht
      refine ⟨d.unop, ⟨hd.unop⟩, P, inferInstance, hinitial, ?_⟩
      intro p
      let q : Q.FullSubcategory := ⟨Opposite.op p.obj, p.property⟩
      obtain ⟨X', Z', b', e', hu', hkill'⟩ := hdata q
      let b : BinaryBiproductData X'.unop Z'.unop :=
        { bicone :=
            { pt := b'.bicone.pt.unop
              fst := b'.bicone.inl.unop
              snd := b'.bicone.inr.unop
              inl := b'.bicone.fst.unop
              inr := b'.bicone.snd.unop
              inl_fst := by
                simpa only [unop_comp, unop_id] using
                  congrArg Quiver.Hom.unop b'.bicone.inl_fst
              inl_snd := by
                simpa only [unop_comp, unop_zero] using
                  congrArg Quiver.Hom.unop b'.bicone.inr_fst
              inr_fst := by
                simpa only [unop_comp, unop_zero] using
                  congrArg Quiver.Hom.unop b'.bicone.inl_snd
              inr_snd := by
                simpa only [unop_comp, unop_id] using
                  congrArg Quiver.Hom.unop b'.bicone.inr_snd }
          isBilimit :=
            { isLimit := by
                convert BinaryCofan.IsColimit.unop b'.isBilimit.isColimit using 1 <;> rfl
              isColimit := by
                convert BinaryFan.IsLimit.unop b'.isBilimit.isLimit using 1 <;> rfl } }
      refine ⟨X'.unop, Z'.unop, b, e'.unop.symm, ?_, ?_⟩
      · letI := hu'
        have hi0 : IsIso
            (b'.bicone.inl ≫ e'.hom ≫ d.ι.app (Q.ι.obj q)) := hu'
        letI := hi0
        have hi : IsIso
            ((b'.bicone.inl ≫ e'.hom ≫ d.ι.app (Q.ι.obj q)).unop) := inferInstance
        simpa [b, q, Iso.unop, Iso.symm, ← unop_comp] using hi
      · obtain ⟨q', f, hzero⟩ := hkill'
        let p' : P.FullSubcategory := ⟨q'.obj.unop, q'.property⟩
        refine ⟨p', ObjectProperty.homMk (by
          change q'.obj.unop ⟶ q.obj.unop
          exact f.hom.unop), ?_⟩
        change M.map f.hom.unop ≫ e'.hom.unop ≫ b'.bicone.inr.unop = 0
        simpa using congrArg Quiver.Hom.unop hzero
  constructor
  · intro h
    exact (hsplit.mpr ((essentiallyConstantInd_iff_indColimitSplitting M.op).mp
      (hdiagram.mp h)))
  · intro h
    exact hdiagram.mpr ((essentiallyConstantInd_iff_indColimitSplitting M.op).mpr
      (hsplit.mp h))

/-! ## Colimits and pointwise direct sums -/

/-- The pointwise direct sum of two diagrams in an additive category.

Mathlib exposes the pointwise bicone once binary biproducts are available.
The additive-category interface supplies finite biproducts, from which the
canonical binary-biproduct existence theorem gives the local instance needed
by that construction. -/
def pointwiseDirectSum
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    (F G : I ⥤ A) : I ⥤ A := by
  letI : HasBinaryBiproducts A :=
    hasBinaryBiproducts_of_finite_biproducts (C := A)
  exact (pointwiseBinaryBiproductData F G).bicone.pt

/-- A colimit of a pointwise binary biproduct exists exactly when the two
component colimits exist. -/
theorem hasColimit_biprod_iff
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A] (F G : I ⥤ A) :
    HasColimit (pointwiseDirectSum F G) ↔ HasColimit F ∧ HasColimit G := by
  letI : HasBinaryBiproducts A :=
    hasBinaryBiproducts_of_finite_biproducts (C := A)
  let B : BinaryBiproductData F G := pointwiseBinaryBiproductData F G
  change HasColimit B.bicone.pt ↔ HasColimit F ∧ HasColimit G
  have htotal (i : I) :
      B.bicone.fst.app i ≫ B.bicone.inl.app i +
          B.bicone.snd.app i ≫ B.bicone.inr.app i = 𝟙 _ := by
    simpa using congrArg (fun z => z.app i)
      (CategoryTheory.Limits.IsBilimit.binary_total B.isBilimit)
  have hinl_fst (i : I) :
      B.bicone.inl.app i ≫ B.bicone.fst.app i = 𝟙 _ := by
    have h := congrArg (fun z => z.app i) B.bicone.inl_fst
    exact h
  have hinl_snd (i : I) :
      B.bicone.inl.app i ≫ B.bicone.snd.app i = 0 := by
    have h := congrArg (fun z => z.app i) B.bicone.inl_snd
    exact h
  have hinr_fst (i : I) :
      B.bicone.inr.app i ≫ B.bicone.fst.app i = 0 := by
    have h := congrArg (fun z => z.app i) B.bicone.inr_fst
    exact h
  have hinr_snd (i : I) :
      B.bicone.inr.app i ≫ B.bicone.snd.app i = 𝟙 _ := by
    have h := congrArg (fun z => z.app i) B.bicone.inr_snd
    exact h
  have hinl_fst_comp (i : I) {X : A} (f : F.obj i ⟶ X) :
      B.bicone.inl.app i ≫ B.bicone.fst.app i ≫ f = f := by
    rw [← Category.assoc, hinl_fst i, Category.id_comp]
  have hinl_snd_comp (i : I) {X : A} (f : G.obj i ⟶ X) :
      B.bicone.inl.app i ≫ B.bicone.snd.app i ≫ f = 0 := by
    rw [← Category.assoc, hinl_snd i, zero_comp]
  have hinr_fst_comp (i : I) {X : A} (f : F.obj i ⟶ X) :
      B.bicone.inr.app i ≫ B.bicone.fst.app i ≫ f = 0 := by
    rw [← Category.assoc, hinr_fst i, zero_comp]
  have hinr_snd_comp (i : I) {X : A} (f : G.obj i ⟶ X) :
      B.bicone.inr.app i ≫ B.bicone.snd.app i ≫ f = f := by
    rw [← Category.assoc, hinr_snd i, Category.id_comp]
  constructor
  · intro h
    letI : HasColimit B.bicone.pt := h
    let c : Cocone B.bicone.pt := colimit.cocone B.bicone.pt
    let hc : IsColimit c := colimit.isColimit B.bicone.pt
    let α : B.bicone.pt ⟶ B.bicone.pt :=
      B.bicone.fst ≫ B.bicone.inl
    have hα : α ≫ α = α := by
      ext i
      dsimp [α]
      change (B.bicone.fst.app i ≫ B.bicone.inl.app i) ≫
          (B.bicone.fst.app i ≫ B.bicone.inl.app i) = _
      calc
        _ = B.bicone.fst.app i ≫
            (B.bicone.inl.app i ≫ B.bicone.fst.app i) ≫
              B.bicone.inl.app i := by simp [Category.assoc]
        _ = B.bicone.fst.app i ≫ B.bicone.inl.app i := by
          rw [hinl_fst i]
          simp
    let cα : Cocone B.bicone.pt :=
      { pt := c.pt
        ι := α ≫ c.ι }
    let q : c.pt ⟶ c.pt := hc.desc cα
    have hqc (i : I) : c.ι.app i ≫ q = α.app i ≫ c.ι.app i := by
      change c.ι.app i ≫ q = α.app i ≫ c.ι.app i
      exact hc.fac cα i
    have hq : q ≫ q = q := by
      apply hc.hom_ext
      intro i
      have hαi : α.app i ≫ α.app i = α.app i := by
        simpa only [NatTrans.comp_app] using congrArg (fun z => z.app i) hα
      calc
        c.ι.app i ≫ q ≫ q = (c.ι.app i ≫ q) ≫ q := by
          simp only [Category.assoc]
        _ = (α.app i ≫ c.ι.app i) ≫ q := by rw [hqc i]
        _ = α.app i ≫ (c.ι.app i ≫ q) := by simp only [Category.assoc]
        _ = α.app i ≫ (α.app i ≫ c.ι.app i) := by rw [hqc i]
        _ = α.app i ≫ c.ι.app i := by
          rw [← Category.assoc, hαi]
        _ = c.ι.app i ≫ q := (hqc i).symm
    let p := Formalization.Books.Homology.Unit03.idempotentComplement q
    have hp : p ≫ p = p :=
      (Formalization.Books.Homology.Unit03.idempotent_complement_relations q hq).2.2
    obtain ⟨X, Z, b, e, he⟩ :=
      (Formalization.Books.Homology.Unit04.karoubian_iff_idempotent_direct_sum_decomposition
        (C := A)).mp
        ‹IsIdempotentComplete A› _ _ hp
    have hqp : q = 𝟙 _ - p := by
      simp [p, Formalization.Books.Homology.Unit03.idempotentComplement]
    have hconj : e.inv ≫ q ≫ e.hom = b.bicone.fst ≫ b.bicone.inl := by
      apply b.isBilimit.isLimit.hom_ext
      intro j
      rcases j with ⟨⟨⟩⟩
      · change (e.inv ≫ q ≫ e.hom) ≫ b.bicone.fst =
          (b.bicone.fst ≫ b.bicone.inl) ≫ b.bicone.fst
        simp [hqp, Category.assoc, he]
      · change (e.inv ≫ q ≫ e.hom) ≫ b.bicone.snd =
          (b.bicone.fst ≫ b.bicone.inl) ≫ b.bicone.snd
        simp [hqp, Category.assoc, he]
    have hpconj : e.inv ≫ p ≫ e.hom = b.bicone.snd ≫ b.bicone.inr := by
      apply b.isBilimit.isLimit.hom_ext
      intro j
      rcases j with ⟨⟨⟩⟩
      · change (e.inv ≫ p ≫ e.hom) ≫ b.bicone.fst =
          (b.bicone.snd ≫ b.bicone.inr) ≫ b.bicone.fst
        simp [Category.assoc, he]
      · change (e.inv ≫ p ≫ e.hom) ≫ b.bicone.snd =
          (b.bicone.snd ≫ b.bicone.inr) ≫ b.bicone.snd
        simp [Category.assoc, he]
    have hqX : q ≫ e.hom ≫ b.bicone.fst = e.hom ≫ b.bicone.fst := by
      calc
        q ≫ e.hom ≫ b.bicone.fst =
            e.hom ≫ (e.inv ≫ q ≫ e.hom) ≫ b.bicone.fst := by
              simp [Category.assoc]
        _ = e.hom ≫ (b.bicone.fst ≫ b.bicone.inl) ≫ b.bicone.fst := by
              rw [hconj]
        _ = e.hom ≫ b.bicone.fst := by simp [Category.assoc]
    have hpZ : p ≫ e.hom ≫ b.bicone.snd = e.hom ≫ b.bicone.snd := by
      calc
        p ≫ e.hom ≫ b.bicone.snd =
            e.hom ≫ (e.inv ≫ p ≫ e.hom) ≫ b.bicone.snd := by
              simp [Category.assoc]
        _ = e.hom ≫ (b.bicone.snd ≫ b.bicone.inr) ≫ b.bicone.snd := by
              rw [hpconj]
        _ = e.hom ≫ b.bicone.snd := by simp [Category.assoc]
    have hpq : p = 𝟙 _ - q := by
      simp [p, Formalization.Books.Homology.Unit03.idempotentComplement]
    have hXproj : e.hom ≫ b.bicone.fst ≫ b.bicone.inl ≫ e.inv = q := by
      calc
        e.hom ≫ b.bicone.fst ≫ b.bicone.inl ≫ e.inv =
            e.hom ≫ (b.bicone.fst ≫ b.bicone.inl) ≫ e.inv := by
              simp only [Category.assoc]
        _ = e.hom ≫ (e.inv ≫ q ≫ e.hom) ≫ e.inv := by rw [hconj]
        _ = q := by simp [Category.assoc]
    have hZproj : e.hom ≫ b.bicone.snd ≫ b.bicone.inr ≫ e.inv = p := by
      calc
        e.hom ≫ b.bicone.snd ≫ b.bicone.inr ≫ e.inv =
            e.hom ≫ (b.bicone.snd ≫ b.bicone.inr) ≫ e.inv := by
              simp only [Category.assoc]
        _ = e.hom ≫ (e.inv ≫ p ≫ e.hom) ≫ e.inv := by rw [hpconj]
        _ = p := by simp [Category.assoc]
    have hcp (i : I) : c.ι.app i ≫ p =
        B.bicone.snd.app i ≫ B.bicone.inr.app i ≫ c.ι.app i := by
      have hpc : 𝟙 _ - B.bicone.fst.app i ≫ B.bicone.inl.app i =
          B.bicone.snd.app i ≫ B.bicone.inr.app i := by
        have ht := htotal i
        rw [← ht]
        abel
      rw [hpq, Preadditive.comp_sub]
      simp only [Functor.const_obj_obj, Category.comp_id]
      rw [hqc i]
      simp only [α, NatTrans.comp_app]
      calc
        _ = (𝟙 _ - B.bicone.fst.app i ≫ B.bicone.inl.app i) ≫
            c.ι.app i := by simp [Preadditive.sub_comp, Category.assoc]
        _ = _ := by rw [hpc]; simp only [Category.assoc]
    have hαc (i : I) : α.app i ≫ c.ι.app i =
        B.bicone.fst.app i ≫ B.bicone.inl.app i ≫ c.ι.app i := by
      simp [α]
    let dF : Cocone F :=
      { pt := X
        ι := B.bicone.inl ≫ c.ι ≫ (Functor.const I).map
          (e.hom ≫ b.bicone.fst) }
    let dG : Cocone G :=
      { pt := Z
        ι := B.bicone.inr ≫ c.ι ≫ (Functor.const I).map
          (e.hom ≫ b.bicone.snd) }
    refine ⟨⟨dF, ?_⟩, ⟨dG, ?_⟩⟩
    · refine
        { desc := fun s =>
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.fst ≫ s.ι }
            b.bicone.inl ≫ e.inv ≫ hc.desc sH
          fac := by
            intro s i
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.fst ≫ s.ι }
            have hfac := hc.fac sH i
            have hfac' : c.ι.app i ≫ hc.desc sH =
                B.bicone.fst.app i ≫ s.ι.app i := by
              change c.ι.app i ≫ hc.desc sH = B.bicone.fst.app i ≫ s.ι.app i
              exact hfac
            dsimp [dF]
            simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
            calc
              B.bicone.inl.app i ≫ c.ι.app i ≫ e.hom ≫ b.bicone.fst ≫
                    b.bicone.inl ≫ e.inv ≫ hc.desc sH =
                  B.bicone.inl.app i ≫ c.ι.app i ≫ q ≫ hc.desc sH := by
                    simpa only [Category.assoc] using congrArg
                      (fun z => B.bicone.inl.app i ≫ c.ι.app i ≫ z ≫ hc.desc sH)
                      hXproj
              _ = B.bicone.inl.app i ≫ B.bicone.fst.app i ≫
                    B.bicone.inl.app i ≫ c.ι.app i ≫ hc.desc sH := by
                    have hi := congrArg
                      (fun z => z ≫ hc.desc sH) (hqc i)
                    simpa [hαc i, Category.assoc] using
                      congrArg (fun z => B.bicone.inl.app i ≫ z) hi
              _ = s.ι.app i := by
                    rw [hfac']
                    rw [hinl_fst_comp i, hinl_fst_comp i]
          uniq := by
            intro s m hm
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.fst ≫ s.ι }
            have hdesc : e.hom ≫ b.bicone.fst ≫ m = hc.desc sH := by
              apply hc.hom_ext
              intro i
              have hfac := hc.fac sH i
              change c.ι.app i ≫ hc.desc sH = B.bicone.fst.app i ≫ s.ι.app i at hfac
              have hqfac : c.ι.app i ≫
                  (e.hom ≫ b.bicone.fst ≫ m) =
                  B.bicone.fst.app i ≫ s.ι.app i := by
                calc
                  c.ι.app i ≫ (e.hom ≫ b.bicone.fst ≫ m) =
                      c.ι.app i ≫ q ≫ (e.hom ≫ b.bicone.fst ≫ m) := by
                        simpa only [Category.assoc] using
                          (congrArg (fun z => c.ι.app i ≫ z ≫ m) hqX).symm
                  _ = B.bicone.fst.app i ≫
                      (B.bicone.inl.app i ≫ c.ι.app i ≫ e.hom ≫ b.bicone.fst ≫ m) := by
                        have hi := congrArg
                          (fun z => z ≫ e.hom ≫ b.bicone.fst ≫ m) (hqc i)
                        simpa [hαc i, Category.assoc] using hi
                  _ = B.bicone.fst.app i ≫ s.ι.app i := by
                        have hm' := hm i
                        dsimp [dF] at hm'
                        have hi := congrArg (fun z => B.bicone.fst.app i ≫ z) hm'
                        simpa [Category.assoc] using hi
              calc
                c.ι.app i ≫ (e.hom ≫ b.bicone.fst ≫ m) =
                    B.bicone.fst.app i ≫ s.ι.app i := hqfac
                _ = c.ι.app i ≫ hc.desc sH := hfac.symm
            change m = b.bicone.inl ≫ e.inv ≫ hc.desc sH
            have hdesc' : b.bicone.fst ≫ m = e.inv ≫ hc.desc sH := by
              calc
                b.bicone.fst ≫ m = e.inv ≫ e.hom ≫ b.bicone.fst ≫ m := by
                  simp [Category.assoc]
                _ = e.inv ≫ hc.desc sH := by rw [hdesc]
            calc
              m = b.bicone.inl ≫ b.bicone.fst ≫ m := by simp
              _ = b.bicone.inl ≫ e.inv ≫ hc.desc sH := by rw [hdesc']
          }
    · refine
        { desc := fun s =>
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.snd ≫ s.ι }
            b.bicone.inr ≫ e.inv ≫ hc.desc sH
          fac := by
            intro s i
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.snd ≫ s.ι }
            have hfac := hc.fac sH i
            have hfac' : c.ι.app i ≫ hc.desc sH =
                B.bicone.snd.app i ≫ s.ι.app i := by
              change c.ι.app i ≫ hc.desc sH = B.bicone.snd.app i ≫ s.ι.app i
              exact hfac
            dsimp [dG]
            simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
            calc
              B.bicone.inr.app i ≫ c.ι.app i ≫ e.hom ≫ b.bicone.snd ≫
                    b.bicone.inr ≫ e.inv ≫ hc.desc sH =
                  B.bicone.inr.app i ≫ c.ι.app i ≫ p ≫ hc.desc sH := by
                    simpa only [Category.assoc] using congrArg
                      (fun z => B.bicone.inr.app i ≫ c.ι.app i ≫ z ≫ hc.desc sH)
                      hZproj
              _ = B.bicone.inr.app i ≫ B.bicone.snd.app i ≫
                    B.bicone.inr.app i ≫ c.ι.app i ≫ hc.desc sH := by
                    have hi := congrArg
                      (fun z => z ≫ hc.desc sH) (hcp i)
                    simpa [Category.assoc] using
                      congrArg (fun z => B.bicone.inr.app i ≫ z) hi
              _ = s.ι.app i := by
                    rw [hfac']
                    rw [hinr_snd_comp i, hinr_snd_comp i]
          uniq := by
            intro s m hm
            let sH : Cocone B.bicone.pt := { pt := s.pt, ι := B.bicone.snd ≫ s.ι }
            have hdesc : e.hom ≫ b.bicone.snd ≫ m = hc.desc sH := by
              apply hc.hom_ext
              intro i
              have hfac := hc.fac sH i
              change c.ι.app i ≫ hc.desc sH = B.bicone.snd.app i ≫ s.ι.app i at hfac
              have hqfac : c.ι.app i ≫
                  (e.hom ≫ b.bicone.snd ≫ m) =
                  B.bicone.snd.app i ≫ s.ι.app i := by
                calc
                  c.ι.app i ≫ (e.hom ≫ b.bicone.snd ≫ m) =
                      c.ι.app i ≫ p ≫ (e.hom ≫ b.bicone.snd ≫ m) := by
                        simpa only [Category.assoc] using
                          (congrArg (fun z => c.ι.app i ≫ z ≫ m) hpZ).symm
                  _ = B.bicone.snd.app i ≫
                      (B.bicone.inr.app i ≫ c.ι.app i ≫ e.hom ≫ b.bicone.snd ≫ m) := by
                        have hi := congrArg
                          (fun z => z ≫ e.hom ≫ b.bicone.snd ≫ m) (hcp i)
                        simpa [Category.assoc] using hi
                  _ = B.bicone.snd.app i ≫ s.ι.app i := by
                        have hm' := hm i
                        dsimp [dG] at hm'
                        have hi := congrArg (fun z => B.bicone.snd.app i ≫ z) hm'
                        simpa [Category.assoc] using hi
              calc
                c.ι.app i ≫ (e.hom ≫ b.bicone.snd ≫ m) =
                    B.bicone.snd.app i ≫ s.ι.app i := hqfac
                _ = c.ι.app i ≫ hc.desc sH := hfac.symm
            change m = b.bicone.inr ≫ e.inv ≫ hc.desc sH
            have hdesc' : b.bicone.snd ≫ m = e.inv ≫ hc.desc sH := by
              calc
                b.bicone.snd ≫ m = e.inv ≫ e.hom ≫ b.bicone.snd ≫ m := by
                  simp [Category.assoc]
                _ = e.inv ≫ hc.desc sH := by rw [hdesc]
            calc
              m = b.bicone.inr ≫ b.bicone.snd ≫ m := by simp
              _ = b.bicone.inr ≫ e.inv ≫ hc.desc sH := by rw [hdesc']
          }
  · rintro ⟨hF, hG⟩
    letI : HasColimit F := hF
    letI : HasColimit G := hG
    let b : BinaryBiproductData (colimit F) (colimit G) :=
      getBinaryBiproductData (colimit F) (colimit G)
    let c : Cocone B.bicone.pt :=
      { pt := b.bicone.pt
        ι :=
          { app := fun i =>
              (B.bicone.fst.app i ≫ colimit.ι F i ≫ b.bicone.inl) +
                (B.bicone.snd.app i ≫ colimit.ι G i ≫ b.bicone.inr)
            naturality := by
              intro i j f
              simp only [Category.assoc, Preadditive.comp_add]
              calc
                B.bicone.pt.map f ≫ B.bicone.fst.app j ≫ colimit.ι F j ≫
                    b.bicone.inl +
                    B.bicone.pt.map f ≫ B.bicone.snd.app j ≫ colimit.ι G j ≫
                    b.bicone.inr =
                    (B.bicone.pt.map f ≫ B.bicone.fst.app j) ≫
                        colimit.ι F j ≫ b.bicone.inl +
                      (B.bicone.pt.map f ≫ B.bicone.snd.app j) ≫
                        colimit.ι G j ≫ b.bicone.inr := by
                          simp only [Category.assoc]
                _ = (B.bicone.fst.app i ≫ F.map f) ≫
                        colimit.ι F j ≫ b.bicone.inl +
                      (B.bicone.snd.app i ≫ G.map f) ≫
                        colimit.ι G j ≫ b.bicone.inr := by
                          rw [B.bicone.fst.naturality f, B.bicone.snd.naturality f]
                _ = B.bicone.fst.app i ≫ colimit.ι F i ≫ b.bicone.inl +
                      B.bicone.snd.app i ≫ colimit.ι G i ≫ b.bicone.inr := by
                          have hFi :
                              B.bicone.fst.app i ≫ F.map f ≫ colimit.ι F j ≫ b.bicone.inl =
                                B.bicone.fst.app i ≫ colimit.ι F i ≫ b.bicone.inl := by
                            simpa only [Category.assoc] using
                              congrArg (fun z => B.bicone.fst.app i ≫ z ≫ b.bicone.inl)
                                (colimit.w F f)
                          have hGi :
                              B.bicone.snd.app i ≫ G.map f ≫ colimit.ι G j ≫ b.bicone.inr =
                                B.bicone.snd.app i ≫ colimit.ι G i ≫ b.bicone.inr := by
                            simpa only [Category.assoc] using
                              congrArg (fun z => B.bicone.snd.app i ≫ z ≫ b.bicone.inr)
                                (colimit.w G f)
                          simpa only [Category.assoc] using
                            congrArg₂ (fun x y => x + y) hFi hGi
                _ = (B.bicone.fst.app i ≫ colimit.ι F i ≫ b.bicone.inl +
                    B.bicone.snd.app i ≫ colimit.ι G i ≫ b.bicone.inr) ≫
                    ((Functor.const I).obj b.bicone.pt).map f := by simp } }
    refine ⟨⟨c, ?_⟩⟩
    refine
      { desc := fun s =>
          (b.bicone.fst ≫ (colimit.isColimit F).desc
              { pt := s.pt
                ι := B.bicone.inl ≫ s.ι }) +
            (b.bicone.snd ≫ (colimit.isColimit G).desc
              { pt := s.pt
                ι := B.bicone.inr ≫ s.ι })
        fac := by
          intro s i
          simp [c, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
            (colimit.isColimit F).fac, (colimit.isColimit G).fac]
          have hi := congrArg (fun z => z ≫ s.ι.app i) (htotal i)
          simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp] using hi
        uniq := by
          intro s m hm
          apply b.isBilimit.isColimit.hom_ext
          intro j
          rcases j with ⟨⟨⟩⟩
          · apply (colimit.isColimit F).hom_ext
            intro i
            have hleg :
                B.bicone.inl.app i ≫ c.ι.app i = colimit.ι F i ≫ b.bicone.inl := by
              dsimp [c]
              simp only [Preadditive.comp_add, Category.assoc]
              rw [hinl_fst_comp i, hinl_snd_comp i]
              simp
            have hfac := (colimit.isColimit F).fac
              { pt := s.pt, ι := B.bicone.inl ≫ s.ι } i
            calc
              colimit.ι F i ≫ b.bicone.inl ≫ m =
                  (B.bicone.inl.app i ≫ c.ι.app i) ≫ m := by
                    rw [hleg]
                    simp only [Category.assoc]
              _ = B.bicone.inl.app i ≫ c.ι.app i ≫ m := by
                    simp only [Category.assoc]
              _ = B.bicone.inl.app i ≫ s.ι.app i := by rw [hm i]
              _ = colimit.ι F i ≫ b.bicone.inl ≫
                  (b.bicone.fst ≫ (colimit.isColimit F).desc
                    { pt := s.pt, ι := B.bicone.inl ≫ s.ι } +
                    b.bicone.snd ≫ (colimit.isColimit G).desc
                      { pt := s.pt, ι := B.bicone.inr ≫ s.ι }) := by
                    simpa [Category.assoc] using hfac.symm
          · apply (colimit.isColimit G).hom_ext
            intro i
            have hleg :
                B.bicone.inr.app i ≫ c.ι.app i = colimit.ι G i ≫ b.bicone.inr := by
              dsimp [c]
              simp only [Preadditive.comp_add, Category.assoc]
              rw [hinr_fst_comp i, hinr_snd_comp i]
              simp
            have hfac := (colimit.isColimit G).fac
              { pt := s.pt, ι := B.bicone.inr ≫ s.ι } i
            calc
              colimit.ι G i ≫ b.bicone.inr ≫ m =
                  (B.bicone.inr.app i ≫ c.ι.app i) ≫ m := by
                    rw [hleg]
                    simp only [Category.assoc]
              _ = B.bicone.inr.app i ≫ c.ι.app i ≫ m := by
                    simp only [Category.assoc]
              _ = B.bicone.inr.app i ≫ s.ι.app i := by rw [hm i]
              _ = colimit.ι G i ≫ b.bicone.inr ≫
                  (b.bicone.fst ≫ (colimit.isColimit F).desc
                    { pt := s.pt, ι := B.bicone.inl ≫ s.ι } +
                    b.bicone.snd ≫ (colimit.isColimit G).desc
                      { pt := s.pt, ι := B.bicone.inr ≫ s.ι }) := by
                    simpa [Category.assoc] using hfac.symm }

/-- When they exist, the colimit of a pointwise binary biproduct is the
binary biproduct of the colimits. -/
theorem colimit_biprod_iso
    {I : Type u} [Category.{v} I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A] (F G : I ⥤ A)
    [HasColimit (pointwiseDirectSum F G)] [HasColimit F] [HasColimit G] :
    ∃ (b : BinaryBiproductData (colimit F) (colimit G)),
      Nonempty (colimit (pointwiseDirectSum F G) ≅ b.bicone.pt) := by
  letI : HasBinaryBiproducts A :=
    hasBinaryBiproducts_of_finite_biproducts (C := A)
  let B : BinaryBiproductData F G := pointwiseBinaryBiproductData F G
  letI : HasColimit B.bicone.pt := ‹HasColimit (pointwiseDirectSum F G)›
  change ∃ (b : BinaryBiproductData (colimit F) (colimit G)),
    Nonempty (colimit B.bicone.pt ≅ b.bicone.pt)
  let b : BinaryBiproductData (colimit F) (colimit G) :=
    getBinaryBiproductData (colimit F) (colimit G)
  have htotal (i : I) :
      B.bicone.fst.app i ≫ B.bicone.inl.app i +
          B.bicone.snd.app i ≫ B.bicone.inr.app i = 𝟙 _ := by
    simpa using congrArg (fun z => z.app i)
      (CategoryTheory.Limits.IsBilimit.binary_total B.isBilimit)
  have hinl_fst (i : I) :
      B.bicone.inl.app i ≫ B.bicone.fst.app i = 𝟙 _ := by
    exact congrArg (fun z => z.app i) B.bicone.inl_fst
  have hinr_snd (i : I) :
      B.bicone.inr.app i ≫ B.bicone.snd.app i = 𝟙 _ := by
    exact congrArg (fun z => z.app i) B.bicone.inr_snd
  have hinl_snd (i : I) :
      B.bicone.inl.app i ≫ B.bicone.snd.app i = 0 := by
    exact congrArg (fun z => z.app i) B.bicone.inl_snd
  have hinr_fst (i : I) :
      B.bicone.inr.app i ≫ B.bicone.fst.app i = 0 := by
    exact congrArg (fun z => z.app i) B.bicone.inr_fst
  have hinl_fst_comp (i : I) {X : A} (f' : F.obj i ⟶ X) :
      B.bicone.inl.app i ≫ B.bicone.fst.app i ≫ f' = f' := by
    rw [← Category.assoc]
    rw [hinl_fst i, Category.id_comp]
  have hinr_snd_comp (i : I) {X : A} (f' : G.obj i ⟶ X) :
      B.bicone.inr.app i ≫ B.bicone.snd.app i ≫ f' = f' := by
    rw [← Category.assoc]
    rw [hinr_snd i, Category.id_comp]
  have hinl_snd_comp (i : I) {X : A} (f' : G.obj i ⟶ X) :
      B.bicone.inl.app i ≫ B.bicone.snd.app i ≫ f' = 0 := by
    rw [← Category.assoc]
    rw [hinl_snd i, zero_comp]
  have hinr_fst_comp (i : I) {X : A} (f' : F.obj i ⟶ X) :
      B.bicone.inr.app i ≫ B.bicone.fst.app i ≫ f' = 0 := by
    rw [← Category.assoc]
    rw [hinr_fst i, zero_comp]
  let c : Cocone B.bicone.pt :=
    { pt := b.bicone.pt
      ι :=
        (B.bicone.fst ≫ (colimit.cocone F).ι ≫
            (Functor.const I).map b.bicone.inl) +
          (B.bicone.snd ≫ (colimit.cocone G).ι ≫
            (Functor.const I).map b.bicone.inr) }
  let dF : Cocone F :=
    { pt := colimit B.bicone.pt
      ι := B.bicone.inl ≫ (colimit.cocone B.bicone.pt).ι }
  let dG : Cocone G :=
    { pt := colimit B.bicone.pt
      ι := B.bicone.inr ≫ (colimit.cocone B.bicone.pt).ι }
  let f : colimit B.bicone.pt ⟶ b.bicone.pt :=
    colimit.desc B.bicone.pt c
  let g : b.bicone.pt ⟶ colimit B.bicone.pt :=
    (b.bicone.fst ≫ (colimit.isColimit F).desc dF) +
      (b.bicone.snd ≫ (colimit.isColimit G).desc dG)
  refine ⟨b, ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
  · apply (colimit.isColimit B.bicone.pt).hom_ext
    intro i
    have hF := (colimit.isColimit F).fac dF i
    have hG := (colimit.isColimit G).fac dG i
    have hc := (colimit.isColimit B.bicone.pt).fac c i
    dsimp [dF] at hF
    dsimp [dG] at hG
    dsimp [c, g] at hc ⊢
    rw [← Category.assoc, hc]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    simp [Category.assoc]
    dsimp [dF, dG]
    have hi := congrArg (fun z => z ≫ colimit.ι B.bicone.pt i) (htotal i)
    simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp] using hi
  · apply b.isBilimit.isColimit.hom_ext
    intro j
    rcases j with ⟨⟨⟩⟩
    · apply (colimit.isColimit F).hom_ext
      intro i
      have hF := (colimit.isColimit F).fac dF i
      have hc := (colimit.isColimit B.bicone.pt).fac c i
      dsimp [g, dF, c] at hF hc ⊢
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
      simp [Category.assoc]
      rw [hc]
      simp only [Preadditive.comp_add, Category.assoc]
      rw [hinl_fst_comp, hinl_snd_comp]
      simp only [zero_add, add_zero]
    · apply (colimit.isColimit G).hom_ext
      intro i
      have hG := (colimit.isColimit G).fac dG i
      have hc := (colimit.isColimit B.bicone.pt).fac c i
      dsimp [g, dG, c] at hG hc ⊢
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
      simp [Category.assoc]
      rw [hc]
      simp only [Preadditive.comp_add, Category.assoc]
      rw [hinr_fst_comp, hinr_snd_comp]
      simp only [zero_add, add_zero]

/-! ## Direct sums of essentially constant systems -/

/-- In a filtered additive Karoubian category, a pointwise direct sum is
essentially constant exactly when both summands are. -/
theorem essentiallyConstantInd_biprod_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {A : Type u'} [Category.{v'} A]
    [Formalization.Books.Homology.Unit03.AdditiveCategory A]
    [IsIdempotentComplete A]
    (F G : I ⥤ A) :
    IsEssentiallyConstantIndDiagram (pointwiseDirectSum F G) ↔
      IsEssentiallyConstantIndDiagram F ∧
        IsEssentiallyConstantIndDiagram G := by
  sorry

end Formalization.Books.Homology.Unit30
