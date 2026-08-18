import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Formalization.Books.Derived.Unit08.HomotopyCategory

/-!
# Derived Categories, Chapter 9: cones and termwise split sequences

The source's cone is Mathlib's canonical `CochainComplex.mappingCone`.  Its
homotopy-category triangle, its functoriality for squares commuting up to
homotopy, and the comparison with degreewise split sequences are already
available in Mathlib.  This file exposes those APIs with the source's
terminology and records the remaining theorem interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Homology.Unit03
open HomologicalComplex
open CochainComplex.HomComplex

universe v u

namespace Formalization.Books.Derived.Unit09

/-! ## Complexes, shifts, and canonical cones -/

/-- The source's `Comp(𝒜)`, represented by integer-indexed cochain complexes. -/
abbrev BookComplex (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.Comp C

/-- The source's `K(𝒜)`, represented by the homotopy category of cochain complexes. -/
abbrev BookHomotopyCategory (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.K C

/-- The shift functor on the source's homotopy category. -/
abbrev homotopyShift
    (C : Type u) [Category.{v} C] [AdditiveCategory C] (n : ℤ) :
    BookHomotopyCategory C ⥤ BookHomotopyCategory C :=
  CategoryTheory.shiftFunctor (BookHomotopyCategory C) n

/-- The zero shift is canonically the identity. -/
noncomputable def homotopyShiftZero
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    homotopyShift C 0 ≅ 𝟭 (BookHomotopyCategory C) :=
  CategoryTheory.shiftFunctorZero (BookHomotopyCategory C) ℤ

/-- Two successive shifts identify with the shift by the sum. -/
noncomputable def homotopyShiftAdd
    (C : Type u) [Category.{v} C] [AdditiveCategory C] (n m : ℤ) :
    homotopyShift C n ⋙ homotopyShift C m ≅ homotopyShift C (n + m) :=
  (CategoryTheory.shiftFunctorAdd (BookHomotopyCategory C) n m).symm

/-- The canonical mapping cone of a morphism of cochain complexes. -/
abbrev Cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : BookComplex C :=
  CochainComplex.mappingCone f

/-- The canonical inclusion of the target into a mapping cone. -/
noncomputable def coneInclusion
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : L ⟶ Cone f :=
  CochainComplex.mappingCone.inr f

/-- The canonical third map from a mapping cone to the shifted source. -/
noncomputable def coneProjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Cone f ⟶ (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj K :=
  (CochainComplex.mappingCone.triangle f).mor₃

/-- The canonical cone triangle in complexes. -/
noncomputable def coneTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Triangle (BookComplex C) :=
  CochainComplex.mappingCone.triangle f

/-- The canonical cone triangle in the homotopy category. -/
abbrev coneTriangleh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Triangle (BookHomotopyCategory C) :=
  CochainComplex.mappingCone.triangleh f

@[simp]
theorem coneTriangle_mor₁
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₁ = f := rfl

@[simp]
theorem coneTriangle_mor₂
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₂ = coneInclusion f := rfl

@[simp]
theorem coneTriangle_mor₃
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₃ = coneProjection f := rfl

theorem coneTriangleh_distinguished
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    coneTriangleh f ∈ distTriang (BookHomotopyCategory C) := by
  exact HomotopyCategory.mappingCone_triangleh_distinguished f

/-! ## Functoriality and factorization through cones -/

/-- The cone map associated to a chosen homotopy-commutative square.

The explicit homotopy is an argument, recording the source's warning that
the resulting cone map is not canonical when the square only commutes up to
homotopy.
-/
noncomputable def coneMapOfHomotopy
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) : Cone f₁ ⟶ Cone f₂ :=
  CochainComplex.mappingCone.mapOfHomotopy H

/-- Functoriality of the cone for a square commuting up to homotopy. -/
noncomputable def coneTriangleMapOfHomotopy
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneTriangleh f₁ ⟶ coneTriangleh f₂ :=
  CochainComplex.mappingCone.trianglehMapOfHomotopy H

theorem functorial_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (coneTriangleMapOfHomotopy H).hom₁ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map a ∧
      (coneTriangleMapOfHomotopy H).hom₂ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b ∧
      (coneTriangleMapOfHomotopy H).hom₃ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (coneMapOfHomotopy H) := by
  dsimp [coneTriangleMapOfHomotopy, coneMapOfHomotopy]
  exact And.intro rfl (And.intro rfl rfl)

theorem map_from_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L M : BookComplex C} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    (∃ u : Cone f ⟶ M, coneInclusion f ≫ u = g) ∧
      (∃ u : K ⟶ (coneTriangle g).invRotate.obj₁,
        u ≫ (coneTriangle g).invRotate.mor₁ = f) := by
  refine ⟨?_, ?_⟩
  · let z : Cochain K M (-1) := ((Cochain.equivHomotopy (f ≫ g) 0) H).1
    have hz : δ (-1) 0 z = Cochain.ofHom (f ≫ g) := by
      have hz' := ((Cochain.equivHomotopy (f ≫ g) 0) H).2
      simp only [Cochain.ofHom_zero, add_zero] at hz'
      exact hz'.symm
    refine ⟨CochainComplex.mappingCone.desc f z g hz, ?_⟩
    exact CochainComplex.mappingCone.inr_desc f z g hz
  · let z : Cochain K M (-1) := ((Cochain.equivHomotopy (f ≫ g) 0) H).1
    have hz : δ (-1) 0 (-z) + Cochain.ofHom (f ≫ g) = 0 := by
      have hz' := ((Cochain.equivHomotopy (f ≫ g) 0) H).2
      simp only [Cochain.ofHom_zero, add_zero] at hz'
      rw [δ_neg, hz'.symm]
      abel
    let u : K ⟶ CochainComplex.mappingCocone g :=
      CochainComplex.mappingCocone.lift g f (-z) hz
    refine ⟨u, ?_⟩
    set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
    have hfst : (coneTriangle g).invRotate.mor₁ =
        CochainComplex.mappingCocone.fst g := by
      dsimp [Triangle.invRotate, coneTriangle]
      ext n
      simp [CochainComplex.mappingCocone.fst,
        CochainComplex.mappingCone.triangle,
        Triangle.mk,
        CochainComplex.shiftFunctor_map_f', HomologicalComplex.XIsoOfEq,
        Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
        shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_inv_app_f',
        CochainComplex.shiftFunctorZero_hom_app_f]
      rw [Cochain.leftShift_v _ _ _ _ n n (by simp) (n + -1) (by omega)]
      have hn : n + -1 + 1 = n := by omega
      change ((CochainComplex.mappingCone.fst g :
        Cochain (CochainComplex.mappingCone g) L 1).v
        (n + -1) (n + -1 + 1) _ ≫ (L.XIsoOfEq hn).hom) = _
      rw [Cochain.v_comp_XIsoOfEq_hom]
      simp [HomologicalComplex.XIsoOfEq, sub_eq_add_neg]
    rw [hfst]
    exact CochainComplex.mappingCocone.lift_fst g f (-z) hz

/-! ## Termwise split maps and replacements -/

/-- A map of cochain complexes is termwise split injective. -/
def termwiseSplitInjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, IsSplitMono (f.f n)

/-- A map of cochain complexes is termwise split surjective. -/
def termwiseSplitSurjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, IsSplitEpi (f.f n)

theorem make_commute_map_injection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B C' D : BookComplex C}
    {f : A ⟶ B} {a : A ⟶ C'} {b : B ⟶ D} {g : C' ⟶ D}
    (H : Homotopy (f ≫ b) (a ≫ g))
    (hf : termwiseSplitInjection f) :
    ∃ b' : B ⟶ D, Nonempty (Homotopy b b') ∧ f ≫ b' = a ≫ g := by
  let r : ∀ n : ℤ, B.X n ⟶ A.X n :=
    fun n => (hf n).exists_splitMono.some.retraction
  have hr : ∀ n : ℤ, f.f n ≫ r n = 𝟙 _ := by
    intro n
    exact (hf n).exists_splitMono.some.id
  let h : Cochain A D (-1) :=
    ((Cochain.equivHomotopy (f ≫ b) (a ≫ g)) H).1
  let z : Cochain B D (-1) :=
    (Cochain.ofHoms r).comp h (zero_add (-1))
  have hfr :
      (Cochain.ofHom f).comp (Cochain.ofHoms r) (zero_add 0) =
        Cochain.ofHom (𝟙 A) := by
    ext n
    simp [Cochain.ofHom, Cochain.ofHoms, hr]
  have hzcomp :
      (Cochain.ofHom f).comp z (zero_add (-1)) = h := by
    dsimp [z]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, hfr,
      Cochain.id_comp]
  let q : Cochain B D 0 := Cochain.ofHom b - δ (-1) 0 z
  have hq : δ 0 1 q = 0 := by
    dsimp [q]
    rw [δ_sub, δ_ofHom, δ_δ]
    simp
  let b' : B ⟶ D :=
    Cocycle.homOf (Cocycle.mk q 1 (zero_add 1) hq)
  have hb'co : Cochain.ofHom b' = q := by
    dsimp [b']
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  have hbb' : Nonempty (Homotopy b b') := by
    refine ⟨(Cochain.equivHomotopy b b').symm ⟨z, ?_⟩⟩
    rw [hb'co]
    dsimp [q]
    abel
  have hH : Cochain.ofHom (f ≫ b) =
      δ (-1) 0 h + Cochain.ofHom (a ≫ g) := by
    exact ((Cochain.equivHomotopy (f ≫ b) (a ≫ g)) H).2.trans (by simp [h])
  have hδ :
      (Cochain.ofHom f).comp (δ (-1) 0 z) (zero_add 0) =
        δ (-1) 0 h := by
    rw [← δ_ofHom_comp f z 0, hzcomp]
  have hfb :
      (Cochain.ofHom f).comp (Cochain.ofHom b) (zero_add 0) =
        Cochain.ofHom (f ≫ b) := (Cochain.ofHom_comp f b).symm
  have hcomm : f ≫ b' = a ≫ g := by
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, hb'co]
    dsimp [q]
    rw [Cochain.comp_sub, hfb, hδ, hH]
    abel
  exact ⟨b', hbb', hcomm⟩

theorem make_commute_map_surjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B C' D : BookComplex C}
    {f : A ⟶ B} {a : A ⟶ C'} {b : B ⟶ D} {g : C' ⟶ D}
    (H : Homotopy (f ≫ b) (a ≫ g))
    (hg : termwiseSplitSurjection g) :
    ∃ a' : A ⟶ C', Nonempty (Homotopy a a') ∧ f ≫ b = a' ≫ g := by
  let s : ∀ n : ℤ, D.X n ⟶ C'.X n :=
    fun n => (hg n).exists_splitEpi.some.section_
  have hs : ∀ n : ℤ, s n ≫ g.f n = 𝟙 _ := by
    intro n
    exact (hg n).exists_splitEpi.some.id
  let h : Cochain A D (-1) :=
    ((Cochain.equivHomotopy (f ≫ b) (a ≫ g)) H).1
  let z : Cochain A C' (-1) :=
    h.comp (Cochain.ofHoms s) (add_zero (-1))
  have hsg :
      (Cochain.ofHoms s).comp (Cochain.ofHom g) (zero_add 0) =
        Cochain.ofHom (𝟙 D) := by
    ext n
    simp [Cochain.ofHom, Cochain.ofHoms, hs]
  have hzcomp :
      z.comp (Cochain.ofHom g) (add_zero (-1)) = h := by
    dsimp [z]
    rw [Cochain.comp_assoc_of_second_is_zero_cochain, hsg,
      Cochain.comp_id]
  let q : Cochain A C' 0 := Cochain.ofHom a + δ (-1) 0 z
  have hq : δ 0 1 q = 0 := by
    dsimp [q]
    rw [δ_add, δ_ofHom, δ_δ]
    simp
  let a' : A ⟶ C' :=
    Cocycle.homOf (Cocycle.mk q 1 (zero_add 1) hq)
  have ha'co : Cochain.ofHom a' = q := by
    dsimp [a']
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  have haa' : Nonempty (Homotopy a a') := by
    refine ⟨(Cochain.equivHomotopy a a').symm ⟨-z, ?_⟩⟩
    rw [ha'co]
    dsimp [q]
    rw [δ_neg]
    abel
  have hH : Cochain.ofHom (f ≫ b) =
      δ (-1) 0 h + Cochain.ofHom (a ≫ g) := by
    exact ((Cochain.equivHomotopy (f ≫ b) (a ≫ g)) H).2.trans (by simp [h])
  have hδ :
      (δ (-1) 0 z).comp (Cochain.ofHom g) (add_zero 0) =
        δ (-1) 0 h := by
    rw [← δ_comp_ofHom z g 0, hzcomp]
  have hag :
      (Cochain.ofHom a).comp (Cochain.ofHom g) (zero_add 0) =
        Cochain.ofHom (a ≫ g) := (Cochain.ofHom_comp a g).symm
  have hfb :
      (Cochain.ofHom f).comp (Cochain.ofHom b) (zero_add 0) =
        Cochain.ofHom (f ≫ b) := (Cochain.ofHom_comp f b).symm
  have hcomm : f ≫ b = a' ≫ g := by
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, Cochain.ofHom_comp, ha'co]
    dsimp [q]
    rw [Cochain.add_comp, hag, hδ, hfb, hH]
    abel
  exact ⟨a', haa', hcomm⟩

theorem make_injective
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (α : K ⟶ L) :
    ∃ (L' : BookComplex C) (i : K ⟶ L') (π : L' ⟶ L),
      i ≫ π = α ∧
      termwiseSplitInjection i ∧
      ∃ s : L ⟶ L',
        s ≫ π = 𝟙 L ∧
      Nonempty (Homotopy (π ≫ s) (𝟙 L')) ∧
      ((IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow L') ∧
      ((IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove L') ∧
      ((IsBounded K ∧ IsBounded L) → IsBounded L') := by
  let L' : BookComplex C := CochainComplex.mappingCone (𝟙 K) ⊞ L
  let i : K ⟶ L' :=
    biprod.lift (CochainComplex.mappingCone.inr (𝟙 K)) α
  let π : L' ⟶ L := biprod.snd
  have hiπ : i ≫ π = α := by
    dsimp [i, π, L']
    simp
  have hi : termwiseSplitInjection i := by
    intro n
    change IsSplitMono (i.f n)
    apply IsSplitMono.mk'
    let r : L'.X n ⟶ K.X n :=
      (biprod.fst : L' ⟶ CochainComplex.mappingCone (𝟙 K)).f n ≫
        (CochainComplex.mappingCone.snd (𝟙 K)).v n n (add_zero n)
    refine ⟨r, ?_⟩
    dsimp [r, i, L']
    rw [← Category.assoc, HomologicalComplex.biprod_lift_fst_f]
    simp
  have hsπ : (biprod.inr : L ⟶ L') ≫ π = 𝟙 L := by
    dsimp [π, L']
    simp
  have hπs : Nonempty (Homotopy (π ≫ (biprod.inr : L ⟶ L')) (𝟙 L')) := by
    have hzero : Homotopy
        ((biprod.fst : L' ⟶ CochainComplex.mappingCone (𝟙 K)) ≫
          (biprod.inl : CochainComplex.mappingCone (𝟙 K) ⟶ L')) 0 := by
      simpa using
        ((CochainComplex.mappingCone.homotopyToZeroOfId K).compRight
          (biprod.inl : CochainComplex.mappingCone (𝟙 K) ⟶ L')).compLeft
          (biprod.fst : L' ⟶ CochainComplex.mappingCone (𝟙 K))
    have hsub : Homotopy
        (𝟙 L' - π ≫ (biprod.inr : L ⟶ L')) 0 := by
      apply (Homotopy.ofEq ?_).trans hzero
      dsimp [π, L']
      rw [← biprod.total]
      abel
    exact ⟨((Homotopy.equivSubZero).symm hsub).symm⟩
  have hbelow :
      (IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow L' := by
    rintro ⟨hK, hL⟩
    obtain ⟨nK, hnK⟩ := hK
    obtain ⟨nL, hnL⟩ := hL
    let n := min (nK - 1) nL
    letI : K.IsStrictlyGE nK := hnK
    letI : L.IsStrictlyGE nL := hnL
    have hcone :
        (CochainComplex.mappingCone (𝟙 K)).IsStrictlyGE n := by
      apply CochainComplex.isStrictlyGE_mappingCone (𝟙 K) nK nK n
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff] at hcone ⊢
    intro j hj
    change IsZero ((CochainComplex.mappingCone (𝟙 K) ⊞ L).X j)
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
    simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
    refine ⟨hcone j hj, L.isZero_of_isStrictlyGE nL j (by dsimp [n] at hj ⊢; omega)⟩
  have habove :
      (IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove L' := by
    rintro ⟨hK, hL⟩
    obtain ⟨nK, hnK⟩ := hK
    obtain ⟨nL, hnL⟩ := hL
    let n := max nK nL
    letI : K.IsStrictlyLE nK := hnK
    letI : L.IsStrictlyLE nL := hnL
    have hcone :
        (CochainComplex.mappingCone (𝟙 K)).IsStrictlyLE n := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      simp only [CochainComplex.mappingCone.isZero_X_iff]
      refine ⟨K.isZero_of_isStrictlyLE nK (j + 1) (by dsimp [n] at hj ⊢; omega),
        K.isZero_of_isStrictlyLE nK j (by dsimp [n] at hj ⊢; omega)⟩
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff] at hcone ⊢
    intro j hj
    change IsZero ((CochainComplex.mappingCone (𝟙 K) ⊞ L).X j)
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
    simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
    exact ⟨hcone j hj, L.isZero_of_isStrictlyLE nL j (by dsimp [n] at hj ⊢; omega)⟩
  have hbounded :
      (IsBounded K ∧ IsBounded L) → IsBounded L' := by
    rintro ⟨⟨pK, qK, hpK, hqK⟩, ⟨pL, qL, hpL, hqL⟩⟩
    refine ⟨min (pK - 1) pL, max qK qL, ?_, ?_⟩
    · letI : K.IsStrictlyGE pK := hpK
      letI : L.IsStrictlyGE pL := hpL
      have hcone :
          (CochainComplex.mappingCone (𝟙 K)).IsStrictlyGE (min (pK - 1) pL) := by
        apply CochainComplex.isStrictlyGE_mappingCone (𝟙 K) pK pK _
      rw [CochainComplex.isStrictlyGE_iff] at hcone ⊢
      intro j hj
      change IsZero ((CochainComplex.mappingCone (𝟙 K) ⊞ L).X j)
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
      simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
      exact ⟨hcone j hj, L.isZero_of_isStrictlyGE pL j (by omega)⟩
    · letI : K.IsStrictlyLE qK := hqK
      letI : L.IsStrictlyLE qL := hqL
      have hcone :
          (CochainComplex.mappingCone (𝟙 K)).IsStrictlyLE (max qK qL) := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro j hj
        simp only [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨K.isZero_of_isStrictlyLE qK (j + 1) (by omega),
          K.isZero_of_isStrictlyLE qK j (by omega)⟩
      rw [CochainComplex.isStrictlyLE_iff] at hcone ⊢
      intro j hj
      change IsZero ((CochainComplex.mappingCone (𝟙 K) ⊞ L).X j)
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
      simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
      exact ⟨hcone j hj, L.isZero_of_isStrictlyLE qL j (by omega)⟩
  exact ⟨L', i, π, hiπ, hi, biprod.inr, hsπ, hπs, hbelow, habove, hbounded⟩

theorem make_surjective
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (α : K ⟶ L) :
    ∃ (K' : BookComplex C) (i : K ⟶ K') (π : K' ⟶ L),
      i ≫ π = α ∧
      termwiseSplitSurjection π ∧
      ∃ s : K' ⟶ K,
        i ≫ s = 𝟙 K ∧
      Nonempty (Homotopy (s ≫ i) (𝟙 K')) ∧
      ((IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow K') ∧
      ((IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove K') ∧
      ((IsBounded K ∧ IsBounded L) → IsBounded K') := by
  let K' : BookComplex C := K ⊞ CochainComplex.mappingCocone (𝟙 L)
  let i : K ⟶ K' := biprod.inl
  let π : K' ⟶ L :=
    biprod.desc α (CochainComplex.mappingCocone.fst (𝟙 L))
  have hiπ : i ≫ π = α := by
    dsimp [i, π, K']
    simp
  have hπ : termwiseSplitSurjection π := by
    intro n
    change IsSplitEpi (π.f n)
    apply IsSplitEpi.mk'
    let s : L.X n ⟶ K'.X n :=
      (CochainComplex.mappingCocone.inl (𝟙 L)).v n n (add_zero n) ≫
        (biprod.inr : CochainComplex.mappingCocone (𝟙 L) ⟶ K').f n
    refine ⟨s, ?_⟩
    dsimp [s, π, K']
    rw [Category.assoc, HomologicalComplex.biprod_inr_desc_f]
    simp
  have his : i ≫ (biprod.fst : K' ⟶ K) = 𝟙 K := by
    dsimp [i, K']
    simp
  have hsi : Nonempty (Homotopy ((biprod.fst : K' ⟶ K) ≫ i) (𝟙 K')) := by
    have hMzero : Homotopy
        (𝟙 (CochainComplex.mappingCocone (𝟙 L))) 0 := by
      let h := CochainComplex.mappingCone.homotopyToZeroOfId L
      let hom : ∀ i j, (CochainComplex.mappingCocone (𝟙 L)).X i ⟶
          (CochainComplex.mappingCocone (𝟙 L)).X j := fun i j =>
        -h.hom (i + -1) (j + -1)
      refine { hom := hom, zero := ?_, comm := ?_ }
      · intro i j hij
        dsimp [hom]
        rw [h.zero _ _ (by
          intro hrel
          apply hij
          change j + 1 = i
          change j + -1 + 1 = i + -1 at hrel
          omega)]
        simp only [neg_zero]
        rfl
      · intro i
        rw [dNext_eq hom (i' := i + 1) (by simp),
          prevD_eq hom (j' := i - 1) (by simp)]
        dsimp [hom, CochainComplex.mappingCocone,
          CochainComplex.shiftFunctor_obj_d']
        have hc := h.comm (i + -1)
        rw [dNext_eq h.hom (i' := i) (by simp),
          prevD_eq h.hom (j' := i + -2) (by
            simp only [ComplexShape.up_Rel]
            omega)] at hc
        rw [show i + 1 + -1 = i by omega,
          show i - 1 + -1 = i + -2 by omega]
        convert hc using 1 <;>
          simp [Int.negOnePow_neg, Int.negOnePow_one, Linear.units_smul_comp,
            Linear.comp_units_smul, smul_smul, Int.units_mul_self, add_assoc]
        all_goals
          change
            ((CochainComplex.mappingCone (𝟙 L)).d (i + -1) i ≫ h.hom i (i + -1) +
              h.hom (i + -1) (i + -2) ≫
                (CochainComplex.mappingCone (𝟙 L)).d (i + -2) (i + -1)) + 0 = _
          exact add_zero _
    have hzero : Homotopy
        ((biprod.snd : K' ⟶ CochainComplex.mappingCocone (𝟙 L)) ≫
          (biprod.inr : CochainComplex.mappingCocone (𝟙 L) ⟶ K')) 0 := by
      simpa using (hMzero.compRight
          (biprod.inr : CochainComplex.mappingCocone (𝟙 L) ⟶ K')).compLeft
          (biprod.snd : K' ⟶ CochainComplex.mappingCocone (𝟙 L))
    have hsub : Homotopy
        (𝟙 K' - (biprod.fst : K' ⟶ K) ≫ i) 0 := by
      apply (Homotopy.ofEq ?_).trans hzero
      dsimp [i, K']
      rw [← biprod.total]
      abel
    exact ⟨((Homotopy.equivSubZero).symm hsub).symm⟩
  have hbelow :
      (IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow K' := by
    rintro ⟨hK, hL⟩
    obtain ⟨nK, hnK⟩ := hK
    obtain ⟨nL, hnL⟩ := hL
    let n := min nK nL
    letI : K.IsStrictlyGE nK := hnK
    letI : L.IsStrictlyGE nL := hnL
    have hcone0 :
        (CochainComplex.mappingCone (𝟙 L)).IsStrictlyGE (nL - 1) := by
      apply CochainComplex.isStrictlyGE_mappingCone (𝟙 L) nL nL (nL - 1)
    letI : (CochainComplex.mappingCone (𝟙 L)).IsStrictlyGE (nL - 1) := hcone0
    have hcone' :
        (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyGE nL := by
      dsimp [CochainComplex.mappingCocone]
      apply CochainComplex.isStrictlyGE_shift
        (CochainComplex.mappingCone (𝟙 L)) (nL - 1) (-1) nL
      omega
    have hcone :
        (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyGE n := by
      rw [CochainComplex.isStrictlyGE_iff] at hcone'
      rw [CochainComplex.isStrictlyGE_iff]
      intro j hj
      exact hcone' j (by dsimp [n] at hj ⊢; omega)
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff] at hcone ⊢
    intro j hj
    change IsZero ((K ⊞ CochainComplex.mappingCocone (𝟙 L)).X j)
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
    simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
    exact ⟨K.isZero_of_isStrictlyGE nK j (by dsimp [n] at hj ⊢; omega), hcone j hj⟩
  have habove :
      (IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove K' := by
    rintro ⟨hK, hL⟩
    obtain ⟨nK, hnK⟩ := hK
    obtain ⟨nL, hnL⟩ := hL
    let n := max nK (nL + 1)
    letI : K.IsStrictlyLE nK := hnK
    letI : L.IsStrictlyLE nL := hnL
    have hcone0 :
        (CochainComplex.mappingCone (𝟙 L)).IsStrictlyLE nL := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      simp only [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨L.isZero_of_isStrictlyLE nL (j + 1) (by omega),
        L.isZero_of_isStrictlyLE nL j (by omega)⟩
    letI : (CochainComplex.mappingCone (𝟙 L)).IsStrictlyLE nL := hcone0
    have hcone' :
        (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyLE (nL + 1) := by
      dsimp [CochainComplex.mappingCocone]
      apply CochainComplex.isStrictlyLE_shift
        (CochainComplex.mappingCone (𝟙 L)) nL (-1) (nL + 1)
      omega
    have hcone :
        (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyLE n := by
      rw [CochainComplex.isStrictlyLE_iff] at hcone'
      rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      exact hcone' j (by dsimp [n] at hj ⊢; omega)
    refine ⟨n, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff] at hcone ⊢
    intro j hj
    change IsZero ((K ⊞ CochainComplex.mappingCocone (𝟙 L)).X j)
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
    simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
    exact ⟨K.isZero_of_isStrictlyLE nK j (by dsimp [n] at hj ⊢; omega), hcone j hj⟩
  have hbounded :
      (IsBounded K ∧ IsBounded L) → IsBounded K' := by
    rintro ⟨⟨pK, qK, hpK, hqK⟩, ⟨pL, qL, hpL, hqL⟩⟩
    refine ⟨min pK pL, max qK (qL + 1), ?_, ?_⟩
    · letI : K.IsStrictlyGE pK := hpK
      letI : L.IsStrictlyGE pL := hpL
      have hcone0 :
          (CochainComplex.mappingCone (𝟙 L)).IsStrictlyGE (pL - 1) := by
        apply CochainComplex.isStrictlyGE_mappingCone (𝟙 L) pL pL (pL - 1)
      letI : (CochainComplex.mappingCone (𝟙 L)).IsStrictlyGE (pL - 1) := hcone0
      have hcone' :
          (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyGE pL := by
        dsimp [CochainComplex.mappingCocone]
        apply CochainComplex.isStrictlyGE_shift
          (CochainComplex.mappingCone (𝟙 L)) (pL - 1) (-1) pL
        omega
      have hcone :
          (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyGE (min pK pL) := by
        rw [CochainComplex.isStrictlyGE_iff] at hcone'
        rw [CochainComplex.isStrictlyGE_iff]
        intro j hj
        exact hcone' j (by omega)
      rw [CochainComplex.isStrictlyGE_iff] at hcone ⊢
      intro j hj
      change IsZero ((K ⊞ CochainComplex.mappingCocone (𝟙 L)).X j)
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
      simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
      exact ⟨K.isZero_of_isStrictlyGE pK j (by omega), hcone j hj⟩
    · letI : K.IsStrictlyLE qK := hqK
      letI : L.IsStrictlyLE qL := hqL
      have hcone0 :
          (CochainComplex.mappingCone (𝟙 L)).IsStrictlyLE qL := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro j hj
        simp only [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨L.isZero_of_isStrictlyLE qL (j + 1) (by omega),
          L.isZero_of_isStrictlyLE qL j (by omega)⟩
      letI : (CochainComplex.mappingCone (𝟙 L)).IsStrictlyLE qL := hcone0
      have hcone' :
          (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyLE (qL + 1) := by
        dsimp [CochainComplex.mappingCocone]
        apply CochainComplex.isStrictlyLE_shift
          (CochainComplex.mappingCone (𝟙 L)) qL (-1) (qL + 1)
        omega
      have hcone :
          (CochainComplex.mappingCocone (𝟙 L)).IsStrictlyLE (max qK (qL + 1)) := by
        rw [CochainComplex.isStrictlyLE_iff] at hcone'
        rw [CochainComplex.isStrictlyLE_iff]
        intro j hj
        exact hcone' j (by omega)
      rw [CochainComplex.isStrictlyLE_iff] at hcone ⊢
      intro j hj
      change IsZero ((K ⊞ CochainComplex.mappingCocone (𝟙 L)).X j)
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapBiprod _ _)
      simp only [HomologicalComplex.eval_obj, biprod_isZero_iff]
      exact ⟨K.isZero_of_isStrictlyLE qK j (by omega), hcone j hj⟩
  exact ⟨K', i, π, hiπ, hπ, (biprod.fst : K' ⟶ K), his, hsi, hbelow, habove, hbounded⟩

/-! ## Termwise split exact sequences and their triangles -/

/-- A termwise split exact sequence, expressed by degreewise Mathlib splittings.

The splittings are the categorical form of the source's specified direct-sum
decompositions `Bⁿ = Aⁿ ⊕ Cⁿ`, with `r` the projection to `Aⁿ` and `s` the
section from `Cⁿ`.
-/
structure TermwiseSplitExactSequence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (A B D : BookComplex C) where
  f : A ⟶ B
  g : B ⟶ D
  zero : f ≫ g = 0
  splitting : ∀ n : ℤ,
    ((ShortComplex.mk f g zero).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting

def termwiseSplitShortComplex
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    ShortComplex (BookComplex C) :=
  ShortComplex.mk S.f S.g S.zero

def termwiseSplitSection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    D.X n ⟶ B.X n :=
  (S.splitting n).s

def termwiseSplitProjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    B.X n ⟶ A.X n :=
  (S.splitting n).r

def termwiseSplitConnectingFamily
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    D.X n ⟶ A.X (n + 1) :=
  termwiseSplitSection S n ≫ B.d n (n + 1) ≫ termwiseSplitProjection S (n + 1)

noncomputable def termwiseSplitConnectingMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    D ⟶ (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj A :=
  CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) S.splitting

theorem termwiseSplitConnectingMap_f
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    (termwiseSplitConnectingMap S).f n = termwiseSplitConnectingFamily S n := by
  change (CochainComplex.homOfDegreewiseSplit (ShortComplex.mk S.f S.g S.zero) S.splitting).f n = _
  rw [CochainComplex.homOfDegreewiseSplit_f]
  rfl

noncomputable def termwiseSplitTriangleWith
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Triangle (BookComplex C) :=
  CochainComplex.triangleOfDegreewiseSplit (termwiseSplitShortComplex S) σ

abbrev termwiseSplitTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookComplex C) :=
  termwiseSplitTriangleWith S S.splitting

abbrev termwiseSplitTrianglehWith
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Triangle (BookHomotopyCategory C) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (termwiseSplitTriangleWith S σ)

abbrev termwiseSplitTriangleh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookHomotopyCategory C) :=
  termwiseSplitTrianglehWith S S.splitting

theorem triangle_independent_splittings
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ σ' : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
      Nonempty (Homotopy
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ)
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ')) ∧
      ∃ e : termwiseSplitTrianglehWith S σ ≅ termwiseSplitTrianglehWith S σ',
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ := by
  have hh : Homotopy
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ)
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ') := by
    let rσ : ∀ i : ℤ, (termwiseSplitShortComplex S).X₂.X i ⟶
        (termwiseSplitShortComplex S).X₁.X i := fun i => by
      exact (σ i).r
    let sσ : ∀ i : ℤ, (termwiseSplitShortComplex S).X₃.X i ⟶
        (termwiseSplitShortComplex S).X₂.X i := fun i => by
      exact (σ i).s
    let rσ' : ∀ i : ℤ, (termwiseSplitShortComplex S).X₂.X i ⟶
        (termwiseSplitShortComplex S).X₁.X i := fun i => by
      exact (σ' i).r
    let sσ' : ∀ i : ℤ, (termwiseSplitShortComplex S).X₃.X i ⟶
        (termwiseSplitShortComplex S).X₂.X i := fun i => by
      exact (σ' i).s
    let k : ∀ i : ℤ, (termwiseSplitShortComplex S).X₃.X i ⟶
        (termwiseSplitShortComplex S).X₁.X i := fun i =>
      sσ' i ≫ rσ i - sσ i ≫ rσ' i
    let dB : ∀ p : ℤ,
        (termwiseSplitShortComplex S).X₂.X p ⟶
          (termwiseSplitShortComplex S).X₂.X (p + 1) := fun p =>
      (termwiseSplitShortComplex S).X₂.d p (p + 1)
    let hom : ∀ i j, (termwiseSplitShortComplex S).X₃.X i ⟶
        ((CochainComplex.shiftFunctor C (1 : ℤ)).obj
          (termwiseSplitShortComplex S).X₁).X j :=
      fun i j => if hij : i + (-1 : ℤ) = j then
        k i ≫
          ((termwiseSplitShortComplex S).X₁.XIsoOfEq (by omega : i = j + 1)).hom ≫
            (CochainComplex.shiftFunctorObjXIso
              (termwiseSplitShortComplex S).X₁ (1 : ℤ) j (j + 1) rfl).inv
      else 0
    refine { hom := hom, zero := ?_, comm := ?_ }
    · intro i j hij
      dsimp only [hom]
      split
      · rename_i h
        exfalso
        apply hij
        change j + 1 = i
        have h' := congrArg (fun x : ℤ => x + 1) h
        omega
      · change (0 : (termwiseSplitShortComplex S).X₃.X i ⟶
          ((CochainComplex.shiftFunctor C (1 : ℤ)).obj
            (termwiseSplitShortComplex S).X₁).X j) = 0
        rfl
    · intro p
      rw [dNext_eq hom (i' := p + 1) (by simp),
        prevD_eq hom (j' := p - 1) (by simp)]
      dsimp only [hom]
      have hp : p + 1 + (-1 : ℤ) = p := by omega
      have hm : p + (-1 : ℤ) = p - 1 := by omega
      simp only [dif_pos hp, dif_pos hm]
      have hcσ :
          (CochainComplex.cocycleOfDegreewiseSplit
            (termwiseSplitShortComplex S) σ).1.v p (p + 1) (by omega) =
            (sσ p ≫ dB p ≫ rσ (p + 1)) ≫
              (CochainComplex.shiftFunctorObjXIso
                (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).inv := by
        dsimp [CochainComplex.cocycleOfDegreewiseSplit]
        simp only [Cocycle.mk_coe, Cochain.mk_v, Category.comp_id]
        apply (cancel_mono (CochainComplex.shiftFunctorObjXIso
          (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom).1
        change (sσ p ≫ dB p ≫ rσ (p + 1)) ≫
            (CochainComplex.shiftFunctorObjXIso
              (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom =
          (((sσ p ≫ dB p ≫ rσ (p + 1)) ≫
            𝟙 ((termwiseSplitShortComplex S).X₁.X (p + 1))) ≫
              (CochainComplex.shiftFunctorObjXIso
                (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom)
        rw [Category.comp_id]
      have hcσ' :
          (CochainComplex.cocycleOfDegreewiseSplit
            (termwiseSplitShortComplex S) σ').1.v p (p + 1) (by omega) =
            (sσ' p ≫ dB p ≫ rσ' (p + 1)) ≫
              (CochainComplex.shiftFunctorObjXIso
                (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).inv := by
        dsimp [CochainComplex.cocycleOfDegreewiseSplit]
        simp only [Cocycle.mk_coe, Cochain.mk_v, Category.comp_id]
        apply (cancel_mono (CochainComplex.shiftFunctorObjXIso
          (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom).1
        change (sσ' p ≫ dB p ≫ rσ' (p + 1)) ≫
            (CochainComplex.shiftFunctorObjXIso
              (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom =
          (((sσ' p ≫ dB p ≫ rσ' (p + 1)) ≫
            𝟙 ((termwiseSplitShortComplex S).X₁.X (p + 1))) ≫
              (CochainComplex.shiftFunctorObjXIso
                (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom)
        rw [Category.comp_id]
      have hd :
          (CochainComplex.shiftFunctorObjXIso
              (termwiseSplitShortComplex S).X₁ (1 : ℤ) (p - 1) (p - 1 + 1) (by omega)).inv ≫
            ((CochainComplex.shiftFunctor C (1 : ℤ)).obj
              (termwiseSplitShortComplex S).X₁).d (p - 1) p ≫
              (CochainComplex.shiftFunctorObjXIso
                (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) (by omega)).hom =
            (-1 : ℤ) • (termwiseSplitShortComplex S).X₁.d (p - 1 + 1) (p + 1) := by
        dsimp [CochainComplex.shiftFunctorObjXIso, CochainComplex.shiftFunctor]
        simp
      rw [CochainComplex.homOfDegreewiseSplit_f,
        CochainComplex.homOfDegreewiseSplit_f]
      rw [hcσ, hcσ']
      rw [← cancel_mono (CochainComplex.shiftFunctorObjXIso
        (termwiseSplitShortComplex S).X₁ (1 : ℤ) p (p + 1) rfl).hom]
      simp only [Preadditive.add_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
      rw [hd]
      have hfrσ (i : ℤ) : S.f.f i ≫ rσ i = 𝟙 _ := by
        exact (σ i).f_r
      have hsgσ (i : ℤ) : sσ i ≫ S.g.f i = 𝟙 _ := by
        exact (σ i).s_g
      have hrfσ (i : ℤ) : rσ i ≫ S.f.f i =
          𝟙 _ - S.g.f i ≫ sσ i := by
        exact (σ i).r_f
      have hgsσ (i : ℤ) : S.g.f i ≫ sσ i =
          𝟙 _ - rσ i ≫ S.f.f i := by
        exact (σ i).g_s
      have hfrσ' (i : ℤ) : S.f.f i ≫ rσ' i = 𝟙 _ := by
        exact (σ' i).f_r
      have hsgσ' (i : ℤ) : sσ' i ≫ S.g.f i = 𝟙 _ := by
        exact (σ' i).s_g
      have hrfσ' (i : ℤ) : rσ' i ≫ S.f.f i =
          𝟙 _ - S.g.f i ≫ sσ' i := by
        exact (σ' i).r_f
      have hgsσ' (i : ℤ) : S.g.f i ≫ sσ' i =
          𝟙 _ - rσ' i ≫ S.f.f i := by
        exact (σ' i).g_s
      have hshift :
          ((termwiseSplitShortComplex S).X₁.XIsoOfEq
              (by omega : p = p - 1 + 1)).hom ≫
            ((-1 : ℤ) • (termwiseSplitShortComplex S).X₁.d (p - 1 + 1) (p + 1)) =
          (-1 : ℤ) • (termwiseSplitShortComplex S).X₁.d p (p + 1) := by
        rw [Preadditive.comp_zsmul]
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d
          (termwiseSplitShortComplex S).X₁
          (by omega : p = p - 1 + 1) (p + 1)]
      let fS : ∀ i : ℤ, (termwiseSplitShortComplex S).X₁.X i ⟶
          (termwiseSplitShortComplex S).X₂.X i := fun i => by
        exact S.f.f i
      let gS : ∀ i : ℤ, (termwiseSplitShortComplex S).X₂.X i ⟶
          (termwiseSplitShortComplex S).X₃.X i := fun i => by
        exact S.g.f i
      have hgS (i j : ℤ) : gS i ≫
          (termwiseSplitShortComplex S).X₃.d i j =
            (termwiseSplitShortComplex S).X₂.d i j ≫ gS j := by
        exact S.g.comm i j
      have hsgσ'B (i : ℤ) : sσ' i ≫ gS i = 𝟙 _ := by
        exact (σ' i).s_g
      have hgsσ'B (i : ℤ) : gS i ≫ sσ' i =
          𝟙 _ - rσ' i ≫ fS i := by
        exact (σ' i).g_s
      have hfrσ'B (i : ℤ) : fS i ≫ rσ' i = 𝟙 _ := by
        exact (σ' i).f_r
      have hD :
          (termwiseSplitShortComplex S).X₃.d p (p + 1) ≫
              sσ' (p + 1) ≫ rσ (p + 1) =
            sσ' p ≫ dB p ≫ rσ (p + 1) -
              sσ' p ≫ dB p ≫ rσ' (p + 1) := by
        calc
          (termwiseSplitShortComplex S).X₃.d p (p + 1) ≫
                sσ' (p + 1) ≫ rσ (p + 1) =
              (sσ' p ≫ gS p) ≫
                (termwiseSplitShortComplex S).X₃.d p (p + 1) ≫
                  sσ' (p + 1) ≫ rσ (p + 1) := by
                    rw [hsgσ'B p]
                    simp
          _ = sσ' p ≫ dB p ≫ gS (p + 1) ≫
                sσ' (p + 1) ≫ rσ (p + 1) := by
                  simpa only [dB, Category.assoc] using
                    congrArg (fun z => sσ' p ≫ z ≫ sσ' (p + 1) ≫ rσ (p + 1))
                      (hgS p (p + 1))
          _ = sσ' p ≫ dB p ≫
                (𝟙 _ - rσ' (p + 1) ≫ fS (p + 1)) ≫
                  rσ (p + 1) := by
                  simpa only [Category.assoc] using
                    congrArg (fun z => sσ' p ≫ dB p ≫ z ≫ rσ (p + 1))
                      (hgsσ'B (p + 1))
          _ = sσ' p ≫ dB p ≫ rσ (p + 1) -
                sσ' p ≫ dB p ≫ rσ' (p + 1) := by
                  sorry
      sorry
  refine ⟨⟨hh⟩, ?_⟩
  let q : BookComplex C ⥤ BookHomotopyCategory C :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let hσ : D ⟶
      (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj
        A := by
    change (termwiseSplitShortComplex S).X₃ ⟶
      (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj
        A
    exact CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ
  let hσ' : D ⟶
      (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj
        A := by
    change (termwiseSplitShortComplex S).X₃ ⟶
      (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj
        A
    exact CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ'
  have hq : q.map hσ = q.map hσ' :=
    HomotopyCategory.eq_of_homotopy _ _ hh
  let Tσ : Triangle (BookHomotopyCategory C) :=
    Triangle.mk (q.map S.f) (q.map S.g)
      (q.map hσ ≫ (q.commShiftIso (1 : ℤ)).hom.app A)
  let Tσ' : Triangle (BookHomotopyCategory C) :=
    Triangle.mk (q.map S.f) (q.map S.g)
      (q.map hσ' ≫ (q.commShiftIso (1 : ℤ)).hom.app A)
  let e₀ : Tσ ≅ Tσ' :=
    Triangle.isoMk _ _
      (Iso.refl (q.obj A))
      (Iso.refl (q.obj B))
      (Iso.refl (q.obj D))
      (by
        dsimp [Tσ, Tσ']
        change q.map S.f ≫ 𝟙 (q.obj B) = 𝟙 (q.obj A) ≫ q.map S.f
        simp only [Category.comp_id, Category.id_comp])
      (by
        dsimp [Tσ, Tσ']
        change q.map S.g ≫ 𝟙 (q.obj D) = 𝟙 (q.obj B) ≫ q.map S.g
        simp only [Category.comp_id, Category.id_comp])
      (by
        dsimp [Tσ, Tσ']
        change (q.map hσ ≫ (q.commShiftIso (1 : ℤ)).hom.app A) ≫
            (shiftFunctor (BookHomotopyCategory C) 1).map (𝟙 (q.obj A)) =
          𝟙 (q.obj D) ≫
            (q.map hσ' ≫ (q.commShiftIso (1 : ℤ)).hom.app A)
        simpa using congrArg (fun x => x ≫
          (q.commShiftIso (1 : ℤ)).hom.app
            A) hq)
  have he₀ : e₀.hom.hom₁ = 𝟙 (q.obj A) ∧
      e₀.hom.hom₂ = 𝟙 (q.obj B) ∧
      e₀.hom.hom₃ = 𝟙 (q.obj D) := by
    simp [e₀, Triangle.isoMk, Triangle.homMk, eqToIso,
      CategoryTheory.eqToHom_refl]
    constructor
    · rfl
    constructor <;> rfl
  simpa only [termwiseSplitTrianglehWith, termwiseSplitTriangleWith,
    termwiseSplitShortComplex, Functor.mapTriangle_obj,
    CochainComplex.triangleOfDegreewiseSplit,
    Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
    Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
    Tσ, Tσ'] using!
    (show ∃ e : Tσ ≅ Tσ', e.hom.hom₁ = 𝟙 _ ∧
      e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ from ⟨e₀, he₀⟩)

/-! ## Consequences in the homotopy category -/

theorem nilpotent
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A₁ B₁ D₁ A₂ B₂ D₂ A₃ B₃ D₃ : BookComplex C}
    (S₁ : TermwiseSplitExactSequence A₁ B₁ D₁)
    (S₂ : TermwiseSplitExactSequence A₂ B₂ D₂)
    (S₃ : TermwiseSplitExactSequence A₃ B₃ D₃)
    (b : B₁ ⟶ B₂) (b' : B₂ ⟶ B₃)
    (h₁ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₁.f ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b = 0)
    (h₂ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₂.g = 0)
    (h₃ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₂.f ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b' = 0)
    (h₄ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b' ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₃.g = 0) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (b ≫ b') = 0 := by
  sorry

theorem third_isomorphism
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (t : coneTriangleh f₁ ⟶ coneTriangleh f₂)
    [IsIso t.hom₁] [IsIso t.hom₂] : IsIso t.hom₃ := by
  sorry

theorem triangle_morphism_isomorphism_of_first_two
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (t : coneTriangleh f₁ ⟶ coneTriangleh f₂)
    [IsIso t.hom₁] [IsIso t.hom₂] : IsIso t := by
  apply Triangle.isIso_of_isIsos t
  · infer_instance
  · infer_instance
  · exact third_isomorphism t

/-! ## Cones and termwise split sequences agree up to isomorphism -/

theorem same_up_to_isomorphisms_of_termwise_split
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    ∃ e : coneTriangleh S.f ≅ termwiseSplitTriangleh S,
      e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ := by
  sorry

theorem same_up_to_isomorphisms_of_map
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    ∃ (M N : BookComplex C) (S : TermwiseSplitExactSequence K M N),
      ∃ e : termwiseSplitTriangleh S ≅ coneTriangleh f,
        e.hom.hom₁ = 𝟙 _ := by
  sorry

/-! ## Simultaneous termwise split replacements -/

/- The parameter of `ComposableArrows` counts arrows, whereas the source's
   sequence lemma counts its objects. -/
def adjacentMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {n : ℕ} (F : ComposableArrows (BookComplex C) n) (i : Fin n) :
    F.obj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟶
      F.obj ⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩ :=
  F.map (homOfLE (show
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) ≤
      ⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩ by simp))

theorem sequence_maps_split
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {n : ℕ} (hn : 0 < n) (A : ComposableArrows (BookComplex C) (n - 1)) :
    ∃ (B : ComposableArrows (BookComplex C) (n - 1)) (φ : B ⟶ A),
      (∀ i : Fin (n - 1), termwiseSplitInjection (adjacentMap B i)) ∧
      (∀ i : Fin ((n - 1) + 1),
        HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) (φ.app i)) ∧
      ((∀ i : Fin ((n - 1) + 1), IsBoundedBelow (A.obj i)) →
        ∀ i : Fin ((n - 1) + 1), IsBoundedBelow (B.obj i)) ∧
      ((∀ i : Fin ((n - 1) + 1), IsBoundedAbove (A.obj i)) →
        ∀ i : Fin ((n - 1) + 1), IsBoundedAbove (B.obj i)) ∧
      ((∀ i : Fin ((n - 1) + 1), IsBounded (A.obj i)) →
        ∀ i : Fin ((n - 1) + 1), IsBounded (B.obj i)) := by
  sorry

/-! ## Rotation -/

/-- The canonical inverse rotation of the associated termwise split triangle. -/
noncomputable def termwiseSplitInverseRotate
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookComplex C) :=
  (termwiseSplitTriangle S).invRotate

abbrev termwiseSplitInverseRotateh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookHomotopyCategory C) :=
  ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (termwiseSplitInverseRotate S))

theorem rotate_triangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Nonempty (termwiseSplitInverseRotateh S ≅
      coneTriangleh (termwiseSplitInverseRotate S).mor₁) := by
  sorry

noncomputable def coneTermwiseSplitSequence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    TermwiseSplitExactSequence
      (CochainComplex.mappingCone.triangle f).rotate.obj₁
      (CochainComplex.mappingCone.triangle f).rotate.obj₂
      (CochainComplex.mappingCone.triangle f).rotate.obj₃ where
  f := (CochainComplex.mappingCone.triangle f).rotate.mor₁
  g := (CochainComplex.mappingCone.triangle f).rotate.mor₂
  zero := by
    change CochainComplex.mappingCone.inr f ≫
      (CochainComplex.mappingCone.triangle f).mor₃ = 0
    exact CochainComplex.mappingCone.inr_triangleδ f
  splitting := fun n => by
    simpa [termwiseSplitShortComplex,
      CochainComplex.mappingCone.triangleRotateShortComplex] using
      (CochainComplex.mappingCone.triangleRotateShortComplexSplitting f n)

theorem rotate_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Nonempty (termwiseSplitTriangleh (coneTermwiseSplitSequence f) ≅
      (coneTriangleh f).rotate) := by
  sorry

end Formalization.Books.Derived.Unit09
