import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Formalization.Books.Homology.Unit13.Complexes
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Homological Algebra, Chapter 31: Inverse systems

The source indexes inverse systems by the positive natural numbers.  They are
represented by the canonical functor category `InverseSystem ℕ+ C`; its
transition maps, limits, pointwise exactness, and essentially constant systems
are all expressed through the existing categorical APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit21
open Formalization.Books.Categories.Unit22
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit13
open scoped ZeroObject

universe u v w

namespace Formalization.Books.Homology.Unit31

/-! ## Inverse systems over the positive integers -/

/- The positive integers are the source's indexing set
`\mathbf{N} = \{1,2,3,\ldots\}`. -/
abbrev NatInverseSystem (C : Type u) [Category.{v} C] :=
  InverseSystem ℕ+ C

/- A map from the `i`-th stage to the `j`-th stage for `j ≤ i`. -/
def transitionMap {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) {i j : ℕ+} (h : j ≤ i) :
    F.obj (Opposite.op i) ⟶ F.obj (Opposite.op j) :=
  F.map (opHomOfLE h)

@[simp] theorem transitionMap_refl {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (i : ℕ+) :
    transitionMap F (i := i) (j := i) le_rfl = 𝟙 (F.obj (Opposite.op i)) := by
  simp [transitionMap, opHomOfLE]

/- Functoriality is the source's identity and composition condition for the
transition maps. -/
theorem transitionMap_comp {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C)
    {i j k : ℕ+} (hij : j ≤ i) (hjk : k ≤ j) :
    transitionMap F (i := i) (j := j) hij ≫
        transitionMap F (i := j) (j := k) hjk =
      transitionMap F (i := i) (j := k) (hjk.trans hij) := by
  change F.map (homOfLE hij).op ≫ F.map (homOfLE hjk).op =
    F.map (homOfLE (hjk.trans hij)).op
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/- The displayed adjacent transition map `φᵢ` is a special case of the
canonical map above. -/
def successiveTransitionMap {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (i : ℕ+) :
    F.obj (Opposite.op (i + 1)) ⟶ F.obj (Opposite.op i) :=
  transitionMap F (i := i + 1) (j := i) (PNat.lt_add_right i 1).le

/- Morphisms of inverse systems are natural transformations, and the category
instance is the canonical functor-category instance. -/
abbrev inverseSystemEvaluation {C : Type u} [Category.{v} C] (i : ℕ+ᵒᵖ) :
    NatInverseSystem C ⥤ C :=
  (evaluation (ℕ+ᵒᵖ) C).obj i

/- The source's additive-category structure is the established project
interface, while the underlying preadditive and finite-product structures are
inherited componentwise from the functor category. -/
@[instance_reducible] def inverseSystemAdditiveCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    AdditiveCategory (NatInverseSystem C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

instance inverseSystem_additiveCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    AdditiveCategory (NatInverseSystem C) :=
  inverseSystemAdditiveCategory C

/- Mathlib's functor-category construction supplies the abelian structure. -/
instance inverseSystem_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (NatInverseSystem C) := by
  infer_instance

/- The source's assertion that exactness is pointwise is recorded with the
canonical evaluation functors. -/
theorem inverseSystem_exact_iff_pointwise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (NatInverseSystem C)) :
    S.Exact ↔
      ∀ i : ℕ+ᵒᵖ,
        (((evaluation (ℕ+ᵒᵖ) C).obj i).mapShortComplex.obj S).Exact := by
  let hF : JointlyFaithful (fun i : ℕ+ᵒᵖ => (evaluation (ℕ+ᵒᵖ) C).obj i) :=
    { map_injective := by
        intro X Y f g h
        apply NatTrans.ext
        funext i
        exact h i }
  simpa only [Functor.mapShortComplex_obj] using
    (hF.jointlyReflectsIsomorphisms.exact_iff S)

/-! ## Limits and compatible families -/

/- This is the source's `limᵢ Mᵢ`; the construction is the canonical limit
of the inverse-system diagram. -/
abbrev inverseSystemLimit {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (F : InverseSystem I C) [HasLimit F] : C :=
  InverseSystemLimit F

noncomputable def inverseSystemLimitIsLimit
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) [HasLimit F] : IsLimit (limit.cone F) :=
  limit.isLimit F

/- In `Type`, a limit is canonically equivalent to the set of compatible
families, and the following unfolds the compatibility condition used in the
source's product description. -/
abbrev inverseLimitFamilies
    (F : NatInverseSystem (Type u)) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  F.sections

theorem inverseLimitFamilies_iff
    (F : NatInverseSystem (Type u))
    (x : ∀ i : ℕ+ᵒᵖ, F.obj i) :
    x ∈ inverseLimitFamilies F ↔
      ∀ {i j : ℕ+ᵒᵖ} (f : i ⟶ j), F.map f (x i) = x j := by
  rfl

/- The same compatible-family description for inverse systems of abelian
groups is obtained after applying the canonical forgetful functor. -/
abbrev additiveGroupInverseLimitFamilies
    (F : NatInverseSystem AddCommGrpCat) :
    Set (∀ i : ℕ+ᵒᵖ, (F.obj i : Type)) :=
  (F ⋙ CategoryTheory.forget AddCommGrpCat).sections

theorem additiveGroupInverseLimitFamilies_iff
    (F : NatInverseSystem AddCommGrpCat)
    (x : ∀ i : ℕ+ᵒᵖ, (F.obj i : Type)) :
    x ∈ additiveGroupInverseLimitFamilies F ↔
      ∀ {i j : ℕ+ᵒᵖ} (f : i ⟶ j),
        (F.map f).hom (x i) = x j := by
  rfl

noncomputable def inverseSystemTypeLimitEquivSections
    (F : NatInverseSystem (Type u)) :
    (inverseSystemLimit F : Type u) ≃ inverseLimitFamilies F :=
  Types.limitEquivSections F

/-! ## The Mittag--Leffler condition -/

/- In an arbitrary abelian category, the image of a transition map is a
subobject of the target.  This is the categorical form of the source's
stabilization condition. -/
def IsMittagLeffler
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C) : Prop :=
  ∀ i : ℕ+, ∃ c : ℕ+, ∃ h : i ≤ c,
    ∀ k : ℕ+, ∀ h' : c ≤ k,
      imageSubobject (F.map (opHomOfLE h)) =
        imageSubobject (F.map (opHomOfLE (h.trans h')))

private def addCommGrpExplicitImage
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) : AddCommGrpCat :=
  AddCommGrpCat.of f.hom.range

private def addCommGrpExplicitImageι
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    addCommGrpExplicitImage f ⟶ H :=
  AddCommGrpCat.ofHom f.hom.range.subtype

private instance addCommGrpExplicitImageι_mono
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    Mono (addCommGrpExplicitImageι f) :=
  ConcreteCategory.mono_of_injective _ (by
    intro x y h
    exact Subtype.ext h)

private def addCommGrpExplicitFactorThruImage
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    G ⟶ addCommGrpExplicitImage f :=
  AddCommGrpCat.ofHom f.hom.rangeRestrict

private def addCommGrpExplicitImageFactorisation
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    MonoFactorisation f where
  I := addCommGrpExplicitImage f
  m := addCommGrpExplicitImageι f
  e := addCommGrpExplicitFactorThruImage f

private noncomputable def addCommGrpExplicitImageIsImage
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    IsImage (addCommGrpExplicitImageFactorisation f) where
  lift F' := AddCommGrpCat.ofHom
    { toFun := fun x =>
        F'.e.hom (Classical.indefiniteDescription (fun y => f.hom y = x)
          (AddMonoidHom.mem_range.mp x.property))
      map_zero' := by
        have hfac (z : G) : F'.m.hom (F'.e.hom z) = f.hom z := by
          exact congrArg (fun q : G ⟶ H => q.hom z) F'.fac
        apply ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
        change F'.m.hom (F'.e.hom _) = F'.m.hom 0
        rw [hfac, map_zero]
        exact (Classical.indefiniteDescription (fun y => f.hom y = 0) _).2
      map_add' := by
        intro x y
        have hfac (z : G) : F'.m.hom (F'.e.hom z) = f.hom z := by
          exact congrArg (fun q : G ⟶ H => q.hom z) F'.fac
        apply ConcreteCategory.injective_of_mono_of_preservesPullback F'.m
        change F'.m.hom (F'.e.hom _) =
          F'.m.hom (F'.e.hom _ + F'.e.hom _)
        rw [map_add, hfac, hfac, hfac]
        rw [(Classical.indefiniteDescription (fun z : G =>
          f.hom z = ((x + y : f.hom.range) : H))
          (AddMonoidHom.mem_range.mp (x + y).property)).2]
        rw [(Classical.indefiniteDescription (fun z : G =>
          f.hom z = (x : H))
          (AddMonoidHom.mem_range.mp x.property)).2]
        rw [(Classical.indefiniteDescription (fun z : G =>
          f.hom z = (y : H))
          (AddMonoidHom.mem_range.mp y.property)).2]
        rfl }
  lift_fac F' := by
    dsimp [addCommGrpExplicitImageFactorisation, addCommGrpExplicitImageι,
      addCommGrpExplicitImage]
    ext x
    have hfac (z : G) : F'.m.hom (F'.e.hom z) = f.hom z := by
      exact congrArg (fun q : G ⟶ H => q.hom z) F'.fac
    let x' : f.hom.range := x
    change F'.m.hom (F'.e.hom
      (Classical.indefiniteDescription (fun y : G => f.hom y = (x' : H))
        (AddMonoidHom.mem_range.mp x'.property))) = (x' : H)
    rw [hfac]
    exact (Classical.indefiniteDescription (fun y : G => f.hom y = (x' : H))
      (AddMonoidHom.mem_range.mp x'.property)).2

private noncomputable def addCommGrpImageIsoRange
    {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
  image f ≅ addCommGrpExplicitImage f :=
  by
    change (Image.monoFactorisation f).I ≅ addCommGrpExplicitImage f
    exact IsImage.isoExt (Image.isImage f) (addCommGrpExplicitImageIsImage f)

private theorem addCommGrp_imageSubobject_eq_iff_range_eq
    {G₁ G₂ H : AddCommGrpCat.{u}} (f : G₁ ⟶ H) (g : G₂ ⟶ H) :
    imageSubobject f = imageSubobject g ↔ f.hom.range = g.hom.range := by
  constructor
  · intro h
    let e : addCommGrpExplicitImage f ≅ addCommGrpExplicitImage g :=
      (addCommGrpImageIsoRange f).symm ≪≫
        (Subobject.isoOfMkEqMk (image.ι f) (image.ι g) h) ≪≫
          addCommGrpImageIsoRange g
    have he : e.hom ≫ addCommGrpExplicitImageι g =
        addCommGrpExplicitImageι f := by
      have hf : (addCommGrpImageIsoRange f).inv ≫ image.ι f =
          addCommGrpExplicitImageι f :=
        by
          simpa [addCommGrpImageIsoRange, addCommGrpExplicitImageFactorisation,
            addCommGrpExplicitImage] using
            (IsImage.isoExt_inv_m (Image.isImage f)
              (addCommGrpExplicitImageIsImage f))
      have hg : (addCommGrpImageIsoRange g).hom ≫
          addCommGrpExplicitImageι g = image.ι g :=
        by
          simpa [addCommGrpImageIsoRange, addCommGrpExplicitImageFactorisation,
            addCommGrpExplicitImage] using
            (IsImage.isoExt_hom_m (Image.isImage g)
              (addCommGrpExplicitImageIsImage g))
      have hm : (Subobject.isoOfMkEqMk (image.ι f) (image.ι g) h).hom ≫
          image.ι g = image.ι f := by
        simp
      dsimp [e]
      simp only [Category.assoc]
      rw [hg, hm, hf]
    apply SetLike.ext
    intro x
    constructor
    · intro hx
      let x' : AddCommGrpCat.of f.hom.range := ⟨x, hx⟩
      have hx' := congrArg (fun q => q x') he
      change (e.hom x').1 = x at hx'
      rw [← hx']
      exact (e.hom x').property
    · intro hx
      let x' : AddCommGrpCat.of g.hom.range := ⟨x, hx⟩
      have he' : e.inv ≫ addCommGrpExplicitImageι f =
          addCommGrpExplicitImageι g := by
        rw [← he]
        simp
      have hx' := congrArg (fun q => q x') he'
      change (e.inv x').1 = x at hx'
      rw [← hx']
      exact (e.inv x').property
  · intro h
    let e : f.hom.range ≃+ g.hom.range :=
      { toFun := fun x => ⟨x, by rw [← h]; exact x.property⟩
        invFun := fun x => ⟨x, by rw [h]; exact x.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        map_add' := by intros; rfl }
    have he : e.toAddCommGrpIso.hom ≫ addCommGrpExplicitImageι g =
        addCommGrpExplicitImageι f := by
      ext x
      rfl
    apply Subobject.mk_eq_mk_of_comm (image.ι f) (image.ι g)
      (addCommGrpImageIsoRange f ≪≫
        e.toAddCommGrpIso ≪≫ (addCommGrpImageIsoRange g).symm)
    have hf : (addCommGrpImageIsoRange f).hom ≫
        addCommGrpExplicitImageι f = image.ι f :=
      by
        simpa [addCommGrpImageIsoRange, addCommGrpExplicitImageFactorisation,
          addCommGrpExplicitImage] using
          (IsImage.isoExt_hom_m (Image.isImage f)
            (addCommGrpExplicitImageIsImage f))
    have hg : (addCommGrpImageIsoRange g).inv ≫ image.ι g =
        addCommGrpExplicitImageι g :=
      by
        simpa [addCommGrpImageIsoRange, addCommGrpExplicitImageFactorisation,
          addCommGrpExplicitImage] using
          (IsImage.isoExt_inv_m (Image.isImage g)
            (addCommGrpExplicitImageIsImage g))
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hg, he, hf]

/- Mathlib's canonical `Functor.IsMittagLeffler` is the underlying-set
formulation.  This bridge records its equivalence with the abelian image
formulation for the abelian groups used by the subsequent exactness lemmas. -/
theorem isMittagLeffler_iff_underlying
    (F : NatInverseSystem AddCommGrpCat) :
    IsMittagLeffler F ↔
      (F ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler := by
  change
    (∀ i : ℕ+, ∃ c : ℕ+, ∃ h : i ≤ c,
      ∀ k : ℕ+, ∀ h' : c ≤ k,
        imageSubobject (F.map (opHomOfLE h)) =
          imageSubobject (F.map (opHomOfLE (h.trans h')))) ↔
      (∀ j : ℕ+ᵒᵖ, ∃ k : ℕ+ᵒᵖ, ∃ f : k ⟶ j,
        ∀ l : ℕ+ᵒᵖ, ∀ g : l ⟶ j,
          Set.range (((F ⋙ CategoryTheory.forget AddCommGrpCat).map f)) ⊆
            Set.range (((F ⋙ CategoryTheory.forget AddCommGrpCat).map g)))
  constructor
  · intro h j
    obtain ⟨c, hic, hc⟩ := h j.unop
    refine ⟨Opposite.op c, opHomOfLE hic, ?_⟩
    intro k g
    have hjk : j.unop ≤ k.unop := le_of_op_hom g
    have hg : g = opHomOfLE hjk := Subsingleton.elim _ _
    rw [hg]
    by_cases hck : c ≤ k.unop
    · have heq := hc (k.unop) hck
      have hjk' : j.unop ≤ k.unop := hic.trans hck
      have hrange :=
        (addCommGrp_imageSubobject_eq_iff_range_eq
          (F.map (opHomOfLE hic))
          (F.map (opHomOfLE hjk'))).1 heq
      change Set.range (F.map (opHomOfLE hic)).hom ⊆
        Set.range (F.map (opHomOfLE hjk)).hom
      have hcomp' : opHomOfLE hjk' = opHomOfLE hjk :=
        Subsingleton.elim _ _
      rw [hcomp'] at hrange
      have hrange' : Set.range (F.map (opHomOfLE hic)).hom =
          Set.range (F.map (opHomOfLE hjk)).hom := by
        simpa only [AddMonoidHom.coe_range] using
          congrArg (fun K : AddSubgroup (F.obj j) => (K : Set (F.obj j))) hrange
      rw [hrange']
    · have hkc : k.unop ≤ c := le_of_not_ge hck
      change Set.range (F.map (opHomOfLE hic)).hom ⊆
        Set.range (F.map (opHomOfLE hjk)).hom
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      refine ⟨(F.map (opHomOfLE hkc)).hom y, ?_⟩
      have hcomp : opHomOfLE hkc ≫ opHomOfLE hjk =
          opHomOfLE (hjk.trans hkc) := by
        change (homOfLE hkc).op ≫ (homOfLE hjk).op =
          (homOfLE (hjk.trans hkc)).op
        rw [← op_comp, homOfLE_comp]
      have hcomp' : opHomOfLE (hjk.trans hkc) = opHomOfLE hic :=
        Subsingleton.elim _ _
      change (F.map (opHomOfLE hjk)).hom
          ((F.map (opHomOfLE hkc)).hom y) =
        (F.map (opHomOfLE hic)).hom y
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp, hcomp']
  · intro h i
    obtain ⟨c, f, hf⟩ := h (Opposite.op i)
    have hic : i ≤ c.unop := le_of_op_hom f
    have hf' : f = opHomOfLE hic := Subsingleton.elim _ _
    refine ⟨c.unop, hic, ?_⟩
    intro k hik
    have hkc : c.unop ≤ k := hik
    have hsub : Set.range (F.map (opHomOfLE hic)).hom ⊆
        Set.range (F.map (opHomOfLE (hic.trans hkc))).hom := by
      have hh := hf (Opposite.op k) (opHomOfLE (hic.trans hkc))
      change Set.range (F.map f).hom ⊆
        Set.range (F.map (opHomOfLE (hic.trans hkc))).hom at hh
      simpa [hf'] using hh
    have hrev : Set.range (F.map (opHomOfLE (hic.trans hkc))).hom ⊆
        Set.range (F.map (opHomOfLE hic)).hom := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      refine ⟨(F.map (opHomOfLE hkc)).hom y, ?_⟩
      have hcomp : opHomOfLE hkc ≫ opHomOfLE hic =
          opHomOfLE (hic.trans hkc) := by
        change (homOfLE hkc).op ≫ (homOfLE hic).op =
          (homOfLE (hic.trans hkc)).op
        rw [← op_comp, homOfLE_comp]
      change (F.map (opHomOfLE hic)).hom
          ((F.map (opHomOfLE hkc)).hom y) =
        (F.map (opHomOfLE (hic.trans hkc))).hom y
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    apply (addCommGrp_imageSubobject_eq_iff_range_eq
      (F.map (opHomOfLE hic)) (F.map (opHomOfLE (hic.trans hkc)))).2
    apply SetLike.ext
    intro x
    constructor
    · intro hx
      exact AddMonoidHom.mem_range.mpr (hsub (AddMonoidHom.mem_range.mp hx))
    · intro hx
      exact AddMonoidHom.mem_range.mpr (hrev (AddMonoidHom.mem_range.mp hx))

/-! ## Exactness after taking inverse limits -/

noncomputable def inverseSystemLimitMap
    {C : Type u} [Category.{v} C]
    {F G : NatInverseSystem C} [HasLimit F] [HasLimit G]
    (f : F ⟶ G) : inverseSystemLimit F ⟶ inverseSystemLimit G :=
  limMap f

/- These are the two finite presentations of the source's displayed exact
sequences. -/
noncomputable def inverseSystemLimitSequence
    (S : ShortComplex (NatInverseSystem AddCommGrpCat)) :
    ComposableArrows AddCommGrpCat 3 :=
  ComposableArrows.mk₃
    (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
    (inverseSystemLimitMap S.f)
    (inverseSystemLimitMap S.g)

noncomputable def inverseSystemLimitShortExactSequence
    (S : ShortComplex (NatInverseSystem AddCommGrpCat)) :
    ComposableArrows AddCommGrpCat 4 :=
  ComposableArrows.mk₄
    (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
    (inverseSystemLimitMap S.f)
    (inverseSystemLimitMap S.g)
    (0 : inverseSystemLimit S.X₃ ⟶ (0 : AddCommGrpCat))

theorem inverseSystemLimit_exact
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact) :
    (inverseSystemLimitSequence S).Exact := by
  have hexact : ∀ i : ℕ+ᵒᵖ, ∀ z : S.X₂.obj i, (S.g.app i) z = 0 →
      ∃ y : S.X₁.obj i, (S.f.app i) y = z := by
    intro i z hz
    have hSi := (inverseSystem_exact_iff_pointwise S).1 hS.exact i
    dsimp [Functor.mapShortComplex, evaluation] at hSi
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hSi z hz
    exact ⟨y, hy⟩
  have hinj : ∀ i : ℕ+ᵒᵖ, Function.Injective (S.f.app i) := by
    intro i
    apply (AddCommGrpCat.mono_iff_injective _).1
    exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f i
  have hA : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
      (limit.cone S.X₁)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (limit.isLimit S.X₁)
  have hzero : inverseSystemLimitMap S.f ≫ inverseSystemLimitMap S.g = 0 := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, inverseSystemLimitMap, limMap_π]
    rw [← Category.assoc, limMap_π S.f i, Category.assoc,
      ← NatTrans.comp_app, S.zero]
    simp
  have hmiddle :
      (ShortComplex.mk (inverseSystemLimitMap S.f)
        (inverseSystemLimitMap S.g) hzero).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x₂ hx₂
    change (limMap S.g) x₂ = 0 at hx₂
    have hxi : ∀ i : ℕ+ᵒᵖ, (S.g.app i) (limit.π S.X₂ i x₂) = 0 := by
      intro i
      rw [← ConcreteCategory.comp_apply, ← limMap_π S.g i,
        ConcreteCategory.comp_apply, hx₂]
      simp
    choose a ha using fun i => hexact i (limit.π S.X₂ i x₂) (hxi i)
    let sA : (S.X₁ ⋙ CategoryTheory.forget AddCommGrpCat).sections :=
      ⟨a, by
        intro i j f
        change (S.X₁.map f) (a i) = a j
        apply hinj j
        rw [← ConcreteCategory.comp_apply, S.f.naturality f,
          ConcreteCategory.comp_apply, ha i, ha j, ← ConcreteCategory.comp_apply,
          limit.w]
      ⟩
    refine ⟨(Types.isLimitEquivSections hA).symm sA, ?_⟩
    apply Concrete.limit_ext S.X₂
    intro i
    change (limit.π S.X₂ i) ((limMap S.f) ((Types.isLimitEquivSections hA).symm sA)) =
      (limit.π S.X₂ i) x₂
    rw [← ConcreteCategory.comp_apply, limMap_π, ConcreteCategory.comp_apply]
    have hπ : (limit.π S.X₁ i) ((Types.isLimitEquivSections hA).symm sA) =
        sA.val i := by
      simpa [Types.isLimitEquivSections, Types.sectionOfCone] using
        (Types.isLimitEquivSections_symm_apply hA sA i)
    rw [hπ, ha i]
  have hleft :
      (ShortComplex.mk (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
        (inverseSystemLimitMap S.f) (by simp)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x₁ hx₁
    change (limMap S.f) x₁ = 0 at hx₁
    have hxzero : x₁ = 0 := by
      apply Concrete.limit_ext S.X₁
      intro i
      apply hinj i
      have hlim := congrArg (fun q => q x₁) (limMap_π S.f i)
      simp only [ConcreteCategory.comp_apply] at hlim
      rw [← hlim, hx₁]
      simp
    exact ⟨0, by simp [hxzero]⟩
  refine
    { toIsComplex := { zero := ?_ }
      exact := ?_ }
  · intro i hi
    by_cases h : i = 0
    · subst i
      change (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁) ≫
        inverseSystemLimitMap S.f = 0
      simp
    · have hi' : i = 1 := by omega
      subst i
      change inverseSystemLimitMap S.f ≫ inverseSystemLimitMap S.g = 0
      exact hzero
  · intro i hi
    by_cases h : i = 0
    · subst i
      change
        (ShortComplex.mk (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
          (inverseSystemLimitMap S.f) _).Exact
      exact hleft
    · have hi' : i = 1 := by omega
      subst i
      change
        (ShortComplex.mk (inverseSystemLimitMap S.f)
          (inverseSystemLimitMap S.g) _).Exact
      exact hmiddle

theorem inverseSystemLimit_mittagLeffler_quotient
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hML : IsMittagLeffler S.X₂) :
    IsMittagLeffler S.X₃ := by
  have hML' := (isMittagLeffler_iff_underlying S.X₂).1 hML
  have hsurj : ∀ i : ℕ+ᵒᵖ, Function.Surjective (S.g.app i) := by
    intro i
    apply (AddCommGrpCat.epi_iff_surjective _).1
    exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g i
  apply (isMittagLeffler_iff_underlying S.X₃).2
  intro i
  obtain ⟨c, f, hf⟩ := hML' i
  refine ⟨c, f, ?_⟩
  intro k g
  intro z hz
  obtain ⟨z_c, rfl⟩ := hz
  obtain ⟨b_c, hb_c⟩ := hsurj c z_c
  have hb_range :
      (S.X₂.map f) b_c ∈
        Set.range ((S.X₂ ⋙ CategoryTheory.forget AddCommGrpCat).map g) :=
    hf g ⟨b_c, rfl⟩
  obtain ⟨b_k, hb_k⟩ := hb_range
  change (S.X₂.map g) b_k = (S.X₂.map f) b_c at hb_k
  refine ⟨S.g.app k b_k, ?_⟩
  have hnf := congrArg (fun q => q b_c) (S.g.naturality f)
  have hng := congrArg (fun q => q b_k) (S.g.naturality g)
  change (S.X₃.map g) (S.g.app k b_k) = (S.X₃.map f) z_c
  calc
    (S.X₃.map g) (S.g.app k b_k) =
        (S.g.app i) ((S.X₂.map g) b_k) := by
      simpa only [ConcreteCategory.comp_apply] using hng.symm
    _ = (S.g.app i) ((S.X₂.map f) b_c) := by rw [hb_k]
    _ = (S.X₃.map f) (S.g.app c b_c) := by
      simpa only [ConcreteCategory.comp_apply] using hnf
    _ = (S.X₃.map f) z_c := by rw [hb_c]

theorem inverseSystemLimit_exact_of_mittagLeffler
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hML : IsMittagLeffler S.X₁) :
    (inverseSystemLimitShortExactSequence S).Exact := by
  let hI : IsDirectedSet ℕ+ := ⟨inferInstance, inferInstance⟩
  have hS' :
      Formalization.Books.Algebra.Unit86.IsPointwiseShortExact S := by
    intro i
    have hi := (inverseSystem_exact_iff_pointwise S).1 hS.exact i
    refine { exact := hi, mono_f := ?_, epi_g := ?_ }
    · exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f i
    · exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g i
  have hlim :=
    Formalization.Books.Algebra.Unit86.inverse_limit_shortExact_of_countable_mittagLeffler
      hI S hS' ((isMittagLeffler_iff_underlying S.X₁).1 hML)
  refine { toIsComplex := { zero := ?_ }, exact := ?_ }
  · intro i hi
    have hi0 : i + 2 ≤ 4 := hi
    have hi_le : i ≤ 2 := by omega
    by_cases h : i = 0
    · subst i
      change (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁) ≫
        inverseSystemLimitMap S.f = 0
      simp
    · by_cases h' : i = 1
      · subst i
        change inverseSystemLimitMap S.f ≫ inverseSystemLimitMap S.g = 0
        exact (Formalization.Books.Algebra.Unit86.inverseLimitShortComplex S).zero
      · have hi' : i = 2 := by omega
        subst i
        change inverseSystemLimitMap S.g ≫
          (0 : inverseSystemLimit S.X₃ ⟶ (0 : AddCommGrpCat)) = 0
        simp
  · intro i hi
    have hi0 : i + 2 ≤ 4 := hi
    have hi_le : i ≤ 2 := by omega
    by_cases h : i = 0
    · subst i
      change (ShortComplex.mk (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
        (inverseSystemLimitMap S.f) _).Exact
      exact (ShortComplex.exact_iff_mono _ (by simp)).2 hlim.mono_f
    · by_cases h' : i = 1
      · subst i
        change (ShortComplex.mk (inverseSystemLimitMap S.f)
          (inverseSystemLimitMap S.g) _).Exact
        exact hlim.exact
      · have hi' : i = 2 := by omega
        subst i
        change (ShortComplex.mk (inverseSystemLimitMap S.g)
          (0 : inverseSystemLimit S.X₃ ⟶ (0 : AddCommGrpCat)) _).Exact
        exact (ShortComplex.exact_iff_epi _ (by simp)).2 hlim.epi_g

theorem inverseSystemLimit_exact_of_exact_of_mittagLeffler
    (S : ComposableArrows (NatInverseSystem AddCommGrpCat) 3)
    (hS : S.Exact)
    (hML : IsMittagLeffler (S.obj' 0)) :
    (ComposableArrows.mk₂
      (inverseSystemLimitMap (S.map' 1 2))
      (inverseSystemLimitMap (S.map' 2 3))).Exact := by
  let hI : IsDirectedSet ℕ+ := ⟨inferInstance, inferInstance⟩
  let T₀ : ShortComplex (NatInverseSystem AddCommGrpCat) :=
    ShortComplex.mk (S.map' 0 1) (S.map' 1 2)
      (by simpa using hS.toIsComplex.zero 0)
  let T₁ : ShortComplex (NatInverseSystem AddCommGrpCat) :=
    ShortComplex.mk (S.map' 1 2) (S.map' 2 3)
      (by simpa using hS.toIsComplex.zero 1)
  have hT₀ : T₀.Exact := by
    exact hS.exact 0
  have hT₁ : T₁.Exact := by
    exact hS.exact 1
  have hT₀' := (inverseSystem_exact_iff_pointwise T₀).1 hT₀
  have hT₁' := (inverseSystem_exact_iff_pointwise T₁).1 hT₁
  have hlocal₀ : ∀ i : ℕ+ᵒᵖ, ∀ x : (S.obj' 1).obj i,
      (S.map' 1 2).app i x = 0 →
        ∃ y : (S.obj' 0).obj i, (S.map' 0 1).app i y = x := by
    intro i x hx
    have hi := hT₀' i
    dsimp [Functor.mapShortComplex, evaluation, T₀] at hi
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hi x hx
    exact ⟨y, hy⟩
  have hlocal₁ : ∀ i : ℕ+ᵒᵖ, ∀ x : (S.obj' 2).obj i,
      (S.map' 2 3).app i x = 0 →
        ∃ y : (S.obj' 1).obj i, (S.map' 1 2).app i y = x := by
    intro i x hx
    have hi := hT₁' i
    dsimp [Functor.mapShortComplex, evaluation, T₁] at hi
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hi x hx
    exact ⟨y, hy⟩
  have hzero :
      inverseSystemLimitMap (S.map' 1 2) ≫
        inverseSystemLimitMap (S.map' 2 3) = 0 := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, inverseSystemLimitMap, limMap_π]
    rw [← Category.assoc, limMap_π (S.map' 1 2) i, Category.assoc,
      ← NatTrans.comp_app, hS.toIsComplex.zero 1]
    simp
  refine { toIsComplex := { zero := ?_ }, exact := ?_ }
  · intro i hi
    have hi' : i = 0 := by omega
    subst i
    change inverseSystemLimitMap (S.map' 1 2) ≫
      inverseSystemLimitMap (S.map' 2 3) = 0
    exact hzero
  · intro i hi
    have hi' : i = 0 := by omega
    subst i
    change (ShortComplex.mk (inverseSystemLimitMap (S.map' 1 2))
      (inverseSystemLimitMap (S.map' 2 3)) _).Exact
    rw [ShortComplex.ab_exact_iff]
    let hB : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
        (limit.cone (S.obj' 1))) :=
      isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat)
        (limit.isLimit (S.obj' 1))
    let hC : IsLimit ((CategoryTheory.forget AddCommGrpCat).mapCone
        (limit.cone (S.obj' 2))) :=
      isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat)
        (limit.isLimit (S.obj' 2))
    intro x₂ hx₂
    change (limMap (S.map' 2 3)) x₂ = 0 at hx₂
    have hxi : ∀ i : ℕ+ᵒᵖ,
        (S.map' 2 3).app i (limit.π (S.obj' 2) i x₂) = 0 := by
      intro i
      rw [← ConcreteCategory.comp_apply, ← limMap_π (S.map' 2 3) i,
        ConcreteCategory.comp_apply, hx₂]
      simp
    let eC := Types.isLimitEquivSections hC
    let s₂ : ((S.obj' 2) ⋙ CategoryTheory.forget AddCommGrpCat).sections := eC x₂
    let E : ℕ+ᵒᵖ ⥤ Type _ :=
      { obj := fun i => {x : (S.obj' 1).obj i //
          (S.map' 1 2).app i x = s₂.val i}
        map := fun {i j} f => ↾(fun
          (x : {x : (S.obj' 1).obj i //
              (S.map' 1 2).app i x = s₂.val i}) =>
            (⟨(S.obj' 1).map f x.1, by
              rw [← ConcreteCategory.comp_apply, (S.map' 1 2).naturality f,
                ConcreteCategory.comp_apply, x.2]
              change (S.obj' 2).map f (s₂.val i) = s₂.val j
              exact s₂.property f⟩ : {x : (S.obj' 1).obj j //
                (S.map' 1 2).app j x = s₂.val j}))
        map_id := by
          intro i
          ext x
          simp
        map_comp := by
          intro i j k f g
          ext x
          simp }
    have hEne : ∀ i : ℕ+ᵒᵖ, Nonempty (E.obj i) := by
      intro i
      obtain ⟨x, hx⟩ := hlocal₁ i (limit.π (S.obj' 2) i x₂) (hxi i)
      change Nonempty {x : (S.obj' 1).obj i //
        (S.map' 1 2).app i x = s₂.val i}
      exact ⟨⟨x, by
        simpa [s₂, eC, Types.isLimitEquivSections, Types.sectionOfCone] using hx⟩⟩
    have hEML : E.IsMittagLeffler := by
      intro j
      obtain ⟨i, f, hf⟩ := (isMittagLeffler_iff_underlying (S.obj' 0)).1 hML j
      refine ⟨i, f, ?_⟩
      intro k g
      rintro _ ⟨eᵢ, rfl⟩
      obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
      obtain ⟨eₗ⟩ := hEne l
      have hker : (S.map' 1 2).app i (eᵢ - (E.map a eₗ).1) = 0 := by
        rw [map_sub, eᵢ.2, (E.map a eₗ).2]
        simp
      obtain ⟨aᵢ, haᵢ⟩ :=
        hlocal₀ i (eᵢ.1 - (E.map a eₗ).1) hker
      obtain ⟨aₖ, haₖ⟩ := hf g ⟨aᵢ, rfl⟩
      let eₖ : E.obj k :=
        ⟨(E.map b eₗ).1 + (S.map' 0 1).app k aₖ, by
          rw [map_add, (E.map b eₗ).2]
          have hz := congrArg (fun q => q.app k) (hS.toIsComplex.zero 0)
          simp only [NatTrans.comp_app] at hz
          have hz' := congrArg (fun q => q aₖ) hz
          have hzero' : (S.map' 1 2).app k ((S.map' 0 1).app k aₖ) = 0 := by
            simpa using hz'
          rw [hzero']
          simp
        ⟩
      refine ⟨eₖ, ?_⟩
      apply Subtype.ext
      change (S.obj' 1).map g eₖ.1 = (S.obj' 1).map f eᵢ
      change (S.obj' 1).map g ((E.map b eₗ).1 +
          (S.map' 0 1).app k aₖ) = (S.obj' 1).map f eᵢ
      have hga : (S.obj' 1).map g ((E.map b eₗ).1) =
          (S.obj' 1).map f ((E.map a eₗ).1) := by
        change (S.obj' 1).map g ((S.obj' 1).map b eₗ.1) =
          (S.obj' 1).map f ((S.obj' 1).map a eₗ.1)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← (S.obj' 1).map_comp, ← (S.obj' 1).map_comp, hab]
      have hfa : (S.obj' 1).map f ((S.map' 0 1).app i aᵢ) =
          (S.map' 0 1).app j ((S.obj' 0).map f aᵢ) := by
        rw [← ConcreteCategory.comp_apply, ← (S.map' 0 1).naturality f,
          ConcreteCategory.comp_apply]
      have hgf : (S.obj' 1).map g ((S.map' 0 1).app k aₖ) =
          (S.map' 0 1).app j ((S.obj' 0).map g aₖ) := by
        rw [← ConcreteCategory.comp_apply, ← (S.map' 0 1).naturality g,
          ConcreteCategory.comp_apply]
      have hdiff : (S.map' 0 1).app j ((S.obj' 0).map f aᵢ) =
          (S.obj' 1).map f (eᵢ - (E.map a eₗ).1) := by
        rw [← hfa, haᵢ]
      have haₖ' : (S.obj' 0).map g aₖ = (S.obj' 0).map f aᵢ := by
        exact haₖ
      rw [map_add, hga, hgf, haₖ', hdiff, map_sub]
      abel
    obtain ⟨sE, hsE⟩ :=
      Formalization.Books.Algebra.Unit86.nonempty_limit_of_countable_mittagLeffler
        hI E hEML hEne
    let sB : ((S.obj' 1) ⋙ CategoryTheory.forget AddCommGrpCat).sections :=
      ⟨fun i => (sE i).1, by
        intro i j f
        exact congrArg Subtype.val (hsE f)⟩
    let x₁ := (Types.isLimitEquivSections hB).symm sB
    refine ⟨x₁, ?_⟩
    apply Concrete.limit_ext (S.obj' 2)
    intro i
    change (limMap (S.map' 1 2) ≫
        limit.π (S.obj' 2) i) x₁ = (limit.π (S.obj' 2) i) x₂
    rw [limMap_π, ConcreteCategory.comp_apply]
    have hπB : (limit.π (S.obj' 1) i) x₁ = sB.val i := by
      simpa [x₁, Types.isLimitEquivSections, Types.sectionOfCone] using
        (Types.isLimitEquivSections_symm_apply hB sB i)
    have hπC : s₂.val i = (limit.π (S.obj' 2) i) x₂ := by
      simp [s₂, eC, Types.isLimitEquivSections, Types.sectionOfCone]
    have hfiber : (S.map' 1 2).app i (sB.val i) = s₂.val i := by
      change (S.map' 1 2).app i ((sE i).1) = s₂.val i
      exact (sE i).2
    rw [hπB, hfiber, hπC]

/-! ## Essentially constant systems -/

/- This is the canonical definition from Categories, Chapter 22, specialized
to the positive-integer inverse-system index. -/
abbrev IsEssentiallyConstant
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) : Prop :=
  Formalization.Books.Categories.Unit22.IsEssentiallyConstantInverseSystem F

/- The source's direct-sum decomposition is written with biproducts.  The
maps `z` are the induced maps on the complementary summands; compatibility
means that every transition map is the identity on the limit summand and is
`z` on the complementary summand. -/
theorem essentiallyConstant_iff_biproduct_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C) [HasLimit F] :
    IsEssentiallyConstant F ↔
      ∃ (i : ℕ+) (Z : ℕ+ → C)
        (e : ∀ j : ℕ+, i ≤ j →
          @CategoryTheory.Iso C _
            (@CategoryTheory.Limits.biprod C _ _ (inverseSystemLimit F) (Z j) _)
            (F.obj (Opposite.op j)))
        (z : ∀ {j j' : ℕ+}, j ≤ j' →
          @Quiver.Hom C _ (Z j') (Z j)),
        (∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j') (h : j ≤ j'),
          (e j' hij').hom ≫ transitionMap F h ≫ (e j hij).inv =
            biprod.map (𝟙 _) (z h)) ∧
        (∀ j : ℕ+, ∃ (j' : ℕ+) (h : j ≤ j'), z h = 0) := by
  have split_data :
      ∀ {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y), j ≫ q = 𝟙 Y →
        ∃ e : biprod Y (kernel (q ≫ j)) ≅ X,
          e.hom ≫ q = biprod.fst ∧ biprod.inl ≫ e.hom = j ∧
            biprod.inr ≫ e.hom = kernel.ι (q ≫ j) := by
    intro X Y j q h
    letI : Mono j := ⟨fun a b hab => by
      rw [← Category.comp_id a, ← Category.comp_id b, ← h,
        ← Category.assoc, ← Category.assoc, hab]⟩
    have he : (q ≫ j) ≫ (q ≫ j) = q ≫ j := by
      rw [Category.assoc, ← Category.assoc j q j, h, Category.id_comp]
    have hk : (𝟙 X - q ≫ j) ≫ (q ≫ j) = 0 := by
      rw [sub_comp, Category.id_comp, he, sub_self]
    let p : X ⟶ kernel (q ≫ j) :=
      kernel.lift (q ≫ j) (𝟙 X - q ≫ j) hk
    have hp : p ≫ kernel.ι (q ≫ j) = 𝟙 X - q ≫ j := by
      exact kernel.lift_ι _ _ _
    have hkp : kernel.ι (q ≫ j) ≫ p = 𝟙 _ := by
      apply Fork.IsLimit.hom_ext (kernelIsKernel (q ≫ j))
      calc
        (kernel.ι (q ≫ j) ≫ p) ≫ kernel.ι (q ≫ j) =
            kernel.ι (q ≫ j) ≫ (p ≫ kernel.ι (q ≫ j)) := by simp [Category.assoc]
        _ = kernel.ι (q ≫ j) ≫ (𝟙 X - q ≫ j) := by rw [hp]
        _ = kernel.ι (q ≫ j) := by
          rw [comp_sub, Category.comp_id, kernel.condition, sub_zero]
        _ = (𝟙 _) ≫ kernel.ι (q ≫ j) := by simp
    have hjq : kernel.ι (q ≫ j) ≫ q = 0 := by
      apply (cancel_mono j).1
      rw [Category.assoc, kernel.condition, zero_comp]
    have hjp : j ≫ p = 0 := by
      apply (cancel_mono (kernel.ι (q ≫ j))).1
      rw [zero_comp, Category.assoc, hp, comp_sub, Category.comp_id,
        ← Category.assoc, h, Category.id_comp, sub_self]
    let eh : biprod Y (kernel (q ≫ j)) ⟶ X :=
      biprod.desc j (kernel.ι (q ≫ j))
    let ei : X ⟶ biprod Y (kernel (q ≫ j)) := biprod.lift q p
    have hjlift : j ≫ ei = biprod.inl := by
      apply biprod.hom_ext
      · simp [ei, h]
      · simp [ei, hjp]
    have hklift : kernel.ι (q ≫ j) ≫ ei = biprod.inr := by
      apply biprod.hom_ext
      · dsimp [ei]
        simp only [Category.assoc, biprod.lift_fst, hjq, biprod.inr_fst]
      · dsimp [ei]
        simp only [Category.assoc, biprod.lift_snd, hkp, biprod.inr_snd]
    have hhi : eh ≫ ei = 𝟙 _ := by
      apply biprod.hom_ext'
      · simp [eh, hjlift]
      · simp [eh, hklift]
    have hih : ei ≫ eh = 𝟙 _ := by
      change biprod.lift q p ≫ biprod.desc j (kernel.ι (q ≫ j)) = 𝟙 X
      rw [biprod.lift_desc, hp]
      abel
    refine ⟨Iso.mk eh ei hhi hih, ?_, ?_, ?_⟩
    · dsimp [eh]
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_desc, h]
        simp
      · rw [← Category.assoc, biprod.inr_desc, hjq]
        simp
    · change biprod.inl ≫ eh = j
      simp [eh]
    · change biprod.inr ≫ eh = kernel.ι (q ≫ j)
      simp [eh]
  constructor
  · intro hF
    rcases hF with ⟨hI, hF⟩
    letI : Nonempty ℕ+ := hI.1
    letI : IsDirectedOrder ℕ+ := hI.2
    obtain ⟨c, hcLim, hc⟩ := essentiallyConstantPro_hasLimit hF
    rcases hc with ⟨i, r, hr, hfactor⟩
    let hcl : IsLimit c := Classical.choice hcLim
    let ec : c.pt ≅ inverseSystemLimit F :=
      hcl.conePointUniqueUpToIso (limit.isLimit F)
    let i₀ : ℕ+ := i.unop
    let q (j : ℕ+) (hij : i₀ ≤ j) :
        F.obj (Opposite.op j) ⟶ inverseSystemLimit F :=
      F.map (opHomOfLE hij) ≫ r ≫ ec.hom
    let l (j : ℕ+) : inverseSystemLimit F ⟶ F.obj (Opposite.op j) :=
      ec.inv ≫ c.π.app (Opposite.op j)
    have hsplit : ∀ (j : ℕ+) (hij : i₀ ≤ j),
        l j ≫ q j hij = 𝟙 _ := by
      intro j hij
      dsimp [l, q]
      rw [Category.assoc ec.inv (c.π.app (Opposite.op j))
        (F.map (opHomOfLE hij) ≫ r ≫ ec.hom)]
      rw [← Category.assoc (c.π.app (Opposite.op j))
        (F.map (opHomOfLE hij)) (r ≫ ec.hom)]
      rw [c.w (opHomOfLE hij)]
      rw [← Category.assoc (c.π.app i) r ec.hom, hr]
      simp
    have hdata : ∀ (j : ℕ+) (hij : i₀ ≤ j),
        ∃ e : biprod (inverseSystemLimit F) (kernel (q j hij ≫ l j)) ≅
            F.obj (Opposite.op j),
          e.hom ≫ q j hij = biprod.fst ∧
            biprod.inl ≫ e.hom = l j ∧
              biprod.inr ≫ e.hom = kernel.ι (q j hij ≫ l j) := by
      intro j hij
      exact split_data (l j) (q j hij) (hsplit j hij)
    choose e₀ he₀q he₀inl he₀inr using hdata
    let Z (j : ℕ+) : C :=
      if hij : i₀ ≤ j then kernel (q j hij ≫ l j) else 0
    have hZ : ∀ (j : ℕ+) (hij : i₀ ≤ j),
        Z j = kernel (q j hij ≫ l j) := by
      intro j hij
      simp [Z, hij]
    let e : ∀ (j : ℕ+), i₀ ≤ j →
        @CategoryTheory.Iso C _
          (@CategoryTheory.Limits.biprod C _ _ (inverseSystemLimit F) (Z j) _)
          (F.obj (Opposite.op j)) :=
      fun j hij =>
        (biprod.mapIso (Iso.refl _) (eqToIso (hZ j hij))) ≪≫ e₀ j hij
    have hq : ∀ {j j' : ℕ+} (hij : i₀ ≤ j) (h : j ≤ j'),
        q j' (hij.trans h) = transitionMap F h ≫ q j hij := by
      intro j j' hij h
      have hmap : F.map (opHomOfLE (hij.trans h)) =
          F.map (opHomOfLE h) ≫ F.map (opHomOfLE hij) := by
        rw [← F.map_comp]
        congr 1
      dsimp [q, transitionMap]
      rw [hmap]
      simp only [Category.assoc]
    have hl : ∀ {j j' : ℕ+} (h : j ≤ j'),
        l j' ≫ transitionMap F h = l j := by
      intro j j' h
      dsimp [l, transitionMap]
      rw [Category.assoc, c.w]
    have hpcomm : ∀ {j j' : ℕ+} (hij : i₀ ≤ j) (h : j ≤ j'),
        (q j' (hij.trans h) ≫ l j') ≫ transitionMap F h =
          transitionMap F h ≫ (q j hij ≫ l j) := by
      intro j j' hij h
      rw [Category.assoc, hl h, hq hij h]
      simp only [Category.assoc]
    let z₀ : ∀ {j j' : ℕ+} (hij : i₀ ≤ j) (h : j ≤ j'),
        kernel (q j' (hij.trans h) ≫ l j') ⟶ kernel (q j hij ≫ l j) :=
      fun {j j'} hij h =>
        kernel.lift (q j hij ≫ l j)
          (kernel.ι (q j' (hij.trans h) ≫ l j') ≫ transitionMap F h) (by
            calc
              (kernel.ι (q j' (hij.trans h) ≫ l j') ≫ transitionMap F h) ≫
                  (q j hij ≫ l j) =
                  kernel.ι (q j' (hij.trans h) ≫ l j') ≫
                    (transitionMap F h ≫ (q j hij ≫ l j)) := by
                      simp only [Category.assoc]
              _ = kernel.ι (q j' (hij.trans h) ≫ l j') ≫
                    ((q j' (hij.trans h) ≫ l j') ≫ transitionMap F h) := by
                      rw [hpcomm hij h]
              _ = (kernel.ι (q j' (hij.trans h) ≫ l j') ≫
                    (q j' (hij.trans h) ≫ l j')) ≫ transitionMap F h := by
                      simp only [Category.assoc]
              _ = 0 := by rw [kernel.condition, zero_comp])
    let z : ∀ {j j' : ℕ+} (h : j ≤ j'), Z j' ⟶ Z j :=
      fun {j j'} h => if hij : i₀ ≤ j then
        (show Z j' ⟶ Z j from by
          exact (eqToIso (hZ j' (hij.trans h))).hom ≫ z₀ hij h ≫
            (eqToIso (hZ j hij)).inv)
      else 0
    refine ⟨i₀, Z, e, z, ?_, ?_⟩
    · intro j j' hij hij' h
      have heq_q : (e j hij).hom ≫ q j hij = biprod.fst := by
        simp [e, he₀q j hij]
      have heq_q' : (e j' hij').hom ≫ q j' hij' = biprod.fst := by
        simp [e, he₀q j' hij']
      have heq_inl : biprod.inl ≫ (e j hij).hom = l j := by
        simp [e, he₀inl j hij]
      have heq_inl' : biprod.inl ≫ (e j' hij').hom = l j' := by
        simp [e, he₀inl j' hij']
      let ιj : Z j ⟶ F.obj (Opposite.op j) :=
        (eqToIso (hZ j hij)).hom ≫ kernel.ι (q j hij ≫ l j)
      let ιj' : Z j' ⟶ F.obj (Opposite.op j') :=
        (eqToIso (hZ j' (hij.trans h))).hom ≫
          kernel.ι (q j' (hij.trans h) ≫ l j')
      have heq_inr : biprod.inr ≫ (e j hij).hom = ιj := by
        simp [e, ιj, he₀inr j hij]
      have heq_inr' : biprod.inr ≫ (e j' hij').hom = ιj' := by
        simp [e, ιj', he₀inr j' hij']
      have hzcomp : z h ≫ ιj = ιj' ≫ transitionMap F h := by
        simp only [z, dif_pos hij, ιj, ιj', Category.assoc]
        simp [Category.assoc]
        rw [kernel.lift_ι]
      apply (cancel_mono (e j hij).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply biprod.hom_ext'
      · conv_lhs => rw [← Category.assoc]
        conv_rhs => rw [← Category.assoc]
        rw [heq_inl', hl h, biprod.inl_map]
        simp only [Category.id_comp, Category.assoc]
        rw [heq_inl]
      · conv_lhs => rw [← Category.assoc]
        conv_rhs => rw [← Category.assoc]
        rw [heq_inr', biprod.inr_map]
        simp only [Category.assoc]
        rw [heq_inr]
        exact hzcomp.symm
    · intro j
      by_cases hij : i₀ ≤ j
      · obtain ⟨k, f, g, hfg⟩ := hfactor (Opposite.op j)
        let j' : ℕ+ := k.unop
        have hij' : i₀ ≤ j' := le_of_op_hom f
        have hj' : j ≤ j' := le_of_op_hom g
        let hij'' : i₀ ≤ j' := hij.trans hj'
        refine ⟨j', hj', ?_⟩
        have hf : f = opHomOfLE hij'' := Subsingleton.elim _ _
        have hg : g = opHomOfLE hj' := Subsingleton.elim _ _
        have hfg' : transitionMap F hj' = q j' hij'' ≫ l j := by
          dsimp [transitionMap, q, l, j']
          rw [← hg, hfg, hf]
          simp
        letI : Mono (l j') := ⟨fun a b hab => by
          calc
            a = a ≫ 𝟙 _ := by simp
            _ = a ≫ (l j' ≫ q j' hij'') := by rw [hsplit]
            _ = (a ≫ l j') ≫ q j' hij'' := by simp only [Category.assoc]
            _ = (b ≫ l j') ≫ q j' hij'' := by rw [hab]
            _ = b := by simp [Category.assoc, hsplit]⟩
        have hqzero : kernel.ι (q j' hij'' ≫ l j') ≫ q j' hij'' = 0 := by
          apply (cancel_mono (l j')).1
          simp only [Category.assoc, kernel.condition, zero_comp]
        let ιj : Z j ⟶ F.obj (Opposite.op j) :=
          (eqToIso (hZ j hij)).hom ≫ kernel.ι (q j hij ≫ l j)
        let ιj' : Z j' ⟶ F.obj (Opposite.op j') :=
          (eqToIso (hZ j' hij'')).hom ≫
            kernel.ι (q j' hij'' ≫ l j')
        have hzcomp' : z hj' ≫ ιj = ιj' ≫ transitionMap F hj' := by
          simp only [z, dif_pos hij, ιj, ιj', Category.assoc]
          simp [Category.assoc]
          rw [kernel.lift_ι]
        apply (cancel_mono ιj).1
        rw [hzcomp', hfg']
        dsimp [ιj']
        have hh := congrArg
          (fun u => eqToHom (hZ j' hij'') ≫ u ≫ l j) hqzero
        simpa only [Category.assoc, zero_comp, comp_zero] using hh
      · refine ⟨j, le_rfl, ?_⟩
        dsimp [z]
        rw [dif_neg hij]
  · intro hdecomp
    rcases hdecomp with ⟨i, Z, e, z, hcompat, hzero⟩
    letI : Nonempty ℕ+ := ⟨i⟩
    letI : IsDirectedOrder ℕ+ := inferInstance
    let l : ∀ j : ℕ+, inverseSystemLimit F ⟶ F.obj (Opposite.op j) :=
      fun j => if hij : i ≤ j then
        biprod.inl ≫ (e j hij).hom
      else
        biprod.inl ≫ (e i le_rfl).hom ≫ transitionMap F (le_of_not_ge hij)
    have hcompat' : ∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j') (h : j ≤ j'),
        (e j' hij').hom ≫ transitionMap F h =
          biprod.map (𝟙 _) (z h) ≫ (e j hij).hom := by
      intro j j' hij hij' h
      calc
        (e j' hij').hom ≫ transitionMap F h =
            ((e j' hij').hom ≫ transitionMap F h) ≫
              (e j hij).inv ≫ (e j hij).hom := by simp [Category.assoc]
        _ = biprod.map (𝟙 _) (z h) ≫ (e j hij).hom := by
          have hh := congrArg (fun u => u ≫ (e j hij).hom)
            (hcompat hij hij' h)
          simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh
    have hl : ∀ {j j' : ℕ+} (h : j ≤ j'),
        l j' ≫ transitionMap F h = l j := by
      intro j j' h
      by_cases hj : i ≤ j
      · have hj' : i ≤ j' := hj.trans h
        dsimp [l]
        rw [dif_pos hj', dif_pos hj]
        rw [Category.assoc, hcompat' hj hj' h]
        simp [Category.assoc]
      · by_cases hj' : i ≤ j'
        · have hji : j ≤ i := le_of_not_ge hj
          dsimp [l]
          rw [dif_pos hj', dif_neg hj]
          have hcomp : transitionMap F h =
              transitionMap F hj' ≫ transitionMap F hji := by
            dsimp [transitionMap]
            rw [← F.map_comp]
            congr 1
          rw [hcomp]
          simp only [Category.assoc]
          have hh := congrArg
            (fun u => biprod.inl ≫ u ≫ transitionMap F hji)
            (hcompat' le_rfl hj' hj')
          simpa only [← Category.assoc, biprod.inl_map, Category.id_comp] using hh
        · have hji : j ≤ i := le_of_not_ge hj
          have hji' : j' ≤ i := le_of_not_ge hj'
          dsimp [l]
          rw [dif_neg hj', dif_neg hj]
          simp only [Category.assoc]
          have hh := congrArg
            (fun u => biprod.inl ≫ (e i le_rfl).hom ≫ u)
            (transitionMap_comp F hji' h)
          simpa only [Category.assoc] using hh
    let c : Cone F :=
      { pt := inverseSystemLimit F
        π :=
          { app := fun j => l j.unop
            naturality := by
              intro j j' f
              change (𝟙 _ : inverseSystemLimit F ⟶ inverseSystemLimit F) ≫ l j'.unop =
                l j.unop ≫ F.map f
              simp only [Category.id_comp]
              have hf : f = opHomOfLE (le_of_op_hom f) := Subsingleton.elim _ _
              rw [hf]
              exact (hl (le_of_op_hom f)).symm } }
    refine ⟨⟨⟨i⟩, inferInstance⟩, ?_⟩
    refine ⟨c, ?_⟩
    refine ⟨Opposite.op i, (e i le_rfl).inv ≫ biprod.fst, ?_, ?_⟩
    · dsimp [c, l]
      rw [dif_pos le_rfl]
      simp
    have hkill : ∀ {a b k : ℕ+} (hia : i ≤ a) (hab : a ≤ b)
        (hbk : b ≤ k) (hz : z hab = 0),
        transitionMap F (hab.trans hbk) =
          (e k (hia.trans (hab.trans hbk))).inv ≫ biprod.fst ≫
            biprod.inl ≫ (e a hia).hom := by
      intro a b k hia hab hbk hz
      let hka : a ≤ k := hab.trans hbk
      let hik : i ≤ k := hia.trans hka
      have hcomp : transitionMap F hka =
          transitionMap F hbk ≫ transitionMap F hab := by
        dsimp [transitionMap]
        rw [← F.map_comp]
        congr 1
      have heq : (e k hik).hom ≫ transitionMap F hka =
          biprod.fst ≫ biprod.inl ≫ (e a hia).hom := by
        calc
          (e k hik).hom ≫ transitionMap F hka =
              (e k hik).hom ≫ transitionMap F hbk ≫ transitionMap F hab := by
                rw [hcomp]
          _ = biprod.map (𝟙 _) (z hbk) ≫ (e b (hia.trans hab)).hom ≫
                transitionMap F hab := by
                have hh := congrArg (fun u => u ≫ transitionMap F hab)
                  (hcompat' (hia.trans hab) hik hbk)
                simpa only [Category.assoc] using hh
          _ = biprod.map (𝟙 _) (z hbk) ≫
                (biprod.map (𝟙 _) (z hab) ≫ (e a hia).hom) := by
                have hh := congrArg
                  (fun u => biprod.map (𝟙 _) (z hbk) ≫ u)
                  (hcompat' hia (hia.trans hab) hab)
                simpa only [Category.assoc] using hh
          _ = biprod.fst ≫ biprod.inl ≫ (e a hia).hom := by
                rw [← Category.assoc]
                have hmap :
                    (biprod.map (𝟙 (inverseSystemLimit F)) (z hbk) :
                        inverseSystemLimit F ⊞ Z k ⟶ inverseSystemLimit F ⊞ Z b) ≫
                      (biprod.map (𝟙 (inverseSystemLimit F)) (z hab) :
                        inverseSystemLimit F ⊞ Z b ⟶ inverseSystemLimit F ⊞ Z a) =
                    (biprod.fst : inverseSystemLimit F ⊞ Z k ⟶ inverseSystemLimit F) ≫
                      (biprod.inl : inverseSystemLimit F ⟶ inverseSystemLimit F ⊞ Z a) := by
                  apply biprod.hom_ext
                  · simp [Category.assoc]
                  · simp [hz, Category.assoc]
                rw [hmap]
                simp only [Category.assoc]
      calc
        transitionMap F hka = 𝟙 _ ≫ transitionMap F hka := by simp
        _ = ((e k hik).inv ≫ (e k hik).hom) ≫ transitionMap F hka := by simp
        _ = (e k hik).inv ≫
              ((e k hik).hom ≫ transitionMap F hka) := by simp only [Category.assoc]
        _ = (e k hik).inv ≫
              (biprod.fst ≫ biprod.inl ≫ (e a hia).hom) := by rw [heq]
        _ = (e k hik).inv ≫ biprod.fst ≫ biprod.inl ≫ (e a hia).hom := by
              simp only [Category.assoc]
    · intro j
      let j₀ : ℕ+ := j.unop
      by_cases hij : i ≤ j₀
      · obtain ⟨b, hab, hz⟩ := hzero j₀
        obtain ⟨k, hik, hbk⟩ := directed_of (· ≤ ·) i b
        have hbj : j₀ ≤ k := hab.trans hbk
        have hg : Opposite.op k ⟶ j := by
          exact opHomOfLE hbj
        have hf : Opposite.op k ⟶ Opposite.op i := opHomOfLE hik
        have hfac := hkill hij hab hbk hz
        refine ⟨Opposite.op k, hf, hg, ?_⟩
        sorry
      · have hji : j₀ ≤ i := le_of_not_ge hij
        obtain ⟨b, hib, hz⟩ := hzero i
        obtain ⟨k, hik, hbk⟩ := directed_of (· ≤ ·) i b
        have hbj : j₀ ≤ k := hji.trans hik
        have hg : Opposite.op k ⟶ j := by
          exact opHomOfLE hbj
        have hf : Opposite.op k ⟶ Opposite.op i := opHomOfLE hik
        have hfac := hkill le_rfl hib hbk hz
        refine ⟨Opposite.op k, hf, hg, ?_⟩
        sorry

theorem essentiallyConstant_isMittagLeffler
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C)
    (hF : IsEssentiallyConstant F) :
    IsMittagLeffler F := by
  rcases hF with ⟨hI, hF⟩
  letI : Nonempty ℕ+ := hI.1
  letI : IsDirectedOrder ℕ+ := hI.2
  rcases hF with ⟨c, i, r, hr, hfactor⟩
  have image_eq_of_factor : ∀ {X X' Y : C} (f : X ⟶ Y) (g : X' ⟶ Y)
      (a : X ⟶ X') (b : X' ⟶ X), a ≫ g = f → b ≫ f = g →
      imageSubobject f = imageSubobject g := by
    intro X X' Y f g a b haf hbg
    apply le_antisymm
    · rw [← haf]
      exact imageSubobject_comp_le a g
    · rw [← hbg]
      exact imageSubobject_comp_le b f
  intro j
  obtain ⟨k, f, g, hfg⟩ := hfactor (Opposite.op j)
  let j' : ℕ+ := k.unop
  have hj' : j ≤ j' := le_of_op_hom g
  have hf : f = opHomOfLE (le_of_op_hom f) := Subsingleton.elim _ _
  have hg : g = opHomOfLE hj' := Subsingleton.elim _ _
  let t : F.obj (Opposite.op j') ⟶ F.obj (Opposite.op j) :=
    F.map (opHomOfLE hj')
  let u : F.obj (Opposite.op j') ⟶ F.obj i :=
    F.map (opHomOfLE (le_of_op_hom f))
  have hfg' : t = u ≫ r ≫ c.π.app (Opposite.op j) := by
    dsimp [t, u, j']
    rw [← hg, hfg, hf]
  have hcone : c.π.app (Opposite.op j') ≫ t = c.π.app (Opposite.op j) := by
    dsimp [t]
    rw [c.w]
  have himage : imageSubobject t =
      imageSubobject (c.π.app (Opposite.op j)) := by
    apply image_eq_of_factor t (c.π.app (Opposite.op j)) (u ≫ r)
      (c.π.app (Opposite.op j'))
    · simpa only [Category.assoc] using hfg'.symm
    · exact hcone
  refine ⟨j', hj', ?_⟩
  intro k' h'
  let t' : F.obj (Opposite.op k') ⟶ F.obj (Opposite.op j) :=
    F.map (opHomOfLE (hj'.trans h'))
  have hcomp : t' = F.map (opHomOfLE h') ≫ t := by
    dsimp [t, t']
    rw [← F.map_comp]
    congr 1
  have hcone' : c.π.app (Opposite.op k') ≫ t' =
      c.π.app (Opposite.op j) := by
    dsimp [t']
    rw [c.w]
  apply le_antisymm
  · rw [himage]
    rw [← hcone']
    exact imageSubobject_comp_le (c.π.app (Opposite.op k')) t'
  · have hcomp' : F.map (opHomOfLE (hj'.trans h')) =
        F.map (opHomOfLE h') ≫ F.map (opHomOfLE hj') := by
      rw [← F.map_comp]
      congr 1
    have hle := imageSubobject_comp_le (F.map (opHomOfLE h')) t
    dsimp [t] at hle
    rw [← hcomp'] at hle
    exact hle

theorem mittagLeffler_iff_of_essentiallyConstant_quotient
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hC : IsEssentiallyConstant S.X₃) :
    IsMittagLeffler S.X₁ ↔ IsMittagLeffler S.X₂ := by
  obtain ⟨i, Z, e, z, hcompat, hzero⟩ :=
    (essentiallyConstant_iff_biproduct_decomposition S.X₃).1 hC
  have hquot : ∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j')
      (h : j ≤ j'),
      transitionMap S.X₃ h ≫ (e j hij).inv ≫ biprod.snd =
        (e j' hij').inv ≫ biprod.snd ≫ z h := by
    intro j j' hij hij' h
    have hh := congrArg (fun q => q ≫ biprod.snd)
      (hcompat hij hij' h)
    apply (cancel_epi (e j' hij').hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, biprod.map_snd] using hh
  have hstable_map : ∀ {j j' : ℕ+} (hij : i ≤ j)
      (hij' : i ≤ j') (h : j ≤ j') (b : S.X₂.obj (Opposite.op j')),
      ((S.g.app (Opposite.op j') ≫ (e j' hij').inv ≫ biprod.snd) b) = 0 →
      (S.g.app (Opposite.op j) ≫ (e j hij).inv ≫ biprod.snd)
        ((S.X₂.map (opHomOfLE h)) b) = 0 := by
    intro j j' hij hij' h b hb
    have hq' : S.X₃.map (opHomOfLE h) ≫ (e j hij).inv ≫ biprod.snd =
        (e j' hij').inv ≫ biprod.snd ≫ z h := by
      simpa [transitionMap] using hquot hij hij' h
    rw [← ConcreteCategory.comp_apply, ← Category.assoc,
      S.g.naturality (opHomOfLE h), Category.assoc,
      ConcreteCategory.comp_apply]
    rw [hq', ConcreteCategory.comp_apply]
    have hb' := hb
    simp only [ConcreteCategory.comp_apply] at hb'
    have hb'' := congrArg (fun q => (z h) q) hb'
    simpa only [ConcreteCategory.comp_apply, map_zero] using hb''
  have hstable_decomp : ∀ {j : ℕ+} (hij : i ≤ j)
      (x : S.X₃.obj (Opposite.op j)),
      ((e j hij).inv ≫ biprod.snd) x = 0 →
      (e j hij).inv x =
        (biprod.inl : inverseSystemLimit S.X₃ ⟶
          inverseSystemLimit S.X₃ ⊞ Z j)
          ((biprod.fst : inverseSystemLimit S.X₃ ⊞ Z j ⟶
            inverseSystemLimit S.X₃) ((e j hij).inv x)) := by
    intro j hij x hx
    let y := (e j hij).inv x
    have ht := congrArg
      (fun q : inverseSystemLimit S.X₃ ⊞ Z j ⟶
          inverseSystemLimit S.X₃ ⊞ Z j => (ConcreteCategory.hom q) y)
      (direct_sum_total (X := inverseSystemLimit S.X₃) (Y := Z j))
    change
      (ConcreteCategory.hom
        (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
          (inverseSystemLimit S.X₃ ⊞ Z j) ⟶
            (inverseSystemLimit S.X₃ ⊞ Z j))) y = y at ht
    change
      (ConcreteCategory.hom
          (biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z j))
          ((ConcreteCategory.hom
            (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z j ⟶
              inverseSystemLimit S.X₃)) y) +
        (ConcreteCategory.hom
          (biprod.inr : Z j ⟶ inverseSystemLimit S.X₃ ⊞ Z j))
          ((ConcreteCategory.hom
            (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z j ⟶ Z j)) y) = y at ht
    have hz : (ConcreteCategory.hom
        (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z j ⟶ Z j)) y = 0 := by
      simpa [y, ConcreteCategory.comp_apply] using hx
    have hfst : (ConcreteCategory.hom
        (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z j ⟶
          inverseSystemLimit S.X₃)) y =
        (ConcreteCategory.hom
          (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z j ⟶
            inverseSystemLimit S.X₃)) ((e j hij).inv x) := by rfl
    rw [← hfst]
    simpa [hz] using ht.symm
  have hinl_map : ∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j')
      (h : j ≤ j') (l : (inverseSystemLimit S.X₃ : AddCommGrpCat)),
      ((e j' hij').hom ≫ transitionMap S.X₃ h)
          ((biprod.inl : (inverseSystemLimit S.X₃ : AddCommGrpCat) ⟶
            (inverseSystemLimit S.X₃ : AddCommGrpCat) ⊞ Z j') l) =
        (e j hij).hom
          ((biprod.inl : (inverseSystemLimit S.X₃ : AddCommGrpCat) ⟶
            (inverseSystemLimit S.X₃ : AddCommGrpCat) ⊞ Z j) l) := by
    intro j j' hij hij' h l
    have heq :
        biprod.inl ≫ (e j' hij').hom ≫ transitionMap S.X₃ h =
          biprod.inl ≫ (e j hij).hom := by
      apply (cancel_mono (e j hij).inv).1
      have hh := congrArg (fun q => biprod.inl ≫ q)
        (hcompat hij hij' h)
      simpa [Category.assoc] using hh
    have heq' := congrArg (fun q => q l) heq
    simpa only [ConcreteCategory.comp_apply] using heq'
  have hquot_g : ∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j')
      (h : j ≤ j'),
      S.X₂.map (opHomOfLE h) ≫ S.g.app (Opposite.op j) ≫
          (e j hij).inv ≫ biprod.snd =
        S.g.app (Opposite.op j') ≫ (e j' hij').inv ≫ biprod.snd ≫ z h := by
    intro j j' hij hij' h
    have hq' : S.X₃.map (opHomOfLE h) ≫ (e j hij).inv ≫ biprod.snd =
        (e j' hij').inv ≫ biprod.snd ≫ z h := by
      simpa [transitionMap] using hquot hij hij' h
    calc
      S.X₂.map (opHomOfLE h) ≫ S.g.app (Opposite.op j) ≫
          (e j hij).inv ≫ biprod.snd =
          S.g.app (Opposite.op j') ≫ S.X₃.map (opHomOfLE h) ≫
            (e j hij).inv ≫ biprod.snd := by
              have hn := congrArg
                (fun q => q ≫ (e j hij).inv ≫ biprod.snd)
                (S.g.naturality (opHomOfLE h))
              simpa [Category.assoc] using hn
      _ = S.g.app (Opposite.op j') ≫ (e j' hij').inv ≫
          biprod.snd ≫ z h := by
            rw [hq']
  have hsurj : ∀ j : ℕ+ᵒᵖ, Function.Surjective (S.g.app j) := by
    intro j
    apply (AddCommGrpCat.epi_iff_surjective _).1
    exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g j
  have hmono : ∀ j : ℕ+ᵒᵖ, Function.Injective (S.f.app j) := by
    intro j
    apply (AddCommGrpCat.mono_iff_injective _).1
    exact (NatTrans.mono_iff_mono_app S.f).1 hS.mono_f j
  have hlocal : ∀ j : ℕ+ᵒᵖ, ∀ x : S.X₂.obj j,
      (S.g.app j) x = 0 →
        ∃ y : S.X₁.obj j, (S.f.app j) y = x := by
    intro j x hx
    have hj := (inverseSystem_exact_iff_pointwise S).1 hS.exact j
    dsimp [Functor.mapShortComplex, evaluation] at hj
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hj x hx
    exact ⟨y, hy⟩
  have hstable_ml_of_A :
      ∀ (hA : IsMittagLeffler S.X₁) (j : ℕ+) (hij : i ≤ j),
        ∃ c : ℕ+, ∃ hjc : j ≤ c, ∃ hic : i ≤ c,
          ∀ k : ℕ+, ∀ hck : c ≤ k,
            ∀ b : S.X₂.obj (Opposite.op c),
              (S.g.app (Opposite.op c) ≫ (e c hic).inv ≫ biprod.snd) b = 0 →
                ∃ y : S.X₂.obj (Opposite.op k),
                  (S.g.app (Opposite.op k) ≫ (e k (hic.trans hck)).inv ≫
                    biprod.snd) y = 0 ∧
                    (S.X₂.map (opHomOfLE hjc)) b =
                      (S.X₂.map (opHomOfLE (hjc.trans hck))) y := by
    intro hA j hij
    have hA' := (isMittagLeffler_iff_underlying S.X₁).1 hA
    obtain ⟨a, f, hf⟩ := hA' (Opposite.op j)
    have hja : j ≤ a.unop := le_of_op_hom f
    have hf' : f = opHomOfLE hja := Subsingleton.elim _ _
    let ha : i ≤ a.unop := hij.trans hja
    refine ⟨a.unop, hja, ha, ?_⟩
    intro k hck b hb
    let l : (inverseSystemLimit S.X₃ : AddCommGrpCat) :=
      (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z a.unop ⟶
        inverseSystemLimit S.X₃)
        ((e a.unop ha).inv ((S.g.app (Opposite.op a.unop)) b))
    have hbdec : (S.g.app (Opposite.op a.unop)) b =
        (e a.unop ha).hom
          ((biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z a.unop) l) := by
      have hh := congrArg (fun q => (e a.unop ha).hom q)
        (hstable_decomp ha (S.g.app (Opposite.op a.unop) b) hb)
      simpa [l] using hh
    obtain ⟨b₀, hb₀⟩ := hsurj (Opposite.op k)
      ((e k (ha.trans hck)).hom
        ((biprod.inl : inverseSystemLimit S.X₃ ⟶
          inverseSystemLimit S.X₃ ⊞ Z k) l))
    have hgc : (S.g.app (Opposite.op a.unop))
          ((S.X₂.map (opHomOfLE hck)) b₀) =
        (S.g.app (Opposite.op a.unop)) b := by
      calc
        (S.g.app (Opposite.op a.unop))
            ((S.X₂.map (opHomOfLE hck)) b₀) =
            (S.X₃.map (opHomOfLE hck)) ((S.g.app (Opposite.op k)) b₀) := by
              rw [← ConcreteCategory.comp_apply, S.g.naturality,
                ConcreteCategory.comp_apply]
        _ = (S.X₃.map (opHomOfLE hck))
            ((e k (ha.trans hck)).hom
              ((biprod.inl : inverseSystemLimit S.X₃ ⟶
                inverseSystemLimit S.X₃ ⊞ Z k) l)) := by rw [hb₀]
        _ = (e a.unop ha).hom
            ((biprod.inl : inverseSystemLimit S.X₃ ⟶
              inverseSystemLimit S.X₃ ⊞ Z a.unop) l) := by
              exact hinl_map ha (ha.trans hck) hck l
        _ = (S.g.app (Opposite.op a.unop)) b := hbdec.symm
    obtain ⟨a_c, ha_c⟩ := hlocal (Opposite.op a.unop)
      (b - (S.X₂.map (opHomOfLE hck)) b₀) (by
        rw [map_sub, hgc, sub_self])
    have harange : Set.range (S.X₁.map (opHomOfLE hja)) ⊆
        Set.range (S.X₁.map (opHomOfLE (hja.trans hck))) := by
      have hh := hf (opHomOfLE (hja.trans hck))
      change Set.range (S.X₁.map f) ⊆
        Set.range (S.X₁.map (opHomOfLE (hja.trans hck))) at hh
      simpa [hf'] using hh
    obtain ⟨a_k, ha_k⟩ := harange ⟨a_c, rfl⟩
    let y := b₀ + (S.f.app (Opposite.op k)) a_k
    have hy : (S.g.app (Opposite.op k) ≫
        (e k (ha.trans hck)).inv ≫ biprod.snd) y = 0 := by
      have hb₀' : (S.g.app (Opposite.op k) ≫
          (e k (ha.trans hck)).inv ≫ biprod.snd) b₀ = 0 := by
        have hq_inl : ((e k (ha.trans hck)).inv ≫ biprod.snd)
            ((e k (ha.trans hck)).hom
              ((biprod.inl : inverseSystemLimit S.X₃ ⟶
                inverseSystemLimit S.X₃ ⊞ Z k) l)) = 0 := by
          have hi : (e k (ha.trans hck)).hom ≫
              (e k (ha.trans hck)).inv ≫ biprod.snd = biprod.snd := by
            simp
          have hi' := congrArg
            (fun q => (ConcreteCategory.hom q)
              ((biprod.inl : inverseSystemLimit S.X₃ ⟶
                inverseSystemLimit S.X₃ ⊞ Z k) l)) hi
          have hi'' :
              (ConcreteCategory.hom
                (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z k ⟶ Z k))
                  ((ConcreteCategory.hom (e k (ha.trans hck)).inv)
                    ((ConcreteCategory.hom (e k (ha.trans hck)).hom)
                      ((ConcreteCategory.hom
                        (biprod.inl : inverseSystemLimit S.X₃ ⟶
                          inverseSystemLimit S.X₃ ⊞ Z k)) l))) =
                (ConcreteCategory.hom
                  (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z k ⟶ Z k))
                  ((ConcreteCategory.hom
                    (biprod.inl : inverseSystemLimit S.X₃ ⟶
                      inverseSystemLimit S.X₃ ⊞ Z k)) l) := by
            simpa only [ConcreteCategory.comp_apply] using hi'
          have hzero :
              (biprod.inl : inverseSystemLimit S.X₃ ⟶
                inverseSystemLimit S.X₃ ⊞ Z k) ≫ biprod.snd = 0 :=
            biprod.inl_snd
          have hzero' := congrArg
            (fun q => (ConcreteCategory.hom q) l) hzero
          have hzero'' :
              (ConcreteCategory.hom
                (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z k ⟶ Z k))
                  ((ConcreteCategory.hom
                    (biprod.inl : inverseSystemLimit S.X₃ ⟶
                      inverseSystemLimit S.X₃ ⊞ Z k)) l) = 0 := by
            change (ConcreteCategory.hom
              (biprod.snd : inverseSystemLimit S.X₃ ⊞ Z k ⟶ Z k))
                ((ConcreteCategory.hom
                  (biprod.inl : inverseSystemLimit S.X₃ ⟶
                    inverseSystemLimit S.X₃ ⊞ Z k)) l) = 0 at hzero'
            exact hzero'
          simpa only [ConcreteCategory.comp_apply] using hi''.trans hzero''
        simpa [ConcreteCategory.comp_apply, hb₀] using hq_inl
      have hf₀' : (S.g.app (Opposite.op k) ≫
          (e k (ha.trans hck)).inv ≫ biprod.snd)
          ((S.f.app (Opposite.op k)) a_k) = 0 := by
        have hz := congrArg (fun q => q.app (Opposite.op k)) S.zero
        simp only [NatTrans.comp_app] at hz
        have hz' := congrArg (fun q => q a_k) hz
        have hfg : (S.g.app (Opposite.op k))
            ((S.f.app (Opposite.op k)) a_k) = 0 := by
          simpa using hz'
        simpa [ConcreteCategory.comp_apply, hfg]
      have hb₀'' := hb₀'
      have hf₀'' := hf₀'
      simp only [ConcreteCategory.comp_apply] at hb₀'' hf₀''
      simp [y, map_add, hb₀'', hf₀'']
    refine ⟨y, hy, ?_⟩
    have hfa : (S.X₂.map (opHomOfLE hja))
          ((S.f.app (Opposite.op a.unop)) a_c) =
        (S.f.app (Opposite.op j))
          ((S.X₁.map (opHomOfLE hja)) a_c) := by
      rw [← ConcreteCategory.comp_apply, ← S.f.naturality,
        ConcreteCategory.comp_apply]
    have hfk : (S.X₂.map (opHomOfLE (hja.trans hck)))
          ((S.f.app (Opposite.op k)) a_k) =
        (S.f.app (Opposite.op j))
          ((S.X₁.map (opHomOfLE hja)) a_c) := by
      rw [← ConcreteCategory.comp_apply, ← S.f.naturality,
        ConcreteCategory.comp_apply, ha_k]
    have hbc : (S.X₂.map (opHomOfLE hja))
          ((S.X₂.map (opHomOfLE hck)) b₀) =
        (S.X₂.map (opHomOfLE (hja.trans hck))) b₀ := by
      rw [← ConcreteCategory.comp_apply, ← S.X₂.map_comp]
      congr 1
    have hdiff : (S.X₂.map (opHomOfLE hja))
          ((S.f.app (Opposite.op a.unop)) a_c) =
        (S.X₂.map (opHomOfLE hja)) b -
          (S.X₂.map (opHomOfLE (hja.trans hck))) b₀ := by
      rw [ha_c, map_sub, hbc]
    rw [map_add, hfk, ← hfa]
    rw [hdiff]
    abel
  have hstable_ml_of_B :
      ∀ (hB : IsMittagLeffler S.X₂) (j : ℕ+) (hij : i ≤ j),
        ∃ c : ℕ+, ∃ hjc : j ≤ c, ∃ hic : i ≤ c,
          ∀ k : ℕ+, ∀ hck : c ≤ k,
            ∀ b : S.X₂.obj (Opposite.op c),
              (S.g.app (Opposite.op c) ≫ (e c hic).inv ≫ biprod.snd) b = 0 →
                ∃ y : S.X₂.obj (Opposite.op k),
                  (S.g.app (Opposite.op k) ≫ (e k (hic.trans hck)).inv ≫
                    biprod.snd) y = 0 ∧
                    (S.X₂.map (opHomOfLE hjc)) b =
                      (S.X₂.map (opHomOfLE (hjc.trans hck))) y := by
    intro hB j hij
    have hB' := (isMittagLeffler_iff_underlying S.X₂).1 hB
    obtain ⟨a, f, hf⟩ := hB' (Opposite.op j)
    have hja : j ≤ a.unop := le_of_op_hom f
    have hf' : f = opHomOfLE hja := Subsingleton.elim _ _
    let ha : i ≤ a.unop := hij.trans hja
    refine ⟨a.unop, hja, ha, ?_⟩
    intro k hck b hb
    obtain ⟨l, hl, hzl⟩ := hzero k
    have hjl : j ≤ l := hja.trans (hck.trans hl)
    obtain ⟨bₗ, hbₗ⟩ := hf (opHomOfLE hjl) ⟨b, rfl⟩
    let y := (S.X₂.map (opHomOfLE hl)) bₗ
    have hy : (S.g.app (Opposite.op k) ≫
        (e k (ha.trans hck)).inv ≫ biprod.snd) y = 0 := by
      have hq := congrArg (fun q => q bₗ)
        (hquot_g (hij := ha.trans hck)
          (hij' := ha.trans (hck.trans hl)) hl)
      have hq' :
          (S.g.app (Opposite.op k) ≫ (e k (ha.trans hck)).inv ≫
            biprod.snd) ((S.X₂.map (opHomOfLE hl)) bₗ) = 0 := by
        simpa [hzl, ConcreteCategory.comp_apply] using hq
      simpa [y] using hq'
    refine ⟨y, hy, ?_⟩
    have hcomp : opHomOfLE (hja.trans (hck.trans hl)) =
        opHomOfLE hl ≫ opHomOfLE hck ≫ opHomOfLE hja := by
      apply Subsingleton.elim
    have hbₗ' := hbₗ
    change (S.X₂.map (opHomOfLE hjl)) bₗ =
      (S.X₂.map f) b at hbₗ'
    rw [hf'] at hbₗ'
    change (S.X₂.map (opHomOfLE hja)) b =
      (S.X₂.map (opHomOfLE (hja.trans hck)))
        ((S.X₂.map (opHomOfLE hl)) bₗ)
    have hmapcomp :
        (S.X₂.map (opHomOfLE (hja.trans hck)))
            ((S.X₂.map (opHomOfLE hl)) bₗ) =
          (S.X₂.map (opHomOfLE hjl)) bₗ := by
      rw [← ConcreteCategory.comp_apply, ← S.X₂.map_comp]
      congr 1
    rw [hmapcomp, hbₗ']
  have hA_to_B : IsMittagLeffler S.X₁ → IsMittagLeffler S.X₂ := by
    intro hA
    apply (isMittagLeffler_iff_underlying S.X₂).2
    intro j₀
    obtain ⟨t, h₀t, hit⟩ := directed_of (· ≤ ·) j₀.unop i
    obtain ⟨c, htc, hic, hc⟩ := hstable_ml_of_A hA t hit
    obtain ⟨d, hcd, hzd⟩ := hzero c
    have hid : i ≤ d := hic.trans hcd
    have hj₀d : j₀.unop ≤ d := h₀t.trans (htc.trans hcd)
    refine ⟨Opposite.op d, opHomOfLE hj₀d, ?_⟩
    intro k g
    have hj₀k : j₀.unop ≤ k.unop := le_of_op_hom g
    have hg : g = opHomOfLE hj₀k := Subsingleton.elim _ _
    rw [hg]
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    obtain ⟨l, hcl, hkl⟩ := directed_of (· ≤ ·) c k.unop
    have htl : t ≤ l := htc.trans hcl
    have hbc :
        (S.g.app (Opposite.op c) ≫ (e c hic).inv ≫ biprod.snd)
          ((S.X₂.map (opHomOfLE hcd)) b) = 0 := by
      have hq := congrArg (fun q => q b)
        (hquot_g (hij := hic) (hij' := hid) hcd)
      simpa [hzd, ConcreteCategory.comp_apply] using hq
    obtain ⟨yₗ, hyₗ, heqₗ⟩ := hc l hcl
      ((S.X₂.map (opHomOfLE hcd)) b) hbc
    let y := (S.X₂.map (opHomOfLE hkl)) yₗ
    have heq₀ :
        (S.X₂.map (opHomOfLE htc))
            ((S.X₂.map (opHomOfLE hcd)) b) =
          (S.X₂.map (opHomOfLE htl)) yₗ := by
      rw [heqₗ]
    have heq₁ :
        (S.X₂.map (opHomOfLE h₀t))
            ((S.X₂.map (opHomOfLE htc))
              ((S.X₂.map (opHomOfLE hcd)) b)) =
          (S.X₂.map (opHomOfLE h₀t))
            ((S.X₂.map (opHomOfLE htl)) yₗ) := by
      exact congrArg (fun q => (S.X₂.map (opHomOfLE h₀t)) q) heq₀
    have heq₂ :
        (S.X₂.map (opHomOfLE hj₀d)) b =
          (S.X₂.map (opHomOfLE h₀t))
            ((S.X₂.map (opHomOfLE htc))
              ((S.X₂.map (opHomOfLE hcd)) b)) := by
      calc
        (S.X₂.map (opHomOfLE hj₀d)) b =
            (S.X₂.map (opHomOfLE (h₀t.trans (htc.trans hcd)))) b := by
              congr 1
        _ = (S.X₂.map (opHomOfLE h₀t))
            ((S.X₂.map (opHomOfLE htc))
              ((S.X₂.map (opHomOfLE hcd)) b)) := by
              rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
                ← S.X₂.map_comp, ← S.X₂.map_comp]
              congr 1
    have heq₃ :
        (S.X₂.map (opHomOfLE h₀t))
            ((S.X₂.map (opHomOfLE htl)) yₗ) =
          (S.X₂.map (opHomOfLE hj₀k)) y := by
      calc
        (S.X₂.map (opHomOfLE h₀t))
              ((S.X₂.map (opHomOfLE htl)) yₗ) =
            (S.X₂.map (opHomOfLE (h₀t.trans htl))) yₗ := by
              rw [← ConcreteCategory.comp_apply, ← S.X₂.map_comp]
              congr 1
        _ = (S.X₂.map (opHomOfLE hj₀k))
            ((S.X₂.map (opHomOfLE hkl)) yₗ) := by
              rw [← ConcreteCategory.comp_apply, ← S.X₂.map_comp]
              congr 1
    refine ⟨y, ?_⟩
    change (S.X₂.map (opHomOfLE hj₀k)) y =
      (S.X₂.map (opHomOfLE hj₀d)) b
    exact (heq₂.trans (heq₁.trans heq₃)).symm
  have hstable_zero_of_map :
      ∀ {t l : ℕ+} (hit : i ≤ t) (htl : t ≤ l)
        (b : S.X₂.obj (Opposite.op l)),
        (S.g.app (Opposite.op l) ≫ (e l (hit.trans htl)).inv ≫ biprod.snd) b = 0 →
        (S.X₃.map (opHomOfLE htl)) ((S.g.app (Opposite.op l)) b) = 0 →
        (S.g.app (Opposite.op l)) b = 0 := by
    intro t l hit htl b hb hmap
    let q : (inverseSystemLimit S.X₃ : AddCommGrpCat) :=
      (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z l ⟶
        inverseSystemLimit S.X₃)
        ((e l (hit.trans htl)).inv ((S.g.app (Opposite.op l)) b))
    have hbdec : (S.g.app (Opposite.op l)) b =
        (e l (hit.trans htl)).hom
          ((biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z l) q) := by
      have hh := congrArg (fun x => (e l (hit.trans htl)).hom x)
        (hstable_decomp (hit.trans htl) (S.g.app (Opposite.op l) b) hb)
      simpa [q] using hh
    have hCeq : (S.X₃.map (opHomOfLE htl))
          ((S.g.app (Opposite.op l)) b) =
        (e t hit).hom
          ((biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z t) q) := by
      rw [hbdec]
      exact hinl_map hit (hit.trans htl) htl q
    have hqzero : (e t hit).hom
          ((biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z t) q) = 0 := by
      rw [← hCeq]
      exact hmap
    have hqzero' := congrArg
      (fun x => (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z t ⟶
        inverseSystemLimit S.X₃) ((e t hit).inv x)) hqzero
    have hqzero'' :
        (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z t ⟶
          inverseSystemLimit S.X₃)
            ((biprod.inl : inverseSystemLimit S.X₃ ⟶
              inverseSystemLimit S.X₃ ⊞ Z t) q) = 0 := by
      have hinv :
          (e t hit).inv
              ((e t hit).hom
                ((biprod.inl : inverseSystemLimit S.X₃ ⟶
                  inverseSystemLimit S.X₃ ⊞ Z t) q)) =
            (biprod.inl : inverseSystemLimit S.X₃ ⟶
              inverseSystemLimit S.X₃ ⊞ Z t) q := by
        have hh := congrArg
          (fun f => (ConcreteCategory.hom f)
            ((biprod.inl : inverseSystemLimit S.X₃ ⟶
              inverseSystemLimit S.X₃ ⊞ Z t) q))
          (e t hit).hom_inv_id
        simpa [ConcreteCategory.comp_apply] using hh
      have hinv0 : (e t hit).inv (0 : S.X₃.obj (Opposite.op t)) = 0 := by
        simpa only [map_zero]
      rw [hinv, hinv0] at hqzero'
      simpa only [map_zero] using hqzero'
    have hq : q = 0 := by
      have hfi :
          (biprod.inl : inverseSystemLimit S.X₃ ⟶
            inverseSystemLimit S.X₃ ⊞ Z t) ≫
              (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z t ⟶
                inverseSystemLimit S.X₃) =
            𝟙 (inverseSystemLimit S.X₃) := by simp
      have hfi' := congrArg
        (fun f => (ConcreteCategory.hom f)
          q) hfi
      have hfi'' :
          (biprod.fst : inverseSystemLimit S.X₃ ⊞ Z t ⟶
            inverseSystemLimit S.X₃)
              ((biprod.inl : inverseSystemLimit S.X₃ ⟶
                inverseSystemLimit S.X₃ ⊞ Z t) q) = q := by
        simpa only [ConcreteCategory.comp_apply,
          CategoryTheory.ConcreteCategory.id_apply] using hfi'
      exact hfi''.symm.trans hqzero''
    rw [hbdec, hq]
    simp
  have hB_to_A : IsMittagLeffler S.X₂ → IsMittagLeffler S.X₁ := by
    intro hB
    apply (isMittagLeffler_iff_underlying S.X₁).2
    intro j₀
    obtain ⟨t, h₀t, hit⟩ := directed_of (· ≤ ·) j₀.unop i
    obtain ⟨c, htc, hic, hc⟩ := hstable_ml_of_B hB t hit
    have hj₀c : j₀.unop ≤ c := h₀t.trans htc
    refine ⟨Opposite.op c, opHomOfLE hj₀c, ?_⟩
    intro k g
    have hj₀k : j₀.unop ≤ k.unop := le_of_op_hom g
    have hg : g = opHomOfLE hj₀k := Subsingleton.elim _ _
    rw [hg]
    intro x hx
    obtain ⟨a_c, rfl⟩ := hx
    obtain ⟨l, hcl, hkl⟩ := directed_of (· ≤ ·) c k.unop
    have htl : t ≤ l := htc.trans hcl
    have hfg : (S.g.app (Opposite.op c))
        ((S.f.app (Opposite.op c)) a_c) = 0 := by
      have hz := congrArg (fun q => q.app (Opposite.op c)) S.zero
      simp only [NatTrans.comp_app] at hz
      have hz' := congrArg (fun q => q a_c) hz
      simpa using hz'
    have hstable_c :
        (S.g.app (Opposite.op c) ≫ (e c hic).inv ≫ biprod.snd)
          ((S.f.app (Opposite.op c)) a_c) = 0 := by
      have hz := congrArg (fun q => q.app (Opposite.op c)) S.zero
      simp only [NatTrans.comp_app] at hz
      have hz' := congrArg (fun q => q a_c) hz
      simpa [ConcreteCategory.comp_apply, hfg]
    obtain ⟨yₗ, hyₗ, heqₗ⟩ := hc l hcl
      ((S.f.app (Opposite.op c)) a_c) hstable_c
    have hmapzero :
        (S.X₃.map (opHomOfLE htl))
            ((S.g.app (Opposite.op l)) yₗ) = 0 := by
      calc
        (S.X₃.map (opHomOfLE htl))
              ((S.g.app (Opposite.op l)) yₗ) =
            (S.g.app (Opposite.op t))
              ((S.X₂.map (opHomOfLE htl)) yₗ) := by
                rw [← ConcreteCategory.comp_apply, ← S.g.naturality,
                  ConcreteCategory.comp_apply]
        _ = (S.g.app (Opposite.op t))
              ((S.X₂.map (opHomOfLE htc))
                ((S.f.app (Opposite.op c)) a_c)) := by
                rw [heqₗ.symm]
        _ = (S.X₃.map (opHomOfLE htc))
              ((S.g.app (Opposite.op c))
                ((S.f.app (Opposite.op c)) a_c)) := by
                rw [← ConcreteCategory.comp_apply, S.g.naturality,
                  ConcreteCategory.comp_apply]
        _ = 0 := by rw [hfg]; simp
    have hzero_l := hstable_zero_of_map hit htl yₗ hyₗ hmapzero
    obtain ⟨aₗ, haₗ⟩ := hlocal (Opposite.op l) yₗ hzero_l
    have hfa :
        (S.X₂.map (opHomOfLE htc)) ((S.f.app (Opposite.op c)) a_c) =
          (S.f.app (Opposite.op t))
            ((S.X₁.map (opHomOfLE htc)) a_c) := by
      rw [← ConcreteCategory.comp_apply, ← S.f.naturality,
        ConcreteCategory.comp_apply]
    have hfl :
        (S.X₂.map (opHomOfLE htl)) yₗ =
          (S.f.app (Opposite.op t))
            ((S.X₁.map (opHomOfLE htl)) aₗ) := by
      rw [← haₗ, ← ConcreteCategory.comp_apply, ← S.f.naturality,
        ConcreteCategory.comp_apply]
    have hat :
        (S.X₁.map (opHomOfLE htc)) a_c =
          (S.X₁.map (opHomOfLE htl)) aₗ := by
      apply hmono (Opposite.op t)
      rw [← hfa, heqₗ, hfl]
    let a_k := (S.X₁.map (opHomOfLE hkl)) aₗ
    refine ⟨a_k, ?_⟩
    have heq₀ :
        (S.X₁.map (opHomOfLE h₀t))
            ((S.X₁.map (opHomOfLE htc)) a_c) =
          (S.X₁.map (opHomOfLE h₀t))
            ((S.X₁.map (opHomOfLE htl)) aₗ) :=
      congrArg (fun q => (S.X₁.map (opHomOfLE h₀t)) q) hat
    have heq₁ :
        (S.X₁.map (opHomOfLE hj₀c)) a_c =
          (S.X₁.map (opHomOfLE h₀t))
            ((S.X₁.map (opHomOfLE htc)) a_c) := by
      rw [← ConcreteCategory.comp_apply, ← S.X₁.map_comp]
      congr 1
    have heq₂ :
        (S.X₁.map (opHomOfLE h₀t))
            ((S.X₁.map (opHomOfLE htl)) aₗ) =
          (S.X₁.map (opHomOfLE hj₀k)) a_k := by
      calc
        (S.X₁.map (opHomOfLE h₀t))
              ((S.X₁.map (opHomOfLE htl)) aₗ) =
            (S.X₁.map (opHomOfLE (h₀t.trans htl))) aₗ := by
              rw [← ConcreteCategory.comp_apply, ← S.X₁.map_comp]
              congr 1
        _ = (S.X₁.map (opHomOfLE hj₀k)) a_k := by
              rw [← ConcreteCategory.comp_apply, ← S.X₁.map_comp]
              congr 1
    change (S.X₁.map (opHomOfLE hj₀k)) a_k =
      (S.X₁.map (opHomOfLE hj₀c)) a_c
    exact (heq₁.trans (heq₀.trans heq₂)).symm
  constructor
  · exact hA_to_B
  · exact hB_to_A

/-! ## Cohomology of inverse systems of complexes -/

abbrev InverseSystemOfCochainComplexes :=
  NatInverseSystem (CochainComplex AddCommGrpCat ℤ)

abbrev inverseSystemComplexComponent
    (K : InverseSystemOfCochainComplexes) (n : ℤ) :
    NatInverseSystem AddCommGrpCat :=
  K ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n

abbrev inverseSystemCohomologySystem
    (K : InverseSystemOfCochainComplexes) (n : ℤ) :
    NatInverseSystem AddCommGrpCat :=
  K ⋙ Formalization.Books.Homology.Unit13.cochainCohomologyFunctor
    AddCommGrpCat n

theorem inverseSystem_cohomology_zero_iso_limit
    (K : InverseSystemOfCochainComplexes)
    (hA₂ : IsMittagLeffler (inverseSystemComplexComponent K (-2)))
    (hA₁ : IsMittagLeffler (inverseSystemComplexComponent K (-1)))
    (hH₁ : IsEssentiallyConstant (inverseSystemCohomologySystem K (-1))) :
    Nonempty
      ((inverseSystemLimit K).homology 0 ≅
        inverseSystemLimit (inverseSystemCohomologySystem K 0)) := by
  let A : ℤ → NatInverseSystem AddCommGrpCat :=
    fun n => inverseSystemComplexComponent K n
  let Z : ℤ → NatInverseSystem AddCommGrpCat :=
    fun n => K ⋙ HomologicalComplex.cyclesFunctor
      AddCommGrpCat (ComplexShape.up ℤ) n
  let H : ℤ → NatInverseSystem AddCommGrpCat :=
    fun n => inverseSystemCohomologySystem K n
  let d : ∀ n : ℤ, A (n - 1) ⟶ A n := fun n =>
    { app := fun i => (K.obj i).d (n - 1) n
      naturality := by
        intro i j f
        exact (K.map f).comm' (n - 1) n (by
          simp [ComplexShape.up, ComplexShape.up']) }
  let dNext : ∀ n : ℤ, A n ⟶ A (n + 1) := fun n =>
    { app := fun i => (K.obj i).d n (n + 1)
      naturality := by
        intro i j f
        exact (K.map f).comm' n (n + 1) (by
          simp [ComplexShape.up, ComplexShape.up']) }
  let q : ∀ n : ℤ, A (n - 1) ⟶ Z n := fun n =>
    { app := fun i => (K.obj i).toCycles (n - 1) n
      naturality := by
        intro i j f
        apply (cancel_mono ((K.obj j).iCycles n)).1
        dsimp [A, Z]
        change
          ((K.map f).f (n - 1) ≫
              (K.obj j).toCycles (n - 1) n) ≫
              (K.obj j).iCycles n =
            ((K.obj i).toCycles (n - 1) n ≫
              HomologicalComplex.cyclesMap (K.map f) n) ≫
              (K.obj j).iCycles n
        simp only [Category.assoc, HomologicalComplex.toCycles_i,
          HomologicalComplex.cyclesMap_i]
        rw [← Category.assoc, HomologicalComplex.toCycles_i]
        exact (K.map f).comm' (n - 1) n (by
          simp [ComplexShape.up, ComplexShape.up']) }
  let ι : ∀ n : ℤ, Z n ⟶ A n := fun n =>
    { app := fun i => (K.obj i).iCycles n
      naturality := by
        intro i j f
        dsimp [A, Z]
        exact HomologicalComplex.cyclesMap_i (K.map f) n }
  let π : ∀ n : ℤ, Z n ⟶ H n := fun n =>
    { app := fun i => (K.obj i).homologyπ n
      naturality := by
        intro i j f
        dsimp [Z, H]
        change
          HomologicalComplex.cyclesMap (K.map f) n ≫
              (K.obj j).homologyπ n =
            (K.obj i).homologyπ n ≫
              HomologicalComplex.homologyMap (K.map f) n
        exact (HomologicalComplex.homologyπ_naturality (K.map f) n).symm }
  have hqι (n : ℤ) : q n ≫ ι n = d n := by
    apply NatTrans.ext
    funext i
    dsimp [q, ι, d]
    exact HomologicalComplex.toCycles_i (K.obj i) (n - 1) n
  have hιd (n : ℤ) : ι n ≫ dNext n = 0 := by
    apply NatTrans.ext
    funext i
    dsimp [ι, dNext]
    exact (HomologicalComplex.iCycles_d (K.obj i) n (n + 1))
  have hqπ (n : ℤ) : q n ≫ π n = 0 := by
    apply NatTrans.ext
    funext i
    dsimp [q, π, Z, H]
    exact
      (HomologicalComplex.toCycles_comp_homologyπ (K.obj i) (n - 1) n)
  have hιd' (n : ℤ) : ι (n - 1) ≫ d n = 0 := by
    apply NatTrans.ext
    funext i
    dsimp [ι, d]
    exact HomologicalComplex.iCycles_d (K.obj i) (n - 1) n
  let I : ℤ → NatInverseSystem AddCommGrpCat := fun n => image (d n)
  let eI : ∀ n : ℤ, A (n - 1) ⟶ I n := fun n => factorThruImage (d n)
  let mI : ∀ n : ℤ, I n ⟶ A n := fun n => image.ι (d n)
  have hιMono (n : ℤ) : Mono (ι n) := by
    rw [NatTrans.mono_iff_mono_app]
    intro i
    dsimp [ι]
    exact Fork.IsLimit.mono (HomologicalComplex.cyclesIsKernel (K.obj i) n (n + 1)
      ((ComplexShape.up ℤ).next_eq'
        (by simp [ComplexShape.up, ComplexShape.up'])))
  letI : ∀ n : ℤ, Mono (ι n) := hιMono
  let rI : ∀ n : ℤ, I n ⟶ Z n := fun n =>
    image.lift
      { I := Z n
        m := ι n
        e := q n
        fac := hqι n }
  have heIr (n : ℤ) : eI n ≫ rI n = q n := by
    simpa [eI, rI] using
      (image.fac_lift (f := d n)
        ({ I := Z n, m := ι n, e := q n, fac := hqι n } : MonoFactorisation (d n)))
  have hrIm (n : ℤ) : rI n ≫ ι n = mI n := by
    simpa [rI, mI] using
      (image.lift_fac (f := d n)
        ({ I := Z n, m := ι n, e := q n, fac := hqι n } : MonoFactorisation (d n)))
  have heIm (n : ℤ) : eI n ≫ mI n = d n := by
    exact image.fac _
  let SIZ (n : ℤ) : ShortComplex (NatInverseSystem AddCommGrpCat) :=
    ShortComplex.mk (rI n) (π n) (by
      apply (cancel_epi (eI n)).1
      rw [← Category.assoc, heIr n, hqπ n, comp_zero])
  let SZI (n : ℤ) : ShortComplex (NatInverseSystem AddCommGrpCat) :=
    ShortComplex.mk (ι (n - 1)) (eI n) (by
      apply (cancel_mono (mI n)).1
      rw [Category.assoc, heIm n, hιd' n, zero_comp])
  have hSIZ (n : ℤ) : (SIZ n).Exact := by
    rw [inverseSystem_exact_iff_pointwise]
    intro i
    let T₁ : ShortComplex AddCommGrpCat :=
      ShortComplex.mk ((q n).app i) ((π n).app i) (by
        simpa only [NatTrans.comp_app, zero_app] using
          congrArg (fun x => x.app i) (hqπ n))
    let T₂ : ShortComplex AddCommGrpCat :=
      ShortComplex.mk ((rI n).app i) ((π n).app i) (by
        simpa only [NatTrans.comp_app, zero_app] using
          congrArg (fun x => x.app i) (SIZ n).zero)
    have hT₁ : T₁.Exact := by
      apply ShortComplex.exact_of_g_is_cokernel
      exact cochainCohomologyIsCokernel (K.obj i) n
    let φ : T₁ ⟶ T₂ :=
      { τ₁ := (eI n).app i
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          dsimp [T₁, T₂]
          change (eI n).app i ≫ (rI n).app i = (q n).app i
          simpa only [NatTrans.comp_app] using
            congrArg (fun x => x.app i) (heIr n)
        comm₂₃ := by
          dsimp [T₁, T₂]
          simp }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hT₁
  have hSZI (n : ℤ) : (SZI n).Exact := by
    rw [inverseSystem_exact_iff_pointwise]
    intro i
    letI : Mono ((ι (n - 1)).app i) := by
      dsimp [ι]
      exact Fork.IsLimit.mono (HomologicalComplex.cyclesIsKernel (K.obj i) (n - 1) n
        ((ComplexShape.up ℤ).next_eq'
          (by simp [ComplexShape.up, ComplexShape.up'])))
    let hcyc := (K.obj i).cyclesIsKernel (n - 1) n (by
      exact (ComplexShape.up ℤ).next_eq'
        (by simp [ComplexShape.up, ComplexShape.up']))
    have hzker : (ι (n - 1)).app i ≫ (eI n).app i = 0 := by
      apply (cancel_mono ((mI n).app i)).1
      have he := congrArg (fun x => x.app i) (heIm n)
      have hd := congrArg (fun x => x.app i) (hιd' n)
      simp only [NatTrans.comp_app, zero_app] at he hd ⊢
      rw [Category.assoc, he, hd, zero_comp]
    have hker : IsLimit (KernelFork.ofι ((ι (n - 1)).app i)
        hzker) := by
      let lift : ∀ {W : AddCommGrpCat} (g : W ⟶ (A (n - 1)).obj i),
          ((g ≫ (eI n).app i = 0) → (W ⟶ (Z (n - 1)).obj i)) :=
        fun {W} g (hg : g ≫ (eI n).app i = 0) => by
          have hem : (eI n).app i ≫ (mI n).app i = (d n).app i := by
            simpa only [NatTrans.comp_app] using
              congrArg (fun x => x.app i) (heIm n)
          have hs : g ≫ (d n).app i = 0 := by
            rw [← hem, ← Category.assoc, hg, zero_comp]
          change W ⟶ (Z (n - 1)).obj i
          exact hcyc.lift (KernelFork.ofι g hs)
      have hfac : ∀ {W : AddCommGrpCat} (g : W ⟶ (A (n - 1)).obj i),
          ∀ hg : (g ≫ (eI n).app i = 0),
            ((lift g hg) ≫ (ι (n - 1)).app i = g) := by
        intro W g hg
        have hem : (eI n).app i ≫ (mI n).app i = (d n).app i := by
          simpa only [NatTrans.comp_app] using
            congrArg (fun x => x.app i) (heIm n)
        have hs : g ≫ (d n).app i = 0 := by
          rw [← hem, ← Category.assoc, hg, zero_comp]
        dsimp [lift]
        change hcyc.lift (KernelFork.ofι g hs) ≫
          (ι (n - 1)).app i = g
        exact Fork.IsLimit.lift_ι hcyc
      refine KernelFork.IsLimit.ofι ((ι (n - 1)).app i) hzker
        lift hfac ?_
      intro W g hg m hm
      apply (cancel_mono ((ι (n - 1)).app i)).1
      calc
        m ≫ (ι (n - 1)).app i = g := hm
        _ = (lift g hg) ≫ (ι (n - 1)).app i := (hfac g hg).symm
    change (ShortComplex.mk ((ι (n - 1)).app i) ((eI n).app i) _).Exact
    exact ShortComplex.exact_of_f_is_kernel _ hker
  have hSZI_short (n : ℤ) : (SZI n).ShortExact := by
    refine { exact := hSZI n, mono_f := ?_, epi_g := ?_ }
    · dsimp [SZI]
      exact hιMono (n - 1)
    · dsimp [SZI]
      infer_instance
  have hrMono (n : ℤ) : Mono (rI n) := by
    apply mono_of_mono_fac (hrIm n)
  have hSIZ_short (n : ℤ) : (SIZ n).ShortExact := by
    refine { exact := hSIZ n, mono_f := hrMono n, epi_g := ?_ }
    dsimp [SIZ]
    rw [NatTrans.epi_iff_epi_app]
    intro i
    dsimp [π]
    exact epi_of_isColimit_cofork (cochainCohomologyIsCokernel (K.obj i) n)
  have hIminus : IsMittagLeffler (I (-1)) :=
    inverseSystemLimit_mittagLeffler_quotient (SZI (-1))
      (hSZI_short (-1)) hA₂
  have hZminus : IsMittagLeffler (Z (-1)) :=
    (mittagLeffler_iff_of_essentiallyConstant_quotient (SIZ (-1))
      (hSIZ_short (-1)) hH₁).1 hIminus
  have hI₀ : IsMittagLeffler (I 0) :=
    inverseSystemLimit_mittagLeffler_quotient (SZI 0) (hSZI_short 0) hA₁
  let hI : IsDirectedSet ℕ+ := ⟨inferInstance, inferInstance⟩
  have hSZI₀' :
      Formalization.Books.Algebra.Unit86.IsPointwiseShortExact (SZI 0) := by
    intro i
    have hi := (inverseSystem_exact_iff_pointwise (SZI 0)).1
      (hSZI_short 0).exact i
    refine { exact := hi, mono_f := ?_, epi_g := ?_ }
    · exact (NatTrans.mono_iff_mono_app (SZI 0).f).1
        (hSZI_short 0).mono_f i
    · exact (NatTrans.epi_iff_epi_app (SZI 0).g).1
        (hSZI_short 0).epi_g i
  have hlimZI :=
    Formalization.Books.Algebra.Unit86.inverse_limit_shortExact_of_countable_mittagLeffler
      hI (SZI 0) hSZI₀'
      ((isMittagLeffler_iff_underlying (SZI 0).X₁).1 hZminus)
  letI : Epi (inverseSystemLimitMap (eI 0)) := by
    change Epi (limMap (SZI 0).g)
    exact hlimZI.epi_g
  have hSIZ₀' :
      Formalization.Books.Algebra.Unit86.IsPointwiseShortExact (SIZ 0) := by
    intro i
    have hi := (inverseSystem_exact_iff_pointwise (SIZ 0)).1
      (hSIZ_short 0).exact i
    refine { exact := hi, mono_f := ?_, epi_g := ?_ }
    · exact (NatTrans.mono_iff_mono_app (SIZ 0).f).1
        (hSIZ_short 0).mono_f i
    · exact (NatTrans.epi_iff_epi_app (SIZ 0).g).1
        (hSIZ_short 0).epi_g i
  have hlimIZ :=
    Formalization.Books.Algebra.Unit86.inverse_limit_shortExact_of_countable_mittagLeffler
      hI (SIZ 0) hSIZ₀'
      ((isMittagLeffler_iff_underlying (SIZ 0).X₁).1 hI₀)
  letI : Epi (inverseSystemLimitMap (π 0)) := by
    change Epi (limMap (SIZ 0).g)
    exact hlimIZ.epi_g
  have hzeroML : IsMittagLeffler (0 : NatInverseSystem AddCommGrpCat) := by
    apply (isMittagLeffler_iff_underlying _).2
    apply Functor.isMittagLeffler_of_surjective
    intro i j f
    intro y
    refine ⟨0, ?_⟩
    change PUnit.unit = y
    cases y
    rfl
  let C₀ : ComposableArrows (NatInverseSystem AddCommGrpCat) 3 :=
    ComposableArrows.mk₃ (0 : (0 : NatInverseSystem AddCommGrpCat) ⟶ I 0)
      (rI 0) (π 0)
  have hC₀ : C₀.Exact := by
    refine { toIsComplex := { zero := ?_ }, exact := ?_ }
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · change (0 : (0 : NatInverseSystem AddCommGrpCat) ⟶ I 0) ≫ (rI 0) = 0
        simp
      · change (rI 0) ≫ (π 0) = 0
        exact (SIZ 0).zero
    · intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · change (ShortComplex.mk (0 : (0 : NatInverseSystem AddCommGrpCat) ⟶ I 0)
          (rI 0) (by simp)).Exact
        exact (ShortComplex.exact_iff_mono _ (by simp)).2 (hrMono 0)
      · exact hSIZ 0
  have hlimC₀ := inverseSystemLimit_exact_of_exact_of_mittagLeffler
    C₀ hC₀ hzeroML
  have hlim_eIr : inverseSystemLimitMap (eI 0) ≫
      inverseSystemLimitMap (rI 0) = inverseSystemLimitMap (q 0) := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, inverseSystemLimitMap, limMap_π]
    rw [← Category.assoc, limMap_π (eI 0) i, Category.assoc,
      ← NatTrans.comp_app, heIr 0]
  have hlimqπ : inverseSystemLimitMap (q 0) ≫
      inverseSystemLimitMap (π 0) = 0 := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, inverseSystemLimitMap, limMap_π]
    rw [← Category.assoc, limMap_π (q 0) i, Category.assoc,
      ← NatTrans.comp_app]
    rw [congrArg (fun x => x.app i) (hqπ 0)]
    simp
  let T₀ : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (inverseSystemLimitMap (rI 0))
      (inverseSystemLimitMap (π 0)) (by
        apply limit.hom_ext
        intro i
        simp only [Category.assoc, inverseSystemLimitMap, limMap_π]
        rw [← Category.assoc, limMap_π (rI 0) i, Category.assoc,
          ← NatTrans.comp_app]
        rw [congrArg (fun x => x.app i) (SIZ 0).zero]
        simp)
  have hT₀ : T₀.Exact := by
    have h := hlimC₀.exact' 0 1 2 (by omega) (by omega) (by omega)
    dsimp [C₀] at h
    convert h using 1 <;> congr 1 <;> simp [T₀, C₀]
  let Tq : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (inverseSystemLimitMap (q 0))
      (inverseSystemLimitMap (π 0)) hlimqπ
  let φ : Tq ⟶ T₀ :=
    { τ₁ := inverseSystemLimitMap (eI 0)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [Tq, T₀]
        simpa only [Category.comp_id] using hlim_eIr
      comm₂₃ := by simp [Tq, T₀] }
  have hTq : Tq.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT₀
  sorry

/-! ## Inverse systems over ordinals -/

abbrev OrdinalInverseSystemOfCochainComplexes (α : Ordinal) :=
  InverseSystem (Set.Iio α) (CochainComplex AddCommGrpCat ℤ)

/- The inclusion of the stages below `β` into the stages below `α`. -/
def ordinalIioEmbedding {α : Ordinal} (β : Set.Iio α) :
    Set.Iio β.1 →o Set.Iio α :=
  { toFun := fun γ =>
      ⟨γ.1, lt_trans (show γ.1 < β.1 from γ.2) (show β.1 < α from β.2)⟩
    monotone' := fun _ _ h => h }

def ordinalIioInclusion {α : Ordinal} (β : Set.Iio α) :
    Set.Iio β.1 ⥤ Set.Iio α :=
  (ordinalIioEmbedding β).monotone.functor

/- The restriction of the ordinal-indexed system to the stages below `β`. -/
abbrev ordinalPrefixSystem {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α) (β : Set.Iio α) :
    InverseSystem (Set.Iio β.1) (CochainComplex AddCommGrpCat ℤ) :=
  (ordinalIioInclusion β).op ⋙ K

abbrev ordinalPrefixComponent {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α) (β : Set.Iio α) (n : ℤ) :
    InverseSystem (Set.Iio β.1) AddCommGrpCat :=
  ordinalPrefixSystem K β ⋙
    HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n

/- The canonical map from the `β`-th component to the limit of all earlier
components. -/
def ordinalPrefixIndexMap {α : Ordinal}
    (β : Set.Iio α) (γ : (Set.Iio β.1)ᵒᵖ) :
    Opposite.op β ⟶
      Opposite.op ((ordinalIioInclusion β).obj γ.unop) :=
  let hγ : (ordinalIioEmbedding β) γ.unop < β := by
    exact γ.unop.property
  (homOfLE hγ.le).op

noncomputable def ordinalPrefixCone {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α)
    (β : Set.Iio α) (n : ℤ) :
    Cone (ordinalPrefixComponent K β n) where
  pt := (K.obj (Opposite.op β)).X n
  π :=
    { app := fun γ => (K.map (ordinalPrefixIndexMap β γ)).f n
      naturality := by
        intro γ γ' f
        change
          (K.map (ordinalPrefixIndexMap β γ')).f n =
            (K.map (ordinalPrefixIndexMap β γ)).f n ≫
              (K.map ((ordinalIioInclusion β).op.map f)).f n
        rw [← HomologicalComplex.comp_f, ← K.map_comp]
        congr 1 }

noncomputable def ordinalPrefixMap {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α)
    (β : Set.Iio α) (n : ℤ) :
    (K.obj (Opposite.op β)).X n ⟶
      inverseSystemLimit (ordinalPrefixComponent K β n) :=
  limit.lift (ordinalPrefixComponent K β n) (ordinalPrefixCone K β n)

theorem acyclic_limit_of_ordinal_inverse_system
    (α : Ordinal) (K : OrdinalInverseSystemOfCochainComplexes α)
    (hacyclic : ∀ β : Set.Iio α, (K.obj (Opposite.op β)).Acyclic)
    (hsurjective : ∀ (β : Set.Iio α) (n : ℤ),
      Function.Surjective (ordinalPrefixMap K β n)) :
    (inverseSystemLimit K).Acyclic := by
  sorry

/- The source's proof-only constructions of the systems of cycles and images
are already represented by the canonical kernel/image and homology APIs used
in the cohomology theorem above; they need no additional public declarations.
The warning that ML need not suffice in arbitrary AB4* abelian categories is
recorded by the hypotheses of the exactness declarations, which specialize
the positive result to abelian groups as in the source. -/

end Formalization.Books.Homology.Unit31
