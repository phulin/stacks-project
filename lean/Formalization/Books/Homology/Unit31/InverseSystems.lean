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
          e.hom ≫ q = biprod.fst ∧ biprod.inl ≫ e.hom = j := by
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
    refine ⟨Iso.mk eh ei hhi hih, ?_, ?_⟩
    · dsimp [eh]
      apply biprod.hom_ext'
      · simp only [Category.assoc, biprod.inl_desc, h, biprod.inl_fst]
      · simp only [Category.assoc, biprod.inr_desc, hjq, biprod.inr_fst]
    · change biprod.inl ≫ eh = j
      simp [eh]
  constructor
  · sorry
  · sorry

theorem essentiallyConstant_isMittagLeffler
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C)
    (hF : IsEssentiallyConstant F) :
    IsMittagLeffler F := by
  sorry

theorem mittagLeffler_iff_of_essentiallyConstant_quotient
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hC : IsEssentiallyConstant S.X₃) :
    IsMittagLeffler S.X₁ ↔ IsMittagLeffler S.X₂ := by
  sorry

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
