import Formalization.Books.Categories.Unit40.RepresentableCategoriesFibredInGroupoids
import Formalization.Books.Categories.Unit41.TwoYonedaLemma
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Categories, Chapter 42: Representable 1-morphisms

The source studies representability of a morphism between categories fibred in
groupoids by pulling it back along every slice of the base.  Units 33--41
already provide the universe-polymorphic fibred-morphism, vertical iso-comma,
2-Yoneda, and representability interfaces used below.
-/

namespace Formalization.Books.Categories.Unit42

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit34
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit39
open Formalization.Books.Categories.Unit40
open Formalization.Books.Categories.Unit41

noncomputable section

/-! ## The 2-fibre product over a slice -/

/- `VerticalIsoComma` is the existing explicit category-valued construction
   of a 2-fibre product over a base.  The first factor below is the slice and
   the second factor is the source of `F`. -/
abbrev SlicePullbackCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :=
  VerticalIsoComma G.functor F.functor
    (Over.forget U) p q G.over F.over

def slicePullbackBase
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ C :=
  verticalIsoCommaBase G.functor F.functor
    (Over.forget U) p q G.over F.over

def slicePullbackLeft
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ Over U :=
  (VerticalIsoCommaProperty G.functor F.functor
    (Over.forget U) p q G.over F.over).ι ⋙
      isoCommaLeft G.functor F.functor

def slicePullbackRight
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ X :=
  (VerticalIsoCommaProperty G.functor F.functor
    (Over.forget U) p q G.over F.over).ι ⋙
      isoCommaRight G.functor F.functor

private lemma sliceStronglyCartesian_map
    {A C : Type*} [Category* A] [Category* C]
    {p : A ⥤ C} {R S : C} {a b : A}
    (f : R ⟶ S) (φ : a ⟶ b)
    (h : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian (p.map φ) φ := by
  let : p.IsStronglyCartesian f φ := h
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · exact Functor.IsHomLift.map _
  · intro c g τ hτ
    let : p.IsHomLift (g ≫ p.map φ) τ := hτ
    let hdom := CategoryTheory.IsHomLift.domain_eq p f φ
    let hcod := CategoryTheory.IsHomLift.codomain_eq p f φ
    let g' : p.obj c ⟶ R := g ≫ eqToHom hdom
    have hφmap : p.map φ = eqToHom hdom ≫ f ≫ eqToHom hcod.symm := by
      exact CategoryTheory.IsHomLift.fac' p f φ
    have hτmap : p.map τ = g ≫ p.map φ := by
      simpa using CategoryTheory.IsHomLift.fac' p (g ≫ p.map φ) τ
    have hτ' : p.IsHomLift (g' ≫ f) τ := by
      apply CategoryTheory.IsHomLift.of_fac' p (g' ≫ f) τ rfl hcod
      rw [hτmap, hφmap]
      simp [g', Category.assoc]
    let : p.IsHomLift (g' ≫ f) τ := hτ'
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p f φ g'
        (g' ≫ f) rfl τ
    have hχg : p.IsHomLift g χ := by
      apply CategoryTheory.IsHomLift.of_fac' p g χ rfl rfl
      have h := CategoryTheory.IsHomLift.fac' p g' χ
      dsimp [g'] at h
      simpa [Category.assoc] using h
    refine ⟨χ, ⟨hχg, hχfac⟩, ?_⟩
    intro χ' hχ'
    let : p.IsHomLift g χ' := hχ'.1
    have hχ'base : p.IsHomLift g' χ' := by
      apply CategoryTheory.IsHomLift.of_fac' p g' χ' rfl hdom
      have h := CategoryTheory.IsHomLift.fac' p g χ'
      dsimp [g']
      simpa [Category.assoc] using h
    exact hχuniq χ' ⟨hχ'base, hχ'.2⟩

/- This is the preparation lemma in the source.  It is stated using the
   actual projection to `C/U`, rather than only the composite to `C`. -/
theorem slicePullbackLeft_isFibredInGroupoids
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    (slicePullbackLeft F U G).IsFibredInGroupoids := by
  have hbaseFibered : (slicePullbackBase F U G).IsFibered := by
    letI : p.IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.2
    letI : q.IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.2
    letI : (Over.forget U).IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres
        (Over.forget U)).mp (sliceProjection_isFibredInGroupoids U) |>.2
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro ξ R f
    change R ⟶ (Over.forget U).obj ξ.obj.obj.left at f
    rcases ξ.property with ⟨V, hA, hX, hξ⟩
    subst V
    change p.obj ξ.obj.obj.right = (Over.forget U).obj ξ.obj.obj.left at hX
    let fX : R ⟶ p.obj ξ.obj.obj.right := f ≫ eqToHom hX.symm
    obtain ⟨x', b, hb⟩ :=
      (fibred_category_iff_exists_stronglyCartesian p).mp (inferInstance)
        ξ.obj.obj.right R fX
    let : p.IsStronglyCartesian fX b := hb
    let : p.IsHomLift fX b := by infer_instance
    have hdomX : p.obj x' = R :=
      CategoryTheory.IsHomLift.domain_eq p fX b
    subst R
    have hBmap : fX = p.map b :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p fX b
    have hb' : p.IsStronglyCartesian (p.map b) b := by
      simpa [hBmap] using hb
    have hFstrong := F.preserves b hb'
    let : q.IsStronglyCartesian (q.map (F.functor.map b))
        (F.functor.map b) := hFstrong
    obtain ⟨a', c, hc⟩ :=
      (fibred_category_iff_exists_stronglyCartesian (Over.forget U)).mp
        (inferInstance) ξ.obj.obj.left _ f
    let : (Over.forget U).IsStronglyCartesian f c := hc
    let : (Over.forget U).IsHomLift f c := by infer_instance
    have hdomA : (Over.forget U).obj a' = p.obj x' :=
      CategoryTheory.IsHomLift.domain_eq (Over.forget U) f c
    have hc' : (Over.forget U).IsStronglyCartesian
        ((Over.forget U).map c) c := by
      exact sliceStronglyCartesian_map f c hc
    have hGcstrong := G.preserves c hc'
    let : q.IsStronglyCartesian (q.map (G.functor.map c))
        (G.functor.map c) := hGcstrong
    let hcodG := congrArg (fun K : Over U ⥤ C => K.obj ξ.obj.obj.left) G.over
    have hGa : q.obj (G.functor.obj a') = p.obj x' :=
      (congrArg (fun K : Over U ⥤ C => K.obj a') G.over).trans hdomA
    have hGc : q.IsHomLift f (G.functor.map c) := by
      apply CategoryTheory.IsHomLift.of_fac' q f (G.functor.map c)
        hGa hcodG
      have h := CategoryTheory.IsHomLift.fac'
        (Over.forget U) f c
      let hGa0 := congrArg (fun K : Over U ⥤ C => K.obj a') G.over
      have hGmap : q.map (G.functor.map c) =
          eqToHom hGa0 ≫ (Over.forget U).map c ≫ eqToHom hcodG.symm := by
        exact Functor.congr_hom G.over c
      calc
        q.map (G.functor.map c) =
            eqToHom hGa0 ≫ (Over.forget U).map c ≫ eqToHom hcodG.symm := hGmap
        _ = eqToHom hGa ≫ f ≫ eqToHom hcodG.symm := by
          rw [h]
          simp only [Category.assoc, eqToHom_refl, Category.id_comp,
            Category.comp_id]
          rw [← eqToHom_trans]
          congr 1
    have hGcmap : q.map (G.functor.map c) =
        eqToHom hGa ≫ f ≫ eqToHom hcodG.symm := by
      exact CategoryTheory.IsHomLift.fac' q f (G.functor.map c)
    let : q.IsHomLift f (G.functor.map c) := hGc
    let : q.IsHomLift (𝟙 ((Over.forget U).obj ξ.obj.obj.left))
        ξ.obj.obj.hom := hξ
    have hcomp : q.IsHomLift f
        (G.functor.map c ≫ ξ.obj.obj.hom) := by
      exact IsHomLift.comp_lift_id_right' q f (G.functor.map c)
        ((Over.forget U).obj ξ.obj.obj.left) ξ.obj.obj.hom
    have hdomG : q.obj (G.functor.obj a') = p.obj x' :=
      CategoryTheory.IsHomLift.domain_eq q f (G.functor.map c)
    let hFx' := congrArg (fun K : X ⥤ C => K.obj x') F.over
    let hFx := congrArg (fun K : X ⥤ C => K.obj ξ.obj.obj.right) F.over
    have hFmap : q.map (F.functor.map b) =
        eqToHom hFx' ≫ p.map b ≫ eqToHom hFx.symm := by
      exact Functor.congr_hom F.over b
    let hcodξ : q.obj (F.functor.obj ξ.obj.obj.right) =
        q.obj (G.functor.obj ξ.obj.obj.left) :=
      hFx.trans (hX.trans hcodG.symm)
    have hmapξ : q.map ξ.obj.obj.hom = eqToHom hcodξ.symm := by
      have h := CategoryTheory.IsHomLift.fac' q
        (𝟙 ((Over.forget U).obj ξ.obj.obj.left)) ξ.obj.obj.hom
      simpa only [Category.id_comp, Category.comp_id, eqToHom_refl,
        eqToHom_trans] using h
    have hsource : q.obj (G.functor.obj a') =
        q.obj (F.functor.obj x') := hdomG.trans hFx'.symm
    have hfactor : q.map (G.functor.map c ≫ ξ.obj.obj.hom) =
        eqToHom hsource ≫ q.map (F.functor.map b) := by
      rw [Functor.map_comp, hGcmap, hmapξ, hFmap, hBmap]
      dsimp [hsource, hcodξ]
      simp [Category.assoc]
    obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property q
        (q.map (F.functor.map b)) (F.functor.map b)
        (eqToHom hsource) (q.map (G.functor.map c ≫ ξ.obj.obj.hom)) hfactor
        (G.functor.map c ≫ ξ.obj.obj.hom)
    have hχmap : eqToHom hsource = q.map χ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift q (eqToHom hsource) χ
    let hχvertical : q.IsHomLift
        (𝟙 (q.obj (F.functor.obj x'))) χ := by
      apply CategoryTheory.IsHomLift.of_fac' q
        (𝟙 (q.obj (F.functor.obj x'))) χ hsource rfl
      rw [← hχmap]
      dsimp [hsource]
      simp
    let hgroup : IsGroupoid (Functor.Fiber q (p.obj x')) :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 _
    have hχiso : IsIso χ := by
      haveI : IsGroupoid (Functor.Fiber q (p.obj x')) := hgroup
      exact hgroup.all_isIso ⟨χ, hχvertical⟩
    let η : SlicePullbackCategory F U G :=
      { obj :=
          { obj :=
              { left := a'
                right := x'
                hom := χ }
            property := by
              refine ⟨p.obj x', hdomA, rfl, hχvertical⟩ }
        property := by
          change IsIso χ
          exact hχiso }
    let φ : η ⟶ ξ :=
      ObjectProperty.homMk
        { left := c
          right := b
          w := hχeq.symm }
    have hbase : (slicePullbackBase F U G).IsHomLift f φ := by
      apply CategoryTheory.IsHomLift.of_fac' (slicePullbackBase F U G)
        f φ hdomA rfl
      have hfac := CategoryTheory.IsHomLift.fac'
        (Over.forget U) f c
      dsimp [slicePullbackBase, verticalIsoCommaBase, φ,
        ObjectProperty.homMk]
      simpa using hfac
    refine ⟨η, φ, ?_⟩
    let : (slicePullbackBase F U G).IsHomLift f φ := hbase
    refine { toIsHomLift := hbase, universal_property' := ?_ }
    intro ζ g τ hτ
    let : (slicePullbackBase F U G).IsHomLift
        (g ≫ (slicePullbackBase F U G).map φ) τ := hτ
    have hτA : (Over.forget U).IsHomLift
        (g ≫ (Over.forget U).map c) τ.hom.left := by
      apply CategoryTheory.IsHomLift.of_fac'
        (Over.forget U) (g ≫ (Over.forget U).map c) τ.hom.left rfl rfl
      have hfac := CategoryTheory.IsHomLift.fac'
        (slicePullbackBase F U G)
          (g ≫ (slicePullbackBase F U G).map φ) τ
      dsimp [slicePullbackBase, verticalIsoCommaBase] at hfac
      exact hfac
    let : (Over.forget U).IsHomLift
        (g ≫ (Over.forget U).map c) τ.hom.left := hτA
    have hτAmap : (Over.forget U).map τ.hom.left =
        g ≫ (Over.forget U).map c := by
      simpa using CategoryTheory.IsHomLift.fac'
        (Over.forget U) (g ≫ (Over.forget U).map c) τ.hom.left
    let : (Over.forget U).IsStronglyCartesian
        ((Over.forget U).map c) c := hc'
    obtain ⟨χleft, ⟨hχleft, hχleftfac⟩, hχleftuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property
        (Over.forget U) ((Over.forget U).map c) c g
        (g ≫ (Over.forget U).map c) rfl τ.hom.left
    rcases ζ.property with ⟨V, hζA, hζX, hζhom⟩
    subst V
    let hζP : p.obj ζ.obj.obj.right =
        (Over.forget U).obj ζ.obj.obj.left := hζX.trans hζA.symm
    let hFζ := congrArg (fun K : X ⥤ C => K.obj ζ.obj.obj.right) F.over
    let hFxτ := congrArg (fun K : X ⥤ C => K.obj ξ.obj.obj.right) F.over
    let hGζ := congrArg (fun K : Over U ⥤ C => K.obj ζ.obj.obj.left) G.over
    let hζcod : q.obj (F.functor.obj ζ.obj.obj.right) =
        q.obj (G.functor.obj ζ.obj.obj.left) :=
      hFζ.trans (hζX.trans hζA.symm).trans hGζ.symm
    have hζmap : q.map ζ.obj.obj.hom = eqToHom hζcod.symm := by
      have h := CategoryTheory.IsHomLift.fac' q
        (𝟙 ((Over.forget U).obj ζ.obj.obj.left)) ζ.obj.obj.hom
      simpa only [Category.id_comp, Category.comp_id, eqToHom_refl,
        eqToHom_trans] using h
    let hGτL := congrArg (fun K : Over U ⥤ C => K.obj ζ.obj.obj.left) G.over
    let hGτR := hcodG
    have hGτmap : q.map (G.functor.map τ.hom.left) =
        eqToHom hGτL ≫ (Over.forget U).map τ.hom.left ≫
          eqToHom hGτR.symm := by
      exact Functor.congr_hom G.over τ.hom.left
    have hFτmap : q.map (F.functor.map τ.hom.right) =
        eqToHom hFζ ≫ p.map τ.hom.right ≫ eqToHom hFxτ.symm := by
      exact Functor.congr_hom F.over τ.hom.right
    have hτwmap :
        q.map (G.functor.map τ.hom.left) ≫ q.map ξ.obj.obj.hom =
          q.map ζ.obj.obj.hom ≫ q.map (F.functor.map τ.hom.right) := by
      rw [← q.map_comp, ← q.map_comp]
      exact congrArg q.map τ.hom.w
    rw [hGτmap, hmapξ, hζmap, hFτmap] at hτwmap
    let hGτL' := hGτL
    have hτwmap' :
        g ≫ eqToHom hdomA ≫ f ≫ eqToHom hcodξ.symm =
          eqToHom hζP.symm ≫ p.map τ.hom.right ≫ eqToHom hFxτ.symm := by
      rw [hτAmap] at hτwmap
      simp [hζcod, hζP, hGτL', hGτR, hGτmap, hmapξ, hζmap,
        hFτmap, hcodξ, Category.assoc] at hτwmap ⊢
      exact hτwmap
    let gX : p.obj ζ.obj.obj.right ⟶ p.obj x' :=
      eqToHom hζP ≫ g ≫ eqToHom hdomA.symm
    have hτmap : p.map τ.hom.right = gX ≫ fX := by
      apply (cancel_epi (eqToHom hζP.symm)).1
      apply (cancel_mono (eqToHom hFxτ.symm)).1
      simp [gX, fX, Category.assoc]
      rw [← hτwmap']
      simp [Category.assoc]
    have hτX : p.IsHomLift (gX ≫ fX) τ.hom.right := by
      apply CategoryTheory.IsHomLift.of_fac' p (gX ≫ fX)
        τ.hom.right rfl rfl
      exact hτmap.symm
    let : p.IsHomLift (gX ≫ fX) τ.hom.right := hτX
    obtain ⟨χright, ⟨hχright, hχrightfac⟩, hχrightuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property
        p fX b gX (gX ≫ fX) rfl τ.hom.right
    let hTarget : (Over.forget U).obj η.obj.obj.left =
        q.obj (F.functor.obj x') := hdomA.trans hFx'.symm
    have hFmapχright : q.map (F.functor.map χright) =
        eqToHom hFζ ≫ p.map χright ≫ eqToHom hFx'.symm := by
      exact Functor.congr_hom F.over χright
    have hχrightmap : gX = p.map χright :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p gX χright
    let gY : (Over.forget U).obj ζ.obj.obj.left ⟶
        q.obj (F.functor.obj x') :=
      g ≫ eqToHom hdomA ≫ eqToHom hFx'.symm
    have hrightcomp : q.IsHomLift gY
        (ζ.obj.obj.hom ≫ F.functor.map χright) := by
      apply CategoryTheory.IsHomLift.of_fac' q gY
        (ζ.obj.obj.hom ≫ F.functor.map χright) hGζ hTarget
      rw [Functor.map_comp, hζmap, hFmapχright, hχrightmap]
      simp [gY, hζcod, hζP, Category.assoc]
    have hGχleftmap : q.map (G.functor.map χleft) =
        eqToHom hGζ ≫ (Over.forget U).map χleft ≫
          eqToHom (congrArg (fun K : Over U ⥤ C => K.obj η.obj.obj.left)
            G.over).symm := by
      exact Functor.congr_hom G.over χleft
    have hχleftmap : (Over.forget U).map χleft = g := by
      simpa using CategoryTheory.IsHomLift.fac'
        (Over.forget U) g χleft
    have hleftcomp : q.IsHomLift gY
        (G.functor.map χleft ≫ χ) := by
      apply CategoryTheory.IsHomLift.of_fac' q gY
        (G.functor.map χleft ≫ χ) hGζ hTarget
      rw [Functor.map_comp, hGχleftmap, hχmap, hχleftmap]
      simp [gY, hsource, hdomA, hFx', Category.assoc]
    let : q.IsHomLift gY (G.functor.map χleft ≫ χ) := hleftcomp
    let : q.IsHomLift gY (ζ.obj.obj.hom ≫ F.functor.map χright) := hrightcomp
    have hκw : G.functor.map χleft ≫ χ =
        ζ.obj.obj.hom ≫ F.functor.map χright := by
      apply Functor.IsStronglyCartesian.ext
        q (q.map (F.functor.map b)) (F.functor.map b) gY
      calc
        (G.functor.map χleft ≫ χ) ≫ F.functor.map b =
            G.functor.map χleft ≫ (χ ≫ F.functor.map b) := by
              simp [Category.assoc]
        _ = G.functor.map χleft ≫
            (G.functor.map c ≫ ξ.obj.obj.hom) := by rw [hχeq]
        _ = G.functor.map (χleft ≫ c) ≫ ξ.obj.obj.hom := by
          simp [Functor.map_comp, Category.assoc]
        _ = G.functor.map τ.hom.left ≫ ξ.obj.obj.hom := by
          rw [hχleftfac]
        _ = ζ.obj.obj.hom ≫ F.functor.map τ.hom.right := by
          exact τ.hom.w
        _ = ζ.obj.obj.hom ≫ F.functor.map (χright ≫ b) := by
          rw [hχrightfac]
        _ = (ζ.obj.obj.hom ≫ F.functor.map χright) ≫
            F.functor.map b := by
              simp [Functor.map_comp, Category.assoc]
    let κ : ζ ⟶ η :=
      ObjectProperty.homMk
        { left := χleft
          right := χright
          w := hκw }
    have hκbase : (slicePullbackBase F U G).IsHomLift g κ := by
      apply CategoryTheory.IsHomLift.of_fac'
        (slicePullbackBase F U G) g κ rfl rfl
      have hfac := CategoryTheory.IsHomLift.fac'
        (Over.forget U) g χleft
      dsimp [slicePullbackBase, verticalIsoCommaBase, κ,
        ObjectProperty.homMk]
      exact hfac
    have hκfac : κ ≫ φ = τ := by
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · dsimp [κ, φ, ObjectProperty.homMk]
        exact hχleftfac
      · dsimp [κ, φ, ObjectProperty.homMk]
        exact hχrightfac
    intro m hm
    rcases hm with ⟨hmBase, hmFac⟩
    let : (slicePullbackBase F U G).IsHomLift g m := hmBase
    have hmLeft : (Over.forget U).IsHomLift g m.hom.left := by
      apply CategoryTheory.IsHomLift.of_fac'
        (Over.forget U) g m.hom.left rfl rfl
      have hfac := CategoryTheory.IsHomLift.fac'
        (slicePullbackBase F U G) g m
      dsimp [slicePullbackBase, verticalIsoCommaBase] at hfac
      exact hfac
    have hmLeftFac : m.hom.left ≫ c = τ.hom.left := by
      have hh := congrArg (fun k => k.hom.left) hmFac
      simpa [φ, ObjectProperty.homMk] using hh
    have hmLeftEq : m.hom.left = χleft :=
      hχleftuniq m.hom.left ⟨hmLeft, hmLeftFac⟩
    have hmLeftMap : (Over.forget U).map m.hom.left = g := by
      let : (Over.forget U).IsHomLift g m.hom.left := hmLeft
      simpa using CategoryTheory.IsHomLift.fac'
        (Over.forget U) g m.hom.left
    have hGmmap : q.map (G.functor.map m.hom.left) =
        eqToHom hGζ ≫ (Over.forget U).map m.hom.left ≫
          eqToHom (congrArg (fun K : Over U ⥤ C => K.obj η.obj.obj.left)
            G.over).symm := by
      exact Functor.congr_hom G.over m.hom.left
    have hmFmap : q.map (F.functor.map m.hom.right) =
        eqToHom hFζ ≫ p.map m.hom.right ≫ eqToHom hFx'.symm := by
      exact Functor.congr_hom F.over m.hom.right
    have hmWmap :
        q.map (G.functor.map m.hom.left) ≫ q.map χ =
          q.map ζ.obj.obj.hom ≫ q.map (F.functor.map m.hom.right) := by
      rw [← q.map_comp, ← q.map_comp]
      exact congrArg q.map m.hom.w
    rw [hGmmap, hχmap, hζmap, hmFmap, hmLeftMap] at hmWmap
    have hmWmap' :
        eqToHom hGζ ≫ g ≫ eqToHom hTarget =
          eqToHom hζcod.symm ≫ eqToHom hFζ ≫
            p.map m.hom.right ≫ eqToHom hFx'.symm := by
      simpa [hsource, hTarget, hζcod, hζP, Category.assoc] using hmWmap
    have hmXMap : p.map m.hom.right = gX := by
      apply (cancel_epi (eqToHom hGζ)).1
      apply (cancel_epi (eqToHom hζP)).1
      apply (cancel_mono (eqToHom hFx'.symm)).1
      simp [gX, gY, hTarget, hζcod, Category.assoc]
      rw [← hmWmap']
      simp [Category.assoc]
    have hmRight : p.IsHomLift gX m.hom.right := by
      rw [← hmXMap]
      infer_instance
    have hmRightFac : m.hom.right ≫ b = τ.hom.right := by
      have hh := congrArg (fun k => k.hom.right) hmFac
      simpa [φ, ObjectProperty.homMk] using hh
    have hmRightEq : m.hom.right = χright :=
      hχrightuniq m.hom.right ⟨hmRight, hmRightFac⟩
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simpa [κ, ObjectProperty.homMk] using hmLeftEq
    · simpa [κ, ObjectProperty.homMk] using hmRightEq
  have hbase : (slicePullbackBase F U G).IsFibredInGroupoids := by
    apply (fibredInGroupoids_iff_fibred_groupoid_fibres
      (slicePullbackBase F U G)).mpr
    constructor
    · intro V
      let hover : IsGroupoid (Functor.Fiber (Over.forget U) V) :=
        (fibredInGroupoids_iff_fibred_groupoid_fibres
          (Over.forget U)).mp (sliceProjection_isFibredInGroupoids U) |>.1 V
      let hpgroup : IsGroupoid (Functor.Fiber p V) :=
        (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.1 V
      constructor
      intro A B m
      let : (slicePullbackBase F U G).IsHomLift (𝟙 V) m.1 := m.2
      have hleft : (Over.forget U).IsHomLift
          (𝟙 V) m.1.hom.left := by
        apply CategoryTheory.IsHomLift.of_fac'
          (Over.forget U) (𝟙 V) m.1.hom.left A.2 B.2
        have hfac := CategoryTheory.IsHomLift.fac'
          (slicePullbackBase F U G) (𝟙 V) m.1
        dsimp [slicePullbackBase, verticalIsoCommaBase] at hfac
        exact hfac
      have hAprop := A.1.property
      have hBprop := B.1.property
      rcases hAprop with ⟨WA, hAleft, hAright, hAhom⟩
      rcases hBprop with ⟨WB, hBleft, hBright, hBhom⟩
      let hAright' : p.obj A.1.obj.right = V :=
        hAright.trans hAleft.symm |>.trans A.2
      let hBright' : p.obj B.1.obj.right = V :=
        hBright.trans hBleft.symm |>.trans B.2
      have hright : p.IsHomLift (𝟙 V) m.1.hom.right := by
        apply CategoryTheory.IsHomLift.of_fac' p (𝟙 V) m.1.hom.right
          hAright' hBright'
        have hFmap := Functor.congr_hom F.over m.1.hom.right
        have hGmap := Functor.congr_hom G.over m.1.hom.left
        have hAmap := CategoryTheory.IsHomLift.fac' q (𝟙 WA) A.1.obj.hom
        have hBmap := CategoryTheory.IsHomLift.fac' q (𝟙 WB) B.1.obj.hom
        have hmmap := congrArg q.map m.1.hom.w
        have hleftmap := CategoryTheory.IsHomLift.fac'
          (Over.forget U) (𝟙 V) m.1.hom.left
        rw [hFmap]
        rw [← hGmap, ← hAmap, ← hBmap]
        rw [← Functor.map_comp, ← Functor.map_comp] at hmmap
        simp only [Functor.map_comp] at hmmap
      let kleft := Functor.Fiber.homMk (Over.forget U) V m.1.hom.left
      let _ : IsIso kleft := hover.all_isIso kleft
      let _ : IsIso m.1.hom.left := by
        change IsIso (Functor.Fiber.fiberInclusion.map kleft)
        exact (Functor.Fiber.fiberInclusion.mapIso (asIso kleft)).isIso_hom
      let kright := Functor.Fiber.homMk p V m.1.hom.right
      let _ : IsIso kright := hpgroup.all_isIso kright
      let _ : IsIso m.1.hom.right := by
        change IsIso (Functor.Fiber.fiberInclusion.map kright)
        exact (Functor.Fiber.fiberInclusion.mapIso (asIso kright)).isIso_hom
      let g : B.1 ⟶ A.1 :=
        ObjectProperty.homMk
          { left := inv m.1.hom.left
            right := inv m.1.hom.right
            w := by
              apply (cancel_mono (G.functor.map m.1.hom.left)).1
              rw [Functor.map_comp]
              simp only [IsIso.hom_inv_id_assoc, Category.id_comp]
              rw [← m.1.hom.w]
              rw [Functor.map_comp]
              simp only [IsIso.inv_hom_id_assoc, Category.comp_id] }
      have hg : (slicePullbackBase F U G).IsHomLift (𝟙 V) g := by
        exact CategoryTheory.IsHomLift.lift_id_inv_isIso
          (slicePullbackBase F U G) V m.1
      let gi : B ⟶ A := ⟨g, hg⟩
      refine ⟨⟨gi, ?_, ?_⟩⟩
      · apply Functor.Fiber.hom_ext
        change m.1 ≫ g = 𝟙 A.1
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp
      · apply Functor.Fiber.hom_ext
        change g ≫ m.1 = 𝟙 B.1
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;> simp
    · exact hbaseFibered
  letI : (slicePullbackBase F U G).IsFibredInGroupoids := hbase
  exact fibredInGroupoids_over_slice U (slicePullbackBase F U G)
    (slicePullbackLeft F U G) rfl hbase

/- The source's definition of a representable 1-morphism. -/
def IsRepresentableFibredMorphism
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (_hp : p.IsFibredInGroupoids) (_hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) : Prop :=
  ∀ (U : C) (G : FibredMorphism (Over.forget U) q),
    IsRepresentableCategoryFibredInGroupoids (slicePullbackLeft F U G)

/-! ## The fibre description -/

def sliceFibreObject {C : Type*} [Category* C] (U : C) (f : Over U) :
    Functor.Fiber (Over.forget U) f.left :=
  ⟨f, rfl⟩

def sliceMorphismIdentityValue
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    Functor.Fiber q U :=
  ⟨G.functor.obj (Over.mk (𝟙 U)),
    Functor.congr_obj G.over (Over.mk (𝟙 U))⟩

def fibredMorphismFibreFunctor
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (V : C) :
    Functor.Fiber p V ⥤ Functor.Fiber q V :=
  fibreFunctor p q F.functor F.over V

def sliceMorphismFibreFunctor
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C) (G : FibredMorphism (Over.forget U) q) (V : C) :
    Functor.Fiber (Over.forget U) V ⥤ Functor.Fiber q V :=
  fibreFunctor (Over.forget U) q G.functor G.over V

/- `PullbackChoice` uses Mathlib's typeclass `IsFibered`, while the source
   presents fibredness in groupoids as an explicit hypothesis.  This wrapper
   carries the canonical `IsFibered` instance supplied by Unit 35 without
   changing the choice data itself. -/
def FibredPullbackChoice
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids) : Type _ :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  PullbackChoice q

noncomputable def defaultFibredPullbackChoice
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids) : FibredPullbackChoice q hq :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  PullbackChoice.default q

def chosenPullbackObject
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) {U : C}
    (y : Functor.Fiber q U) (f : Over U) :
    Functor.Fiber q f.left :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  P.pullback f.hom y

noncomputable def chosenPullbackMorphism
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) (U : C)
    (y : Functor.Fiber q U) :
    FibredMorphism (Over.forget U) q :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  { functor := twoYonedaPullbackFunctor q P U y
    over := twoYonedaPullbackFunctor_isOver q P U y
    preserves := twoYonedaPullbackFunctor_mapsStronglyCartesian q P U y }

def sliceMorphismAsTwoYonedaObject
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    twoYonedaGroupoidMorphismCategory q U :=
  ⟨G.functor, G.over⟩

noncomputable def chosenPullbackAsTwoYonedaObject
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) (U : C)
    (y : Functor.Fiber q U) :
    twoYonedaGroupoidMorphismCategory q U :=
  let H := chosenPullbackMorphism q hq P U y
  ⟨H.functor, H.over⟩

theorem sliceMorphism_isomorphic_to_chosenPullback
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq)
    (G : FibredMorphism (Over.forget U) q) :
    Nonempty
      (sliceMorphismAsTwoYonedaObject U G ≅
        chosenPullbackAsTwoYonedaObject q hq P U
          (sliceMorphismIdentityValue U G)) := by
  letI : q.IsFibredInGroupoids := hq
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  have hGobj :
      twoYonedaEvaluationCoreObj q U (sliceMorphismAsTwoYonedaObject U G) =
        sliceMorphismIdentityValue U G := by
    apply Subtype.ext
    rfl
  have hHobj :
      twoYonedaEvaluationCoreObj q U
          (chosenPullbackAsTwoYonedaObject q hq P U
            (sliceMorphismIdentityValue U G)) =
        chosenPullbackObject q hq P (sliceMorphismIdentityValue U G)
          (Over.mk (𝟙 U)) := by
    apply Subtype.ext
    rfl
  obtain ⟨α, -, -⟩ := pullback_identity_iso q P U
  let e :
      twoYonedaEvaluationCoreObj q U (sliceMorphismAsTwoYonedaObject U G) ≅
        twoYonedaEvaluationCoreObj q U
          (chosenPullbackAsTwoYonedaObject q hq P U
            (sliceMorphismIdentityValue U G)) :=
    eqToIso hGobj ≪≫
      α.hom.app (sliceMorphismIdentityValue U G) ≪≫
        eqToIso hHobj.symm
  letI : (twoYonedaEvaluationCore q U).IsEquivalence :=
    twoYoneda_groupoid_equivalence q U
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful
    (twoYonedaEvaluationCore q U)).preimageIso e⟩

structure RelativeFibrePair
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) where
  x : Functor.Fiber p f.left
  phi : chosenPullbackObject q hq P y f ⟶
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj x

structure RelativeFibrePairHom
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {hq : q.IsFibredInGroupoids} {P : FibredPullbackChoice q hq}
    {y : Functor.Fiber q U} {f : Over U}
    (A B : RelativeFibrePair F U hq P y f) where
  psi : A.x ⟶ B.x
  comm : A.phi ≫
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi

@[ext]
lemma RelativeFibrePairHom.ext
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {hq : q.IsFibredInGroupoids} {P : FibredPullbackChoice q hq}
    {y : Functor.Fiber q U} {f : Over U}
    {A B : RelativeFibrePair F U hq P y f}
    {k l : RelativeFibrePairHom A B} (h : k.psi = l.psi) : k = l := by
  cases k
  cases l
  cases h
  rfl

instance relativeFibrePairCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :
    Category (RelativeFibrePair F U hq P y f) where
  Hom A B := RelativeFibrePairHom A B
  id A :=
    { psi := 𝟙 A.x
      comm := by simp }
  comp k l :=
    { psi := k.psi ≫ l.psi
      comm := by
        rw [Functor.map_comp, ← Category.assoc, k.comm]
        exact l.comm }
  id_comp k := by
    apply RelativeFibrePairHom.ext
    simp
  comp_id k := by
    apply RelativeFibrePairHom.ext
    simp
  assoc k l m := by
    apply RelativeFibrePairHom.ext
    simp [Category.assoc]

abbrev RelativeFibrePairCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :=
  RelativeFibrePair F U hq P y f

def relativeFibrePairIsoRelation
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :
    Setoid (RelativeFibrePairCategory F U hq P y f) where
  r A B := Nonempty (A ≅ B)
  iseqv :=
    { refl := fun A => ⟨Iso.refl A⟩
      symm := fun h => ⟨(Classical.choice h).symm⟩
      trans := fun h k =>
        ⟨(Classical.choice h).trans (Classical.choice k)⟩ }

abbrev RelativeFibrePairClass
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :=
  Quotient (relativeFibrePairIsoRelation F U hq P y f)

theorem relativeFibrePair_phi_isIso
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A : RelativeFibrePairCategory F U hq P y f) : IsIso A.phi := by
  let hgroup : IsGroupoid (Functor.Fiber q f.left) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 f.left
  exact hgroup.all_isIso A.phi

noncomputable def relativeFibrePair_phi_inv
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A : RelativeFibrePairCategory F U hq P y f) :
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj A.x ⟶
      chosenPullbackObject q hq P y f := by
  letI : IsIso A.phi := relativeFibrePair_phi_isIso F U hq P y f A
  exact inv A.phi

theorem relativeFibrePairHom_comm_iff
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A B : RelativeFibrePairCategory F U hq P y f)
    (psi : A.x ⟶ B.x) :
    A.phi ≫
          (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi ↔
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi =
        relativeFibrePair_phi_inv F U hq P y f A ≫ B.phi := by
  letI : IsIso A.phi := relativeFibrePair_phi_isIso F U hq P y f A
  change A.phi ≫
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi ↔
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi =
      inv A.phi ≫ B.phi
  constructor
  · intro h
    simpa [Category.assoc] using congrArg (fun k => inv A.phi ≫ k) h
  · intro h
    rw [h]
    simp [Category.assoc]

def pullbackFibreBaseObject
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Functor.Fiber q f.left :=
  (sliceMorphismFibreFunctor U G f.left).obj (sliceFibreObject U f)

structure PullbackFibreObject
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) where
  x : Functor.Fiber p f.left
  phi : pullbackFibreBaseObject (q := q) U G f ⟶
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj x

structure PullbackFibreHom
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {G : FibredMorphism (Over.forget U) q} {f : Over U}
  (A B : PullbackFibreObject F U G f) where
  psi : A.x ⟶ B.x
  comm : A.phi ≫
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi

@[ext]
lemma PullbackFibreHom.ext
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {G : FibredMorphism (Over.forget U) q} {f : Over U}
    {A B : PullbackFibreObject F U G f}
    {k l : PullbackFibreHom A B} (h : k.psi = l.psi) : k = l := by
  cases k
  cases l
  cases h
  rfl

instance pullbackFibreCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Category (PullbackFibreObject F U G f) where
  Hom A B := PullbackFibreHom A B
  id A :=
    { psi := 𝟙 A.x
      comm := by simp }
  comp k l :=
    { psi := k.psi ≫ l.psi
      comm := by
        rw [Functor.map_comp, ← Category.assoc, k.comm]
        exact l.comm }
  id_comp k := by
    apply PullbackFibreHom.ext
    simp
  comp_id k := by
    apply PullbackFibreHom.ext
    simp
  assoc k l m := by
    apply PullbackFibreHom.ext
    simp [Category.assoc]

abbrev PullbackFibreCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :=
  PullbackFibreObject F U G f

def pullbackFibreObjectIsoRelation
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Setoid (PullbackFibreCategory F U G f) where
  r A B := Nonempty (A ≅ B)
  iseqv :=
    { refl := fun A => ⟨Iso.refl A⟩
      symm := fun h => ⟨(Classical.choice h).symm⟩
      trans := fun h k =>
        ⟨(Classical.choice h).trans (Classical.choice k)⟩ }

abbrev PullbackFibreObjectClass
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :=
  Quotient (pullbackFibreObjectIsoRelation F U G f)

theorem pullbackFibreObject_phi_isIso
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U)
    (A : PullbackFibreCategory F U G f) : IsIso A.phi := by
  let hgroup : IsGroupoid (Functor.Fiber q f.left) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 f.left
  exact hgroup.all_isIso A.phi

theorem identify_pullback_fibre
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids) (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Nonempty
      (Functor.Fiber (slicePullbackLeft F U G) f ≌
        PullbackFibreCategory F U G f) := by
  sorry

theorem identify_pullback_fibre_with_chosen_pullback
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids) (F : FibredMorphism p q) (U : C)
    (P : FibredPullbackChoice q hq)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Nonempty
      (Functor.Fiber (slicePullbackLeft F U G) f ≌
        RelativeFibrePairCategory F U hq P
          (sliceMorphismIdentityValue U G) f) := by
  sorry

/-! ## Faithfulness and the presheaf criterion -/

theorem representable_fibredMorphism_fibrewise_faithful
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q)
    (hF : IsRepresentableFibredMorphism hp hq F) :
    ∀ U : C, (fibredMorphismFibreFunctor F U).Faithful := by
  sorry

/- Faithfulness makes the fibres of the slice pullback setoids.  This is the
   hypothesis needed by the established Unit 40 object-class presheaf, whose
   values are the actual isomorphism classes of the pullback fibres. -/
theorem slicePullback_isCategoryFibredInSetoids
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q)
    (hfaithful : ∀ V : C, (fibredMorphismFibreFunctor F V).Faithful)
    (U : C) (G : FibredMorphism (Over.forget U) q) :
    IsCategoryFibredInSetoids (slicePullbackLeft F U G) := by
  sorry

theorem criterion_for_representable_fibredMorphism
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (pullbacksY : FibredPullbackChoice q hq)
    (hfaithful : ∀ U : C, (fibredMorphismFibreFunctor F U).Faithful)
    (hpresheaf : ∀ (U : C) (y : Functor.Fiber q U),
      IsRepresentableObjectClassPresheaf
        (slicePullbackLeft F U
          (chosenPullbackMorphism q hq pullbacksY U y))
        (slicePullback_isCategoryFibredInSetoids hp hq F hfaithful U
          (chosenPullbackMorphism q hq pullbacksY U y))) :
    IsRepresentableFibredMorphism hp hq F := by
  sorry

/-! ## 2-products and the diagonal -/

theorem identityFunctor_isStronglyCartesian
    {C : Type*} [Category* C] {R S : C} (f : R ⟶ S) :
    (𝟭 C).IsStronglyCartesian f f := by
  let hf : (𝟭 C).IsHomLift f f := by
    exact Functor.IsHomLift.map f
  refine { toIsHomLift := hf, universal_property' := ?_ }
  intro c g φ hφ
  refine ⟨g, ⟨Functor.IsHomLift.map g, ?_⟩, ?_⟩
  · simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift (𝟭 C) (g ≫ f) φ)
  · intro χ hχ
    simpa using
      (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (𝟭 C) _ _ g χ hχ.1).symm

theorem toBase_mapsStronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    MapsStronglyCartesian p (𝟭 C) p := by
  intro a b φ hφ
  change Functor.IsStronglyCartesian (𝟭 C)
    ((𝟭 C).map (p.map φ)) ((𝟭 C).map (p.map φ))
  exact identityFunctor_isStronglyCartesian _

def toBaseFibredMorphism
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    FibredMorphism p (𝟭 C) where
  functor := p
  over := Functor.comp_id p
  preserves := toBase_mapsStronglyCartesian p

abbrev TwoProductCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    (p : X ⥤ C) (q : Y ⥤ C) :=
  VerticalIsoComma p q p q (𝟭 C)
    (toBaseFibredMorphism p).over (toBaseFibredMorphism q).over

def twoProductBase
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    (p : X ⥤ C) (q : Y ⥤ C) :
    TwoProductCategory p q ⥤ C :=
  verticalIsoCommaBase p q p q (𝟭 C)
    (toBaseFibredMorphism p).over (toBaseFibredMorphism q).over

theorem twoProductBase_isFibredInGroupoids
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    (twoProductBase p p).IsFibredInGroupoids := by
  sorry

def rawDiagonalFunctor
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    X ⥤ TwoProductCategory p p where
  obj x :=
    { obj := (isoCommaDiagonal p).obj x
      property := by
        refine ⟨p.obj x, rfl, rfl, ?_⟩
        exact Functor.IsHomLift.map (𝟙 (p.obj x)) }
  map f := ObjectProperty.homMk ((isoCommaDiagonal p).map f)
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    rfl

theorem rawDiagonalFunctor_over
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    rawDiagonalFunctor p ⋙ twoProductBase p p = p := by
  rfl

theorem rawDiagonalFunctor_mapsStronglyCartesian
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    MapsStronglyCartesian p (twoProductBase p p) (rawDiagonalFunctor p) := by
  sorry

def rawDiagonalMorphism
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    FibredMorphism p (twoProductBase p p) where
  functor := rawDiagonalFunctor p
  over := rawDiagonalFunctor_over p
  preserves := rawDiagonalFunctor_mapsStronglyCartesian p hp

def IsRepresentableDiagonal
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) : Prop :=
  IsRepresentableFibredMorphism hp (twoProductBase_isFibredInGroupoids p hp)
    (rawDiagonalMorphism p hp)

theorem representable_diagonal_iff_slice_representable
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids)
    [HasBinaryProducts C] [HasPullbacks C] :
    IsRepresentableDiagonal p hp ↔
      ∀ (U : C) (G : FibredMorphism (Over.forget U) p),
        IsRepresentableFibredMorphism
          (sliceProjection_isFibredInGroupoids U) hp G := by
  sorry

end

end Formalization.Books.Categories.Unit42
