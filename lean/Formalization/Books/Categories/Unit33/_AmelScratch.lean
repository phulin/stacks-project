import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered

namespace ScratchAmel

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty

universe u v

noncomputable section

def Property {X Y C : Type u} [Category.{v} X] [Category.{v} Y]
    [Category.{v} C] (q : Y ⥤ C) (F : X ⥤ Y) :
    ObjectProperty (Comma (𝟭 Y) F) := fun ξ =>
  ∃ U : C,
    q.obj ξ.left = U ∧ q.obj (F.obj ξ.right) = U ∧
      q.IsHomLift (𝟙 U) ξ.hom

abbrev ACategory {X Y C : Type u} [Category.{v} X] [Category.{v} Y]
    [Category.{v} C] (q : Y ⥤ C) (F : X ⥤ Y) :=
  (Property q F).FullSubcategory

def base {X Y C : Type u} [Category.{v} X] [Category.{v} Y]
    [Category.{v} C] (q : Y ⥤ C) (F : X ⥤ Y) :
    ACategory q F ⥤ C :=
  (Property q F).ι ⋙ Comma.fst (𝟭 Y) F ⋙ q

private theorem lifts {A C : Type u} [Category.{v} A] [Category.{v} C]
    (p : A ⥤ C) [p.IsFibered] (a : A) (R : C) (f : R ⟶ p.obj a) :
    ∃ (b : A) (φ : b ⟶ a), Functor.IsStronglyCartesian p f φ := by
  obtain ⟨b, φ, hφ⟩ :=
    (inferInstance : p.IsFibered).toIsPreFibered.exists_isCartesian' f
  exact ⟨b, φ, @Functor.IsFibered.isStronglyCartesian_of_isCartesian
    _ _ _ _ p inferInstance R _ f _ _ φ hφ⟩

theorem exists_lift {X Y C : Type u} [Category.{v} X] [Category.{v} Y]
    [Category.{v} C] (q : Y ⥤ C) (F : X ⥤ Y)
    [q.IsFibered] [(F ⋙ q).IsFibered]
    (preserves : ∀ {a b : X} (φ : a ⟶ b),
      Functor.IsStronglyCartesian (F ⋙ q) ((F ⋙ q).map φ) φ →
        Functor.IsStronglyCartesian q (q.map (F.map φ)) (F.map φ))
    {ξ : ACategory q F} {R : C} (f : R ⟶ (base q F).obj ξ) :
    ∃ (ξ' : ACategory q F) (h : ξ' ⟶ ξ),
      (base q F).IsStronglyCartesian f h := by
  classical
  rcases ξ.property with ⟨U, hy, hx, hξ⟩
  change R ⟶ q.obj ξ.obj.left at f
  let hxy : (F ⋙ q).obj ξ.obj.right = q.obj ξ.obj.left := hx.trans hy.symm
  let fX := f ≫ eqToHom hxy.symm
  obtain ⟨x', φ, hφ⟩ :=
    lifts (F ⋙ q)
      ξ.obj.right R fX
  letI : (F ⋙ q).IsStronglyCartesian fX φ := hφ
  have hdomX : (F ⋙ q).obj x' = R :=
    CategoryTheory.IsHomLift.domain_eq (F ⋙ q) fX φ
  subst R
  have hmapX : fX = (F ⋙ q).map φ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (F ⋙ q) fX φ
  obtain ⟨y', ψ, hψ⟩ :=
    lifts q
      ξ.obj.left ((F ⋙ q).obj x') f
  letI : q.IsStronglyCartesian f ψ := hψ
  have hdomY : q.obj y' = (F ⋙ q).obj x' :=
    CategoryTheory.IsHomLift.domain_eq q f ψ
  have hmapY : q.map ψ = eqToHom hdomY ≫ f := by
    simpa [base, Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q f ψ)
  let hFx' : q.obj (F.obj x') = (F ⋙ q).obj x' := rfl
  let hFx : q.obj (F.obj ξ.obj.right) = (F ⋙ q).obj ξ.obj.right := rfl
  let hFy : q.obj (F.obj ξ.obj.right) = U := hFx.trans hx
  have hFmap : q.map (F.map φ) =
      eqToHom hFx' ≫ (F ⋙ q).map φ ≫ eqToHom hFx.symm := by
    simp [Functor.comp_map]
  have hξmap : q.map ξ.obj.hom =
      eqToHom hy ≫ (𝟙 U) ≫ eqToHom hFy.symm := by
    letI : q.IsHomLift (𝟙 U) ξ.obj.hom := hξ
    simpa [Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q (𝟙 U) ξ.obj.hom)
  let g : q.obj y' ⟶ q.obj (F.obj x') :=
    eqToHom hdomY ≫ eqToHom hFx'.symm
  have hφ' : (F ⋙ q).IsStronglyCartesian ((F ⋙ q).map φ) φ := by
    simpa [hmapX] using
      (inferInstance : (F ⋙ q).IsStronglyCartesian fX φ)
  letI : (F ⋙ q).IsStronglyCartesian ((F ⋙ q).map φ) φ := hφ'
  letI : q.IsStronglyCartesian (q.map (F.map φ)) (F.map φ) :=
    preserves φ hφ'
  have hfactor : q.map (ψ ≫ ξ.obj.hom) = g ≫ q.map (F.map φ) := by
    rw [Functor.map_comp, hmapY, hξmap, hFmap, ← hmapX]
    simp only [g, fX, hxy, hFx, hFx', hFy, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property q
      (q.map (F.map φ)) (F.map φ) g (q.map (ψ ≫ ξ.obj.hom)) hfactor
      (ψ ≫ ξ.obj.hom)
  have hχmap : g = q.map χ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift q g χ
  have hχbase : q.IsHomLift (𝟙 ((F ⋙ q).obj x')) χ := by
    apply CategoryTheory.IsHomLift.of_fac q (𝟙 ((F ⋙ q).obj x')) χ
      hdomY hFx'
    rw [← hχmap]
    simp [g, Category.assoc]
  let ξ' : ACategory q F :=
    { obj := { left := y', right := x', hom := χ }
      property := ⟨(F ⋙ q).obj x', hdomY, rfl, hχbase⟩ }
  let h : ξ' ⟶ ξ := ObjectProperty.homMk
    { left := ψ, right := φ, w := hχeq.symm }
  refine ⟨ξ', h, ?_⟩
  have hbase : (base q F).IsHomLift f h := by
    let hdomY' : (base q F).obj ξ' = (F ⋙ q).obj x' := by
      change q.obj y' = (F ⋙ q).obj x'
      exact hdomY
    change q.obj y' = (F ⋙ q).obj x' at hdomY'
    have hcod : (base q F).obj ξ = q.obj ξ.obj.left := by
      change q.obj ξ.obj.left = q.obj ξ.obj.left
      rfl
    apply CategoryTheory.IsHomLift.of_fac' (base q F) f h hdomY' hcod
    simp only [base, h, ξ', Functor.comp_map, ObjectProperty.ι_map,
      Comma.fst_map, ObjectProperty.homMk, hmapY, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
    change eqToHom hdomY ≫ f =
      eqToHom hdomY ≫ f ≫ eqToHom (rfl : q.obj ξ.obj.left = q.obj ξ.obj.left)
    simp
  refine { toIsHomLift := hbase, universal_property' := ?_ }
  intro ζ g₀ τ hτ
  rcases ζ.property with ⟨U₀, hy₀, hx₀, hζ⟩
  letI : (base q F).IsHomLift (g₀ ≫ f) τ := hτ
  have hτmap : g₀ ≫ f = (base q F).map τ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (base q F) (g₀ ≫ f) τ
  change q.obj ζ.obj.left ⟶ (F ⋙ q).obj x' at g₀
  have hτmap' : g₀ ≫ f = q.map τ.hom.left := by
    simpa [base] using hτmap
  have hτq : q.IsHomLift (g₀ ≫ f) τ.hom.left := by
    rw [hτmap']
    infer_instance
  obtain ⟨α, ⟨hα, hαeq⟩, hαuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property q f ψ
      g₀ (g₀ ≫ f) rfl τ.hom.left
  let hxy₀ : (F ⋙ q).obj ζ.obj.right = q.obj ζ.obj.left :=
    hx₀.trans hy₀.symm
  let gX : (F ⋙ q).obj ζ.obj.right ⟶ (F ⋙ q).obj x' :=
    eqToHom hxy₀ ≫ g₀ ≫ eqToHom hdomY.symm ≫ g
  have hζmap : q.map ζ.obj.hom =
      eqToHom hy₀ ≫ (𝟙 U₀) ≫ eqToHom hx₀.symm := by
    letI : q.IsHomLift (𝟙 U₀) ζ.obj.hom := hζ
    simpa [Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q (𝟙 U₀) ζ.obj.hom)
  have hαmap : q.map α = g₀ ≫ eqToHom hdomY.symm :=
    by
      have h := CategoryTheory.IsHomLift.fac' q g₀ α
      simpa [Category.assoc] using h
  have hτfactor : (F ⋙ q).map τ.hom.right =
      gX ≫ (F ⋙ q).map φ := by
    have hf : f = eqToHom hdomY.symm ≫ q.map ψ := by
      rw [hmapY]
      simp
    have hχcomp : q.map ψ ≫ q.map ξ.obj.hom =
        q.map χ ≫ q.map (F.map φ) := by
      rw [← q.map_comp, ← q.map_comp, hχeq]
    have hτw := congrArg q.map τ.hom.w
    change q.map (τ.hom.left ≫ ξ.obj.hom) =
      q.map (ζ.obj.hom ≫ F.map τ.hom.right) at hτw
    rw [q.map_comp, q.map_comp] at hτw
    rw [← hτmap'] at hτw
    have hτw' :
        g₀ ≫ eqToHom hdomY.symm ≫ q.map χ ≫ q.map (F.map φ) =
          q.map ζ.obj.hom ≫ q.map (F.map τ.hom.right) := by
      calc
        g₀ ≫ eqToHom hdomY.symm ≫ q.map χ ≫ q.map (F.map φ) =
            (g₀ ≫ f) ≫ q.map ξ.obj.hom := by
              rw [← hχcomp, hmapY]
              simp [Category.assoc]
        _ = q.map ζ.obj.hom ≫ q.map (F.map τ.hom.right) := hτw
    have hτw'' := congrArg
      (fun k => eqToHom hx₀ ≫ eqToHom hy₀.symm ≫ k) hτw'.symm
    simpa [hζmap, gX, hχmap, hxy₀, hx₀, hy₀, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
      using hτw''
  have hτp : (F ⋙ q).IsHomLift
      (gX ≫ (F ⋙ q).map φ) τ.hom.right := by
    have hmap : (F ⋙ q).IsHomLift ((F ⋙ q).map τ.hom.right) τ.hom.right :=
      inferInstance
    rw [hτfactor] at hmap
    exact hmap
  letI : (F ⋙ q).IsHomLift
      (gX ≫ (F ⋙ q).map φ) τ.hom.right := hτp
  obtain ⟨β, ⟨hβ, hβeq⟩, hβuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property (F ⋙ q)
      ((F ⋙ q).map φ) φ gX ((F ⋙ q).map τ.hom.right) hτfactor τ.hom.right
  have hβmap : gX = (F ⋙ q).map β :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (F ⋙ q) gX β
  let gcomp : q.obj ζ.obj.left ⟶ q.obj (F.obj x') :=
    g₀ ≫ eqToHom hdomY.symm ≫ g
  have hα' : q.IsHomLift (g₀ ≫ eqToHom hdomY.symm) α := by
    apply CategoryTheory.IsHomLift.of_fac q
      (g₀ ≫ eqToHom hdomY.symm) α rfl rfl
    simpa using hαmap.symm
  have hother : q.IsHomLift gcomp
      (ζ.obj.hom ≫ F.map β) := by
    apply CategoryTheory.IsHomLift.of_fac q gcomp
      (ζ.obj.hom ≫ F.map β) rfl rfl
    change gcomp = q.map (ζ.obj.hom ≫ F.map β)
    have hβmap' : q.map (F.map β) = gX := by
      simpa [Functor.comp_map] using hβmap.symm
    rw [Functor.map_comp, hζmap, hβmap']
    simp only [gcomp, gX, hxy₀, hx₀, hy₀, Category.assoc,
      eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  letI : q.IsHomLift (g₀ ≫ eqToHom hdomY.symm) α := hα'
  letI : q.IsHomLift gcomp (α ≫ χ) := by infer_instance
  letI : q.IsHomLift gcomp (ζ.obj.hom ≫ F.map β) := hother
  have hcomp : (α ≫ χ) ≫ F.map φ =
      (ζ.obj.hom ≫ F.map β) ≫ F.map φ := by
    rw [Category.assoc, hχeq, ← Category.assoc, hαeq,
      ← Category.assoc, τ.hom.w, Functor.map_comp, hβeq]
    simp [Category.assoc]
  have hw : α ≫ χ = ζ.obj.hom ≫ F.map β :=
    Functor.IsStronglyCartesian.ext q (q.map (F.map φ)) (F.map φ)
      gcomp hcomp
  let δ : ζ ⟶ ξ' := ObjectProperty.homMk
    { left := α, right := β, w := hw }
  have hδbase : (base q F).IsHomLift g₀ δ := by
    change q.IsHomLift g₀ α
    exact hα
  refine ⟨δ, ⟨hδbase, ?_⟩, ?_⟩
  · apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · exact hαeq
    · exact hβeq
  intro δ' hδ'
  rcases hδ' with ⟨hδ'base, hδ'eq⟩
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · apply hαuniq
    exact ⟨by change q.IsHomLift g₀ δ'.hom.left; exact hδ'base, by
      have := congrArg CommaMorphism.left hδ'eq
      exact this⟩
  · apply hβuniq
    have hδ'leftmap : g₀ = q.map δ'.hom.left :=
      CategoryTheory.IsHomLift.eq_of_isHomLift q g₀ δ'.hom.left
    have hδ'rightmap : gX = (F ⋙ q).map δ'.hom.right := by
      have hδ'w := congrArg q.map δ'.hom.w
      rw [← q.map_comp, ← q.map_comp, hδ'leftmap, hχmap, hζmap] at hδ'w
      simpa [gX, g, Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id] using hδ'w.symm
    have hδ'right : (F ⋙ q).IsHomLift gX δ'.hom.right := by
      have hmap : (F ⋙ q).IsHomLift ((F ⋙ q).map δ'.hom.right)
          δ'.hom.right := inferInstance
      rw [← hδ'rightmap] at hmap
      exact hmap
    exact ⟨hδ'right, by
      have := congrArg CommaMorphism.right hδ'eq
      exact this⟩

end

end ScratchAmel
