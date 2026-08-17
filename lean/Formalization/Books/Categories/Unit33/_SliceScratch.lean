import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fibered

namespace SliceScratch

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

theorem test_slice
    {X C : Type*} [Category* X] [Category* C]
    (U : C) (p : X ⥤ C) (p' : X ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p)
    (h : ∀ (x : X) (R : C) (f : R ⟶ p.obj x),
      ∃ (y : X) (ψ : y ⟶ x), Functor.IsStronglyCartesian p f ψ) :
    p'.IsFibered := by
  cases factor
  let q := p' ⋙ Over.forget U
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x R f
  obtain ⟨y, ψ, hψ⟩ := h x R.left f.left
  letI : q.IsStronglyCartesian f.left ψ := hψ
  letI : q.IsHomLift f.left ψ := by infer_instance
  have hdom : (p'.obj y).left = R.left :=
    CategoryTheory.IsHomLift.domain_eq q f.left ψ
  have hfac' : (p'.map ψ).left = eqToHom hdom ≫ f.left := by
    have h := CategoryTheory.IsHomLift.fac' q f.left ψ
    simpa [q, Category.assoc] using h
  have hobj : p'.obj y = R := by
    apply CostructuredArrow.obj_ext (p'.obj y) R hdom
    calc
      eqToHom hdom ≫ R.hom =
          eqToHom hdom ≫ f.left ≫ (p'.obj x).hom := by
            rw [Over.w f]
      _ = (p'.map ψ).left ≫ (p'.obj x).hom := by
            rw [hfac']
            simp [Category.assoc]
      _ = (p'.obj y).hom := Over.w (p'.map ψ)
  subst R
  have hmap : f.left = (p'.map ψ).left := by
    simpa using hfac'.symm
  have hf : f = p'.map ψ := by
    apply Over.OverMorphism.ext
    exact hmap
  letI : p'.IsHomLift f ψ := by
    rw [hf]
    infer_instance
  have hψ' : p'.IsStronglyCartesian f ψ := by
    constructor
    intro z g τ hτ
    letI : p'.IsHomLift (g ≫ f) τ := hτ
    have hτmap : g ≫ f = p'.map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p' (g ≫ f) τ
    have hτmap_left : (g ≫ f).left = (p'.map τ).left :=
      congrArg (fun k => k.left) hτmap
    have hτbase : g.left ≫ f.left = q.map τ := by
      simpa [q] using hτmap_left
    have hτq : q.IsHomLift (g.left ≫ f.left) τ := by
      rw [hτbase]
      exact Functor.IsHomLift.map τ
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property q f.left ψ
        g.left (g.left ≫ f.left) rfl τ
    letI : (p' ⋙ Over.forget U).IsHomLift g.left χ := hχ
    have hχmap : g.left = (p'.map χ).left := by
      change g.left = (p' ⋙ Over.forget U).map χ
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (p' ⋙ Over.forget U) z y g.left χ hχ
    have hg : g = p'.map χ := by
      apply Over.OverMorphism.ext
      exact hχmap
    letI : p'.IsHomLift g χ := by
      rw [hg]
      infer_instance
    refine ⟨χ, ⟨inferInstance, hχfac⟩, ?_⟩
    intro χ' hχ'
    rcases hχ' with ⟨hχ'base, hχ'fac⟩
    letI : p'.IsHomLift g χ' := hχ'base
    have hχ'map : g = p'.map χ' :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p' g χ'
    have hχ'map_left : g.left = (p'.map χ').left :=
      congrArg (fun k => k.left) hχ'map
    have hχ'base : g.left = q.map χ' := by
      simpa [q] using hχ'map_left
    have hχ'q : q.IsHomLift g.left χ' := by
      rw [hχ'base]
      exact Functor.IsHomLift.map χ'
    exact hχuniq χ' ⟨hχ'q, hχ'fac⟩
  exact ⟨y, ψ, hψ'⟩

end

end SliceScratch
