import Formalization.Books.Simplicial.Unit20.Augmentations
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Simplicial.Unit30.TrivialKanFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Simplicial Methods, Chapter 32: A homotopy equivalence

The source's `cosk₀(A)` is Mathlib's coskeleton of the constant simplicial
set on `A`.  The lifting and homotopy criteria below use the canonical units
of the truncation--coskeleton adjunction.  The final simplicial set is the
Čech nerve of a surjection of sets, using the established finite wide
pullback construction.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit32

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe u

/-! ## The cosk₀ construction and its associated map -/

/-- The simplicial map associated to a map of sets `f : A → B`. -/
def coskZeroMap {A B : Type u} (f : A → B) :
    Unit19.coskZero A ⟶ Unit19.coskZero B :=
  (SSet.Truncated.cosk 0).map
    ((SSet.truncation 0).map
      ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f)))

/-!
The source gives the degreewise formula for a homotopy between two maps of
`cosk₀` objects.  Mathlib's `SSet.Homotopy` is the canonical cylinder
interface for exactly this assertion; the componentwise formula is the
source-facing description of the witness supplied here.
-/

/-- Two maps between `cosk₀` simplicial sets are joined by a simplicial
homotopy. -/
theorem coskZeroMap_homotopy {A B : Type u} (f₀ f₁ : A → B) :
    Nonempty (SSet.Homotopy (coskZeroMap f₀) (coskZeroMap f₁)) := by
  open CategoryTheory.MonoidalCategory in
    let εA := (SSet.coskAdj 0).counit.app
      ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A))
    let eA : (Unit19.coskZero A).obj (op (SimplexCategory.mk 0)) → A :=
      εA.app ⟨SimplexCategory.mk 0, by simp⟩
    let h₀ : ((Unit19.coskZero A ⊗ (Δ[1] : SSet)).obj
        (op (SimplexCategory.mk 0))) → B := by
      intro x
      change (Unit19.coskZero A).obj _ × (Δ[1] : SSet).obj _ at x
      exact if SSet.stdSimplex.obj₀Equiv x.2 = 0 then
        f₀ (eA x.1) else f₁ (eA x.1)
    let X₀ : (SimplexCategory.Truncated 0)ᵒᵖ :=
      op ⟨SimplexCategory.mk 0, by simp⟩
    have hX (X : (SimplexCategory.Truncated 0)ᵒᵖ) : X = X₀ := by
      cases X with
      | op X =>
        apply congrArg Opposite.op
        apply ObjectProperty.FullSubcategory.ext
        cases X with
        | mk a ha =>
          cases a
          apply congrArg SimplexCategory.mk
          exact Nat.eq_zero_of_le_zero ha
    let S := (SSet.truncation 0).obj (Unit19.coskZero A ⊗ (Δ[1] : SSet))
    let T := (SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj B)
    let h₀' : S.obj X₀ → T.obj X₀ := h₀
    let q : S ⟶ T :=
      { app := fun X =>
          eqToHom (congrArg S.obj (hX X)) ≫ TypeCat.ofHom h₀' ≫
            eqToHom (congrArg T.obj (hX X).symm)
        naturality := by
          intro X Y g
          cases hX X
          cases hX Y
          have hg : g = 𝟙 X₀ := by
            apply Opposite.unop_injective
            apply SimplexCategory.Truncated.Hom.ext
            ext i
            dsimp [X₀] at i ⊢
            exact congrArg Fin.val (Subsingleton.elim _ _)
          rw [hg]
          simp }
    let h : (Unit19.coskZero A ⊗ (Δ[1] : SSet)) ⟶
        (SSet.Truncated.cosk 0).obj
          ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj B)) :=
      (SSet.coskAdj 0).homEquiv _ _ q
    have hε :
        ((SSet.coskAdj 0).homEquiv
          ((SSet.Truncated.cosk 0).obj
            ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A)))
          ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A))).symm
            (𝟙 ((SSet.Truncated.cosk 0).obj
              ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A)))) = εA := by
      exact (SSet.coskAdj 0).homEquiv_symm_id
        ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A))
    refine ⟨?_
      ⟩
    unfold SSet.Homotopy
    refine { h := h, h₀ := ?_, h₁ := ?_, rel := ?_ }
    · change SSet.ι₀ ≫ h = coskZeroMap f₀
      let c₀ := (SSet.truncation 0).map
        ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f₀))
      have hmap : coskZeroMap f₀ = (SSet.Truncated.cosk 0).map c₀ := by
        rfl
      rw [hmap]
      rw [← (SSet.coskAdj 0).homEquiv_naturality_left SSet.ι₀ q]
      apply ((SSet.coskAdj 0).homEquiv (Unit19.coskZero A) T).symm.injective
      simp only [Equiv.symm_apply_apply]
      have hright0 :
          ((SSet.coskAdj 0).homEquiv
            ((SSet.Truncated.cosk 0).obj
              ((SSet.truncation 0).obj
                ((SimplicialObject.const (Type u)).obj A)))
            ((SSet.truncation 0).obj
              ((SimplicialObject.const (Type u)).obj B))).symm
              ((SSet.Truncated.cosk 0).map c₀) =
            (SSet.coskAdj 0).counit.app
              ((SSet.truncation 0).obj
                ((SimplicialObject.const (Type u)).obj A)) ≫ c₀ := by
        rw [← (SSet.coskAdj 0).homEquiv_symm_id
          ((SSet.truncation 0).obj
            ((SimplicialObject.const (Type u)).obj A))]
        rw [← (SSet.coskAdj 0).homEquiv_naturality_right_symm
          (𝟙 ((SSet.Truncated.cosk 0).obj
            ((SSet.truncation 0).obj
              ((SimplicialObject.const (Type u)).obj A)))) c₀]
        simp
      change (SSet.truncation 0).map SSet.ι₀ ≫ q =
        ((SSet.coskAdj 0).homEquiv
            ((SSet.Truncated.cosk 0).obj
            ((SSet.truncation 0).obj
              ((SimplicialObject.const (Type u)).obj A)))
          ((SSet.truncation 0).obj
            ((SimplicialObject.const (Type u)).obj B))).symm
          ((SSet.Truncated.cosk 0).map c₀)
      rw [hright0]
      apply SSet.Truncated.hom_ext
      intro d
      cases hX d
      ext x
      change
        (if (SSet.ι₀.app (op (SimplexCategory.mk 0)) x).2 0 = 0 then
            f₀ (eA (SSet.ι₀.app (op (SimplexCategory.mk 0)) x).1)
          else f₁ (eA (SSet.ι₀.app (op (SimplexCategory.mk 0)) x).1)) =
        f₀ (eA x)
      have hfst := SSet.ι₀_app_fst (X := Unit19.coskZero A) x
      have hsnd := SSet.ι₀_app_snd_apply (X := Unit19.coskZero A) x (0 : Fin 1)
      have hfst' :
          ((ConcreteCategory.hom
            (SSet.ι₀.app (op (SimplexCategory.mk 0)))) x).1 = x := by
        simpa [X₀] using hfst
      simp only [hfst']
      exact if_pos hsnd
    · change SSet.ι₁ ≫ h = coskZeroMap f₁
      let c₁ := (SSet.truncation 0).map
        ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f₁))
      have hmap : coskZeroMap f₁ = (SSet.Truncated.cosk 0).map c₁ := by
        rfl
      rw [hmap]
      rw [← (SSet.coskAdj 0).homEquiv_naturality_left SSet.ι₁ q]
      apply ((SSet.coskAdj 0).homEquiv (Unit19.coskZero A) T).symm.injective
      simp only [Equiv.symm_apply_apply]
      have hright0 :
          ((SSet.coskAdj 0).homEquiv
            ((SSet.Truncated.cosk 0).obj
              ((SSet.truncation 0).obj
                ((SimplicialObject.const (Type u)).obj A)))
            ((SSet.truncation 0).obj
              ((SimplicialObject.const (Type u)).obj B))).symm
              ((SSet.Truncated.cosk 0).map c₁) =
            (SSet.coskAdj 0).counit.app
              ((SSet.truncation 0).obj
                ((SimplicialObject.const (Type u)).obj A)) ≫ c₁ := by
        rw [← (SSet.coskAdj 0).homEquiv_symm_id
          ((SSet.truncation 0).obj
            ((SimplicialObject.const (Type u)).obj A))]
        rw [← (SSet.coskAdj 0).homEquiv_naturality_right_symm
          (𝟙 ((SSet.Truncated.cosk 0).obj
            ((SSet.truncation 0).obj
              ((SimplicialObject.const (Type u)).obj A)))) c₁]
        simp
      change (SSet.truncation 0).map SSet.ι₁ ≫ q =
        ((SSet.coskAdj 0).homEquiv
            ((SSet.Truncated.cosk 0).obj
              ((SSet.truncation 0).obj
                ((SimplicialObject.const (Type u)).obj A)))
          ((SSet.truncation 0).obj
            ((SimplicialObject.const (Type u)).obj B))).symm
          ((SSet.Truncated.cosk 0).map c₁)
      rw [hright0]
      apply SSet.Truncated.hom_ext
      intro d
      cases hX d
      ext x
      change
        (if (SSet.ι₁.app (op (SimplexCategory.mk 0)) x).2 0 = 0 then
            f₀ (eA (SSet.ι₁.app (op (SimplexCategory.mk 0)) x).1)
          else f₁ (eA (SSet.ι₁.app (op (SimplexCategory.mk 0)) x).1)) =
        f₁ (eA x)
      have hfst := SSet.ι₁_app_fst (X := Unit19.coskZero A) x
      have hsnd := SSet.ι₁_app_snd_apply (X := Unit19.coskZero A) x (0 : Fin 1)
      have hfst' :
          ((ConcreteCategory.hom
            (SSet.ι₁.app (op (SimplexCategory.mk 0)))) x).1 = x := by
        simpa [X₀] using hfst
      simp only [hfst']
      apply if_neg
      intro hzero
      have h01 : (0 : Fin 2) = 1 := hzero.symm.trans hsnd
      exact Fin.zero_ne_one h01
    · ext m x
      exact x.1.property.elim

/-- The degree-zero example gives the homotopy relation used in Chapter 26. -/
theorem coskZeroMap_homotopic {A B : Type u} (f₀ f₁ : A → B) :
    Unit26.Homotopic (coskZeroMap f₀) (coskZeroMap f₁) := by
  rcases coskZeroMap_homotopy f₀ f₁ with ⟨H⟩
  exact Unit26.homotopicOfHomotopy
    (SSet.Homotopy.toSimplicialObjectHomotopy H)

private lemma boundaryTruncationMap_isIso (n k : ℕ) (h : n < k) :
    IsIso ((SSet.truncation n).map (SSet.boundary k).ι) := by
  let g := (SSet.truncation n).map (SSet.boundary k).ι
  have h_apps : ∀ X, IsIso (g.app X) := by
    intro X
    cases X with
    | op X =>
      cases X with
      | mk X hX =>
        cases X with
        | mk i =>
          apply (CategoryTheory.isIso_iff_bijective _).2
          change Function.Bijective (fun x : (SSet.boundary k).obj (op ⦋i⦌) =>
            ((SSet.boundary k).ι.app (op ⦋i⦌)) x)
          constructor
          · intro x y hxy
            exact Subtype.ext hxy
          · intro y
            have hy : y ∈ (SSet.boundary k).obj (op ⦋i⦌) := by
              rw [SSet.boundary_obj_eq_univ i k (lt_of_le_of_lt hX h)]
              exact Set.mem_univ y
            exact ⟨⟨y, hy⟩, rfl⟩
  exact (CategoryTheory.NatTrans.isIso_iff_isIso_app g).2 h_apps

private lemma coskeletal_extension {X : SSet.{u}} (n k : ℕ) (h : n < k)
    (hX : IsIso ((SSet.coskAdj n).unit.app X))
    (a : (∂Δ[k] : SSet.{u}) ⟶ X) :
    ∃ l : (Δ[k] : SSet.{u}) ⟶ X, (SSet.boundary k).ι ≫ l = a := by
  letI : IsIso ((SSet.coskAdj n).unit.app X) := hX
  let i := (SSet.truncation n).map (SSet.boundary k).ι
  haveI : IsIso i := boundaryTruncationMap_isIso n k h
  let q : (SSet.truncation n).obj (Δ[k] : SSet.{u}) ⟶
      (SSet.truncation n).obj X :=
    inv i ≫ (SSet.truncation n).map a
  let l' : (Δ[k] : SSet.{u}) ⟶
      (SSet.Truncated.cosk n).obj ((SSet.truncation n).obj X) :=
    (SSet.coskAdj n).homEquiv _ _ q
  let l : (Δ[k] : SSet.{u}) ⟶ X :=
    l' ≫ inv ((SSet.coskAdj n).unit.app X)
  refine ⟨l, ?_⟩
  apply (cancel_mono ((SSet.coskAdj n).unit.app X)).1
  simp [l, Category.assoc]
  dsimp [l']
  refine ((SSet.coskAdj n).homEquiv
    (∂Δ[k] : SSet.{u}) ((SSet.truncation n).obj X)).symm.injective ?_
  rw [(SSet.coskAdj n).homEquiv_naturality_left_symm
    (SSet.boundary k).ι
    (((SSet.coskAdj n).homEquiv (Δ[k] : SSet.{u})
      ((SSet.truncation n).obj X)) q)]
  rw [(SSet.coskAdj n).homEquiv_naturality_left_symm a
    ((SSet.coskAdj n).unit.app X)]
  simp [q, i]

private lemma coskeletal_boundary_mono {X : SSet.{u}} (n k : ℕ) (h : n < k)
    (hX : IsIso ((SSet.coskAdj n).unit.app X))
    {p q : (Δ[k] : SSet.{u}) ⟶ X}
    (hpq : (SSet.boundary k).ι ≫ p = (SSet.boundary k).ι ≫ q) : p = q := by
  letI : IsIso ((SSet.coskAdj n).unit.app X) := hX
  let i := (SSet.truncation n).map (SSet.boundary k).ι
  haveI : IsIso i := boundaryTruncationMap_isIso n k h
  apply (cancel_mono ((SSet.coskAdj n).unit.app X)).1
  let e := (SSet.coskAdj n).homEquiv
    (Δ[k] : SSet.{u}) ((SSet.truncation n).obj X)
  have hp : e ((SSet.truncation n).map p) =
      p ≫ (SSet.coskAdj n).unit.app X := by
    apply (Equiv.apply_eq_iff_eq_symm_apply e).2
    rw [(SSet.coskAdj n).homEquiv_naturality_left_symm p
      ((SSet.coskAdj n).unit.app X)]
    simp
  have hq : e ((SSet.truncation n).map q) =
      q ≫ (SSet.coskAdj n).unit.app X := by
    apply (Equiv.apply_eq_iff_eq_symm_apply e).2
    rw [(SSet.coskAdj n).homEquiv_naturality_left_symm q
      ((SSet.coskAdj n).unit.app X)]
    simp
  rw [← hp, ← hq]
  rw [e.apply_eq_iff_eq]
  apply (cancel_epi i).1
  simpa [i, Category.assoc] using
    congrArg (fun z => (SSet.truncation n).map z) hpq

private lemma boundary_map_ext {X Y : SSet.{u}} (k : ℕ) (g : X ⟶ Y)
    (hg : ∀ i : ℕ, i < k →
      Function.Injective (g.app (op (SimplexCategory.mk i))))
    {p q : (∂Δ[k] : SSet.{u}) ⟶ X}
    (hpq : p ≫ g = q ≫ g) : p = q := by
  apply SSet.hom_ext
  intro m
  cases m with
  | op m =>
    cases m with
    | mk m =>
      induction m using Nat.strong_induction_on with
      | h m ih =>
        ext x
        by_cases hm : m < k
        · apply hg m hm
          exact ConcreteCategory.congr_hom
            (congr_app hpq (op (SimplexCategory.mk m))) x
        · obtain ⟨r, α, hα, y, hy⟩ :=
            (∂Δ[k] : SSet.{u}).exists_nonDegenerate x
          have hr : r < k :=
            (∂Δ[k] : SSet.{u}).dim_lt_of_nonDegenerate y k
          have hrm : r < m := lt_of_lt_of_le hr (Nat.le_of_not_gt hm)
          have hy' : p.app (op (SimplexCategory.mk r)) y =
              q.app (op (SimplexCategory.mk r)) y :=
            ConcreteCategory.congr_hom (ih r hrm) y
          rw [hy]
          have hp :
              p.app (op (SimplexCategory.mk m))
                  ((∂Δ[k] : SSet.{u}).map α.op y) =
                X.map α.op (p.app (op (SimplexCategory.mk r)) y) := by
            simpa only [CategoryTheory.comp_apply] using
              ConcreteCategory.congr_hom (p.naturality α.op) y
          have hq :
              q.app (op (SimplexCategory.mk m))
                  ((∂Δ[k] : SSet.{u}).map α.op y) =
                X.map α.op (q.app (op (SimplexCategory.mk r)) y) := by
            simpa only [CategoryTheory.comp_apply] using
              ConcreteCategory.congr_hom (q.naturality α.op) y
          have hmid :
              X.map α.op (p.app (op (SimplexCategory.mk r)) y) =
                X.map α.op (q.app (op (SimplexCategory.mk r)) y) :=
            congrArg (fun z => X.map α.op z) hy'
          exact hp.trans hmid |>.trans hq.symm

/-- If a map is bijective below degree `n`, surjective in degree `n`, and
both simplicial sets are `n`-coskeletal, then it is a trivial Kan fibration.
-/
theorem section_lemma {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (h_bijective : ∀ i : ℕ, i < n →
      Function.Bijective (f.app (op (SimplexCategory.mk i))))
    (h_surjective : Function.Surjective
      (f.app (op (SimplexCategory.mk n))))
    (hU : IsIso ((SSet.coskAdj n).unit.app U))
    (hV : IsIso ((SSet.coskAdj n).unit.app V)) :
    Unit30.TrivialKanFibration f := by
  constructor
  · by_cases hn : n = 0
    · subst n
      exact h_surjective
    · exact (h_bijective 0 (Nat.pos_of_ne_zero hn)).2
  · intro k hk a b comm
    by_cases hkn : k ≤ n
    · have htop : Function.Surjective
          (f.app (op (SimplexCategory.mk k))) := by
        rcases Nat.lt_or_eq_of_le hkn with hkn' | rfl
        · exact (h_bijective k hkn').2
        · exact h_surjective
      obtain ⟨y, hy⟩ := htop (SSet.yonedaEquiv b)
      let l := SSet.yonedaEquiv.symm y
      have hl₂ : l ≫ f = b := by
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp]
        simpa [l] using hy
      refine ⟨l, ?_, hl₂⟩
      apply boundary_map_ext k f
      · intro i hi
        exact (h_bijective i (lt_of_lt_of_le hi hkn)).1
      · simpa [Category.assoc, hl₂] using comm.symm
    · have hnk : n < k := lt_of_not_ge hkn
      obtain ⟨l, hl⟩ := coskeletal_extension n k hnk hV a
      refine ⟨l, hl, ?_⟩
      apply coskeletal_boundary_mono n k hnk hU
      rw [← Category.assoc, hl]
      exact comm

/-- The degree-zero case of `section_lemma` for a surjective map of sets. -/
theorem coskZeroMap_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskZeroMap f) := by
  let c := (SSet.truncation 0).map
    ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))
  let εA := (SSet.coskAdj 0).counit.app
    ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A))
  let εB := (SSet.coskAdj 0).counit.app
    ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj B))
  let z : (SimplexCategory.Truncated 0)ᵒᵖ :=
    ⟨SimplexCategory.mk 0, by simp⟩
  haveI : IsIso (εA.app z) := by
    dsimp [εA]
    infer_instance
  haveI : IsIso (εB.app z) := by
    dsimp [εB]
    infer_instance
  have hzero : Function.Surjective
      ((coskZeroMap f).app (op (SimplexCategory.mk 0))) := by
    intro y
    let b := εB.app z y
    obtain ⟨a, ha⟩ := hf b
    let x := inv (εA.app z) a
    refine ⟨x, ?_⟩
    apply ((CategoryTheory.isIso_iff_bijective
      (εB.app z)).1 inferInstance).1
    have hn' : εB.app z ((coskZeroMap f).app
        (op (SimplexCategory.mk 0)) x) = f a := by
      have hεA : εA.app z x = a := by
        dsimp [x]
        exact ConcreteCategory.congr_hom
          (IsIso.inv_hom_id (εA.app z)) a
      rw [← hεA]
      change (εB.app z) ((coskZeroMap f).app
          (op (SimplexCategory.mk 0)) x) = (c.app z) (εA.app z x)
      have hn₀ : ((SSet.truncation 0).map
          ((SSet.Truncated.cosk 0).map c)).app z ≫ εB.app z =
          εA.app z ≫ c.app z := by
        exact congr_app ((SSet.coskAdj 0).counit.naturality c) z
      have hn := ConcreteCategory.congr_hom hn₀ x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
      
    simpa [b] using hn'.trans ha
  apply section_lemma (coskZeroMap f) 0
  · intro i hi
    omega
  · simpa [coskZeroMap, c] using hzero
  · change IsIso ((SSet.coskAdj 0).unit.app
      ((SSet.Truncated.cosk 0).obj ((SSet.truncation 0).obj
        ((SimplicialObject.const (Type u)).obj B))))
    infer_instance
  · change IsIso ((SSet.coskAdj 0).unit.app
      ((SSet.Truncated.cosk 0).obj ((SSet.truncation 0).obj
        ((SimplicialObject.const (Type u)).obj A))))
    infer_instance

/-! ## Homotopy from agreement below the coskeleton degree -/

/-- Maps agreeing below degree `n` are homotopic when both simplicial sets are
`n`-coskeletal. -/
theorem homotopy_lemma {V U : SSet.{u}} (f₀ f₁ : V ⟶ U) (n : ℕ)
    (h_equal : ∀ i : ℕ, i < n →
      f₀.app (op (SimplexCategory.mk i)) =
        f₁.app (op (SimplexCategory.mk i)))
    (hU : IsIso ((SSet.coskAdj n).unit.app U))
    (hV : IsIso ((SSet.coskAdj n).unit.app V)) :
    Unit26.Homotopic f₀ f₁ := by
  let f₀' := (SSet.truncation n).map f₀
  let f₁' := (SSet.truncation n).map f₁
  let Q := coequalizer f₀' f₁'
  let q := coequalizer.π f₀' f₁'
  let W := (SSet.Truncated.cosk n).obj Q
  let g : U ⟶ W := (SSet.coskAdj n).homEquiv _ _ q
  have hqg :
      (SSet.truncation n).map g ≫ (SSet.coskAdj n).counit.app Q = q := by
    change ((SSet.coskAdj n).homEquiv U Q).symm g = q
    exact ((SSet.coskAdj n).homEquiv U Q).symm_apply_apply q
  have hW : IsIso ((SSet.coskAdj n).unit.app W) := by
    infer_instance
  have hg_low : ∀ i : ℕ, i < n →
      Function.Bijective (g.app (op (SimplexCategory.mk i))) := by
    intro i hi
    let z : (SimplexCategory.Truncated n)ᵒᵖ :=
      op ⟨SimplexCategory.mk i, by simpa using hi.le⟩
    have hz := congr_app hqg z
    simp only [NatTrans.comp_app] at hz
    rw [Unit12.truncation_map_app] at hz
    change g.app (op (SimplexCategory.mk i)) ≫
        ((SSet.coskAdj n).counit.app Q).app z = q.app z at hz
    have hqz : f₀'.app z = f₁'.app z := by
      change f₀.app (op (SimplexCategory.mk i)) =
        f₁.app (op (SimplexCategory.mk i))
      exact h_equal i hi
    let e := (evaluation (SimplexCategory.Truncated n)ᵒᵖ (Type u)).obj z
    let F := parallelPair f₀' f₁' ⋙ e
    let c := e.mapCocone
      (Cofork.ofπ (coequalizer.π f₀' f₁') (coequalizer.condition f₀' f₁'))
    have hcolim : IsColimit c := isColimitOfPreserves e
      (coequalizerIsCoequalizer f₀' f₁')
    have hleft : F.map WalkingParallelPairHom.left =
        F.map WalkingParallelPairHom.right := by
      change f₀'.app z = f₁'.app z
      exact hqz
    let d : Cocone F := {
      pt := F.obj WalkingParallelPair.one
      ι := {
        app := fun j =>
          match j with
          | .zero => F.map WalkingParallelPairHom.left
          | .one => 𝟙 _
        naturality := by
          rintro (_ | _) (_ | _) (_ | _)
          all_goals simp_all
      }
    }
    let l := hcolim.desc d
    have hlq : c.ι.app WalkingParallelPair.one ≫ l =
        𝟙 (F.obj WalkingParallelPair.one) := by
      simpa [d, l] using hcolim.fac d WalkingParallelPair.one
    haveI : Epi (c.ι.app WalkingParallelPair.one) := by
      change Epi (q.app z)
      exact (NatTrans.epi_iff_epi_app q).1 (inferInstance : Epi q) z
    have hql : l ≫ c.ι.app WalkingParallelPair.one =
        𝟙 c.pt := by
      apply (cancel_epi (c.ι.app WalkingParallelPair.one)).1
      rw [← Category.assoc, hlq]
      calc
        𝟙 (F.obj WalkingParallelPair.one) ≫ c.ι.app WalkingParallelPair.one =
            c.ι.app WalkingParallelPair.one := Category.id_comp _
        _ = c.ι.app WalkingParallelPair.one ≫ 𝟙 c.pt :=
          (Category.comp_id _).symm
    have hqi : IsIso (c.ι.app WalkingParallelPair.one) :=
      IsIso.mk ⟨l, hlq, hql⟩
    have hqiso : IsIso (q.app z) := by
      change IsIso (e.map q)
      exact hqi
    have hcounit : IsIso (SSet.coskAdj n).counit := inferInstance
    have hco : IsIso ((SSet.coskAdj n).counit.app Q) :=
      (CategoryTheory.NatTrans.isIso_iff_isIso_app
        (SSet.coskAdj n).counit).1 hcounit Q
    have hcomp : IsIso (((SSet.coskAdj n).counit.app Q).app z) :=
      (CategoryTheory.NatTrans.isIso_iff_isIso_app
        ((SSet.coskAdj n).counit.app Q)).1 hco z
    have hgi : IsIso (g.app (op (SimplexCategory.mk i))) := by
      letI : IsIso (((SSet.coskAdj n).counit.app Q).app z) := hcomp
      have hcompg : IsIso
          (g.app (op (SimplexCategory.mk i)) ≫
            ((SSet.coskAdj n).counit.app Q).app z) := by
        rw [hz]
        exact hqiso
      letI : IsIso
          (g.app (op (SimplexCategory.mk i)) ≫
            ((SSet.coskAdj n).counit.app Q).app z) := hcompg
      exact @IsIso.of_isIso_comp_right _ _ _ _ _
        (g.app (op (SimplexCategory.mk i)))
        (((SSet.coskAdj n).counit.app Q).app z) hcomp hcompg
    letI : IsIso (g.app (op (SimplexCategory.mk i))) := hgi
    exact (CategoryTheory.isIso_iff_bijective
      (g.app (op (SimplexCategory.mk i)))).1 inferInstance
  have hg_top : Function.Surjective
      (g.app (op (SimplexCategory.mk n))) := by
    let z : (SimplexCategory.Truncated n)ᵒᵖ :=
      op ⟨SimplexCategory.mk n, le_rfl⟩
    have hz := congr_app hqg z
    simp only [NatTrans.comp_app] at hz
    rw [Unit12.truncation_map_app] at hz
    change g.app (op (SimplexCategory.mk n)) ≫
        ((SSet.coskAdj n).counit.app Q).app z = q.app z at hz
    haveI : Epi (q.app z) := by
      exact (NatTrans.epi_iff_epi_app q).1 (inferInstance : Epi q) z
    have hqepi : Epi
        (g.app (op (SimplexCategory.mk n)) ≫
          ((SSet.coskAdj n).counit.app Q).app z) := by
      rw [hz]
      exact (NatTrans.epi_iff_epi_app q).1 (inferInstance : Epi q) z
    have hcounit : IsIso (SSet.coskAdj n).counit := inferInstance
    have hco : IsIso ((SSet.coskAdj n).counit.app Q) :=
      (CategoryTheory.NatTrans.isIso_iff_isIso_app
        (SSet.coskAdj n).counit).1 hcounit Q
    have hcomp : IsIso (((SSet.coskAdj n).counit.app Q).app z) :=
      (CategoryTheory.NatTrans.isIso_iff_isIso_app
        ((SSet.coskAdj n).counit.app Q)).1 hco z
    letI : IsIso (((SSet.coskAdj n).counit.app Q).app z) := hcomp
    haveI : Epi (g.app (op (SimplexCategory.mk n))) := by
      exact (@epi_comp_iff_of_isIso _ _ _ _ _
        (g.app (op (SimplexCategory.mk n)))
        (((SSet.coskAdj n).counit.app Q).app z) hcomp).1 hqepi
    rw [← epi_iff_surjective]
    infer_instance
  have hg : Unit30.TrivialKanFibration g := by
    apply section_lemma g n hg_low hg_top
    · exact hW
    · exact hU
  let K : SSet := (SimplicialObject.const (Type u)).obj (ULift (Fin 2))
  let hconst : Unit13.FiniteNonemptySimplicialSet K := by
    intro m
    dsimp [K]
    exact ⟨inferInstance, inferInstance⟩
  let hJ : Unit13.HasDegreewiseCoproducts K V :=
    Unit13.degreewiseCoproductInstance K V hconst
  let J : SSet := Unit13.simplicialSetProductOf K V hJ
  let hI := Unit26.intervalCoproducts V
  let i : J ⟶ Unit26.intervalCylinder V := {
    app := fun X =>
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      Sigma.map' (fun ε : ULift (Fin 2) =>
        SSet.stdSimplex.const 1 ε.down X) (fun _ => 𝟙 (V.obj X))
    naturality := by
      intro X Y φ
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      let _ := Unit13.degreewiseCoproductInstanceAt hI X
      let _ := Unit13.degreewiseCoproductInstanceAt hI Y
      dsimp [Unit26.intervalCylinder, J,
        Unit13.simplicialSetProductOf, Sigma.map']
      apply Sigma.hom_ext
      intro ε
      have hK : K.map φ = 𝟙 _ := by rfl
      rw [hK]
      have hK' (u : K.obj X) :
          (ConcreteCategory.hom (𝟙 (K.obj X))) u = u := by rfl
      simp only [hK']
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
      let _ := Unit13.degreewiseCoproductInstanceAt hI X
      let _ := Unit13.degreewiseCoproductInstanceAt hI Y
      simp only [Category.assoc, Sigma.ι_desc, Category.id_comp]
      have hε :
          (Δ[1] : SSet).map φ
              (SSet.stdSimplex.const 1 ε.down X) =
            SSet.stdSimplex.const 1 ε.down Y := by
        apply SSet.stdSimplex.objEquiv.injective
        apply SimplexCategory.Hom.ext
        rfl
      rw [hε] }
  have hk : ∀ X : SimplexCategoryᵒᵖ,
      Function.Injective (fun ε : ULift (Fin 2) =>
        SSet.stdSimplex.const 1 ε.down X) := by
    intro X ε₁ ε₂ hε
    apply ULift.ext
    apply Fin.ext
    have h0 := congrArg (fun z => z.down.toOrderHom 0) hε
    change ε₁.down = ε₂.down at h0
    exact congrArg Fin.val h0
  have hi : Unit30.TermwiseInjective i := by
    intro m
    have hm : Mono (i.app (op (SimplexCategory.mk m))) := by
      dsimp [i]
      apply CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective
      exact hk _
    rw [mono_iff_injective] at hm
    exact hm
  let j₀ : V ⟶ J := {
    app := fun X =>
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      Sigma.ι (fun _ : ULift (Fin 2) => V.obj X) (ULift.up 0)
    naturality := by
      intro X Y φ
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      dsimp [J, Unit13.simplicialSetProductOf]
      rw [Sigma.ι_desc]
      have hK : K.map φ = 𝟙 _ := by rfl
      rw [hK]
      rfl }
  let j₁ : V ⟶ J := {
    app := fun X =>
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      Sigma.ι (fun _ : ULift (Fin 2) => V.obj X) (ULift.up 1)
    naturality := by
      intro X Y φ
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      dsimp [J, Unit13.simplicialSetProductOf]
      rw [Sigma.ι_desc]
      have hK : K.map φ = 𝟙 _ := by rfl
      rw [hK]
      rfl }
  let a : J ⟶ U := {
    app := fun X =>
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      Sigma.desc (fun ε : ULift (Fin 2) =>
        if ε.down = 0 then f₀.app X else f₁.app X)
    naturality := by
      intro X Y φ
      let _ := Unit13.degreewiseCoproductInstanceAt hJ X
      let _ := Unit13.degreewiseCoproductInstanceAt hJ Y
      dsimp [J, Unit13.simplicialSetProductOf]
      apply Sigma.hom_ext
      intro ε
      simp only [← Category.assoc, Sigma.ι_desc]
      have hK : K.map φ = 𝟙 _ := by rfl
      rw [hK]
      have hKε : (ConcreteCategory.hom (𝟙 (K.obj X))) ε = ε := by rfl
      rw [hKε]
      change
        V.map φ ≫
            (Sigma.ι (fun _ : ULift (Fin 2) => V.obj Y) ε ≫
              Sigma.desc (fun ε : ULift (Fin 2) =>
                if ε.down = 0 then f₀.app Y else f₁.app Y)) =
          (if ε.down = 0 then f₀.app X else f₁.app X) ≫ U.map φ
      rw [Sigma.ι_desc]
      by_cases hε : ε.down = 0
      · simp only [hε, ↓reduceIte]
        exact f₀.naturality φ
      · simp only [hε, ↓reduceIte]
        exact f₁.naturality φ }
  have ha0 : j₀ ≫ a = f₀ := by
    apply NatTrans.ext
    funext X
    let _ := Unit13.degreewiseCoproductInstanceAt hJ X
    dsimp [j₀, a, J, Unit13.simplicialSetProductOf]
    change Sigma.ι (fun _ : ULift (Fin 2) => V.obj X) (ULift.up 0) ≫
      Sigma.desc (fun ε : ULift (Fin 2) =>
        if ε.down = 0 then f₀.app X else f₁.app X) = f₀.app X
    rw [Sigma.ι_desc]
    rfl
  have ha1 : j₁ ≫ a = f₁ := by
    apply NatTrans.ext
    funext X
    let _ := Unit13.degreewiseCoproductInstanceAt hJ X
    dsimp [j₁, a, J, Unit13.simplicialSetProductOf]
    change Sigma.ι (fun _ : ULift (Fin 2) => V.obj X) (ULift.up 1) ≫
      Sigma.desc (fun ε : ULift (Fin 2) =>
        if ε.down = 0 then f₀.app X else f₁.app X) = f₁.app X
    rw [Sigma.ι_desc]
    simp
  have hji0 : j₀ ≫ i = Unit26.homotopyE₀ V := by
    apply NatTrans.ext
    funext X
    let _ := Unit13.degreewiseCoproductInstanceAt hJ X
    dsimp [j₀, i, J, Unit26.intervalCylinder,
      Unit13.simplicialSetProductOf, Sigma.map']
    simp only [Sigma.ι_desc, Category.assoc, Category.id_comp]
    rfl
  have hji1 : j₁ ≫ i = Unit26.homotopyE₁ V := by
    apply NatTrans.ext
    funext X
    let _ := Unit13.degreewiseCoproductInstanceAt hJ X
    dsimp [j₁, i, J, Unit26.intervalCylinder,
      Unit13.simplicialSetProductOf, Sigma.map']
    simp only [Sigma.ι_desc, Category.assoc, Category.id_comp]
    rfl
  have hfg : f₀ ≫ g = f₁ ≫ g := by
    apply ((SSet.coskAdj n).homEquiv V Q).symm.injective
    rw [← (SSet.coskAdj n).homEquiv_naturality_left f₀ q,
      ← (SSet.coskAdj n).homEquiv_naturality_left f₁ q]
    simpa [f₀', f₁'] using coequalizer.condition f₀' f₁'
  let b : Unit26.intervalCylinder V ⟶ W :=
    Unit26.intervalProjection V ≫ (f₀ ≫ g)
  have comm : a ≫ g = i ≫ b := by
    apply NatTrans.ext
    funext X
    let _ := Unit13.degreewiseCoproductInstanceAt hJ X
    dsimp [a, i, b, J, Unit26.intervalCylinder,
      Unit13.simplicialSetProductOf, Sigma.map']
    apply Sigma.hom_ext
    intro ε
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
    simp only [Category.id_comp]
    change
      (if ε.down = 0 then f₀.app X else f₁.app X) ≫ g.app X =
        Sigma.ι (fun _ : (Δ[1] : SSet).obj X => V.obj X)
            (SSet.stdSimplex.const 1 ε.down X) ≫
          (Unit26.intervalProjection V).app X ≫
            (f₀.app X ≫ g.app X)
    by_cases hε : ε.down = 0
    · simp only [hε, ↓reduceIte]
      have hp := congr_app (Unit26.intervalProjection_comp_endpoint V).1 X
      simpa [Unit26.homotopyE₀, Unit26.intervalEndpoint,
        Unit26.intervalProjection, Unit13.productWithSimplicialSetTo_app,
        Category.assoc] using congrArg
          (fun z => z ≫ (f₀.app X ≫ g.app X)) hp
    · have hε1 : ε.down = 1 := by omega
      simp only [hε, ↓reduceIte, hε1]
      have hp := congr_app (Unit26.intervalProjection_comp_endpoint V).2 X
      calc
        f₁.app X ≫ g.app X = f₀.app X ≫ g.app X := by
          simpa only [NatTrans.comp_app] using (congr_app hfg X).symm
        _ = Sigma.ι (fun _ : (Δ[1] : SSet).obj X => V.obj X)
              (SSet.stdSimplex.const 1 1 X) ≫
            (Unit26.intervalProjection V).app X ≫
              (f₀.app X ≫ g.app X) := by
          simpa [Unit26.homotopyE₁, Unit26.intervalEndpoint,
            Unit26.intervalProjection,
            Unit13.productWithSimplicialSetTo_app, Category.assoc] using
            (congrArg (fun z => z ≫ (f₀.app X ≫ g.app X)) hp).symm
  obtain ⟨l, hl_i, hl_g⟩ :=
    Unit30.trivialKanFibration_lift g hg i hi a b comm
  have hcyl : Nonempty (Unit26.CylinderHomotopy f₀ f₁) := by
    refine ⟨{ h := l, h₀ := ?_, h₁ := ?_ }⟩
    · rw [← hji0, Category.assoc, hl_i, ha0]
    · rw [← hji1, Category.assoc, hl_i, ha1]
  exact Relation.EqvGen.rel _ _ ((Unit26.homotopy_iff_degreewise).1 hcyl)

/-! ## The `cosk₋₁` Čech nerve -/

/-- The wide pullbacks needed for the Čech nerve of a map of types. -/
theorem hasCechNerveOfFunction {A B : Type u} (f : A → B) :
    Unit20.HasCechNerve (C := Type u) (TypeCat.ofHom f) := by
  intro n
  infer_instance

/-- The simplicial set with degree `n` given by the `(n+1)`-fold fibre
product of `A` over `B`. -/
noncomputable def coskMinusOne {A B : Type u} (f : A → B) : SSet.{u} :=
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  (Arrow.mk (TypeCat.ofHom f)).cechNerve

/-- The canonical augmentation of the Čech nerve to the constant simplicial
set on `B`. -/
noncomputable def coskMinusOneAugmentation {A B : Type u} (f : A → B) :
    coskMinusOne f ⟶ (SimplicialObject.const (Type u)).obj B := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  exact (Arrow.mk (TypeCat.ofHom f)).augmentedCechNerve.hom

private noncomputable def cechNerve_lift_of_zero {A B : Type u} (f : A → B)
    (hwp : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f))
    {T : SSet.{u}} (a : T ⟶ (SimplicialObject.const (Type u)).obj B)
    (g₀ : T.obj (op (SimplexCategory.mk 0)) ⟶ A)
    (hg₀ : g₀ ≫ TypeCat.ofHom f = a.app (op (SimplexCategory.mk 0))) :
    T ⟶ coskMinusOne f := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hwp
  let F : Arrow (Type u) := Arrow.mk (TypeCat.ofHom f)
  let app (X : (SimplexCategoryᵒᵖ)) : T.obj X ⟶
      (F.cechNerve).obj X := by
    refine WidePullback.lift (a.app X) (fun i => ?_) ?_
    · exact T.map (SimplexCategory.const (SimplexCategory.mk 0)
        X.unop i).op ≫ g₀
    · intro i
      have hi := a.naturality
        (SimplexCategory.const (SimplexCategory.mk 0) X.unop i).op
      rw [← hg₀] at hi
      simpa [F, Arrow.mk] using hi
  have naturality : ∀ {X Y : SimplexCategoryᵒᵖ} (q : X ⟶ Y),
      T.map q ≫ app Y = app X ≫ F.cechNerve.map q := by
    intro X Y q
    dsimp [app]
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp only [Category.assoc, WidePullback.lift_π]
      rw [← T.map_comp_assoc, ← Quiver.Hom.op_unop q, ← op_comp,
        SimplexCategory.const_comp]
      simp only [Quiver.Hom.unop_op]
    · simp only [Category.assoc, WidePullback.lift_base]
      simp
  change T ⟶ F.cechNerve
  refine { app := app, naturality := ?_ }
  intro X Y q
  exact naturality q

/-- The Čech nerve is the pullback of `cosk₀(A)` along the canonical map
from the constant simplicial set on `B`. -/
theorem coskMinusOne_isPullback {A B : Type u} (f : A → B) :
    ∃ top : coskMinusOne f ⟶ Unit19.coskZero A,
      IsPullback top (coskMinusOneAugmentation f)
        (coskZeroMap f)
        ((SSet.coskAdj 0).unit.app ((SimplicialObject.const (Type u)).obj B)) := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  let F : Arrow (Type u) := Arrow.mk (TypeCat.ofHom f)
  let C : SSet.{u} := coskMinusOne f
  let ε : C ⟶ (SimplicialObject.const (Type u)).obj B :=
    coskMinusOneAugmentation f
  let u := (SSet.coskAdj 0).unit.app
    ((SimplicialObject.const (Type u)).obj B)
  let εA := (SSet.coskAdj 0).counit.app
    ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj A))
  let εB := (SSet.coskAdj 0).counit.app
    ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj B))
  let S := (SSet.truncation 0).obj C
  let T := (SSet.truncation 0).obj
    ((SimplicialObject.const (Type u)).obj A)
  let z₀ : SimplexCategory.Truncated 0 :=
    ⟨SimplexCategory.mk 0, by simp⟩
  let z : (SimplexCategory.Truncated 0)ᵒᵖ := op z₀
  let p₀' : C.obj (op z₀.obj) ⟶ A := by
    dsimp [C, coskMinusOne]
    exact WidePullback.π (fun _ : Fin (0 + 1) => F.hom) 0
  have hS : S.obj z = C.obj (op z₀.obj) := by rfl
  have hT : T.obj z = A := by rfl
  let p₀ : S.obj z ⟶ T.obj z := by
    exact eqToHom hS ≫ p₀' ≫ eqToHom hT.symm
  let eT : T.obj z ⟶ A := by
    exact eqToHom hT
  have hX (X : (SimplexCategory.Truncated 0)ᵒᵖ) : X = z := by
    cases X with
    | op X =>
      apply congrArg Opposite.op
      apply ObjectProperty.FullSubcategory.ext
      cases X with
      | mk a ha =>
        cases a
        apply congrArg SimplexCategory.mk
        exact Nat.eq_zero_of_le_zero ha
  let p : S ⟶ T :=
    { app := fun X =>
        eqToHom (congrArg S.obj (hX X)) ≫ TypeCat.ofHom p₀ ≫
          eqToHom (congrArg T.obj (hX X).symm)
      naturality := by
        intro X Y q
        cases hX X
        cases hX Y
        have hq : q = 𝟙 z := by
          apply Opposite.unop_injective
          apply SimplexCategory.Truncated.Hom.ext
          ext i
          dsimp [z, z₀] at i ⊢
          exact congrArg Fin.val (Subsingleton.elim _ _)
        rw [hq]
        simp }
  let top' : C ⟶ (SSet.Truncated.cosk 0).obj T :=
    (SSet.coskAdj 0).homEquiv _ _ p
  have hmap : coskZeroMap f = (SSet.Truncated.cosk 0).map
      ((SSet.truncation 0).map
        ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))) := by
    rfl
  let top : C ⟶ Unit19.coskZero A := by
    change C ⟶ (SSet.Truncated.cosk 0).obj T
    exact top'
  refine ⟨top, ?_⟩
  apply IsPullback.mk'
  · rw [hmap]
    change top' ≫ (SSet.Truncated.cosk 0).map
        ((SSet.truncation 0).map
          ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))) =
      ε ≫ u
    apply ((SSet.coskAdj 0).homEquiv C
      ((SSet.truncation 0).obj ((SimplicialObject.const (Type u)).obj B))).symm.injective
    rw [(SSet.coskAdj 0).homEquiv_naturality_right_symm top'
      ((SSet.truncation 0).map
        ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f)))]
    rw [(SSet.coskAdj 0).homEquiv_naturality_left_symm ε u]
    dsimp [top', u]
    simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_unit]
    apply SSet.Truncated.hom_ext
    intro X
    cases hX X
    ext x
    have hp : p.app z = TypeCat.ofHom p₀ := by
      dsimp [p]
      simp
    have hp₀ : p₀ ≫ TypeCat.ofHom f =
        ε.app (op (SimplexCategory.mk 0)) := by
      dsimp [p₀, ε, C, coskMinusOne, coskMinusOneAugmentation]
      change WidePullback.π (fun _ : Fin (0 + 1) => TypeCat.ofHom f) 0 ≫
        TypeCat.ofHom f = _
      simp
    have hcomp : p.app z ≫
        ((SSet.truncation 0).map
          ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))).app z =
        ((SSet.truncation 0).map ε).app z := by
      change p.app z ≫ TypeCat.ofHom f = ε.app
        (op (SimplexCategory.mk 0))
      rw [hp]
      exact hp₀
    exact ConcreteCategory.congr_hom hcomp x
  · intro R φ φ' htop hε
    have htr : (SSet.truncation 0).map φ ≫ p =
        (SSet.truncation 0).map φ' ≫ p := by
      have hp' : ((SSet.coskAdj 0).homEquiv C T).symm top' = p := by
        dsimp [top']
        simp
      rw [← hp']
      rw [← (SSet.coskAdj 0).homEquiv_naturality_left_symm φ top',
        ← (SSet.coskAdj 0).homEquiv_naturality_left_symm φ' top']
      change φ ≫ top' = φ' ≫ top' at htop
      exact congrArg ((SSet.coskAdj 0).homEquiv R T).symm htop
    have hp : p.app z = TypeCat.ofHom p₀ := by
      dsimp [p]
      simp
    have hzero : φ.app (op (SimplexCategory.mk 0)) ≫ p₀ =
        φ'.app (op (SimplexCategory.mk 0)) ≫ p₀ := by
      have hz := congr_app htr z
      change φ.app (op (SimplexCategory.mk 0)) ≫ p.app z =
        φ'.app (op (SimplexCategory.mk 0)) ≫ p.app z at hz
      simpa [hp] using hz
    apply SSet.hom_ext
    intro X
    cases X with
    | op X =>
      cases X with
      | mk m =>
        dsimp [C, coskMinusOne]
        change φ.app (op (SimplexCategory.mk m)) =
          φ'.app (op (SimplexCategory.mk m))
        apply WidePullback.hom_ext _ _ _
        · intro i
          let q := (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk m) i).op
          have hφ := φ.naturality q
          have hφ' := φ'.naturality q
          change R.map q ≫ φ.app (op (SimplexCategory.mk 0)) =
            φ.app (op (SimplexCategory.mk m)) ≫ C.map q at hφ
          change R.map q ≫ φ'.app (op (SimplexCategory.mk 0)) =
            φ'.app (op (SimplexCategory.mk m)) ≫ C.map q at hφ'
          have hcoord : C.map q ≫ p₀' =
              WidePullback.π (fun _ : Fin (m + 1) => F.hom) i := by
            dsimp [C, coskMinusOne, p₀', q, F]
            change WidePullback.lift _ _ _ ≫ _ = _
            change WidePullback.lift _ _ _ ≫
                WidePullback.π (fun _ : Fin (0 + 1) => TypeCat.ofHom f) 0 = _
            apply WidePullback.lift_π
          rw [← hcoord]
          have hzero' : φ.app (op (SimplexCategory.mk 0)) ≫ p₀' =
              φ'.app (op (SimplexCategory.mk 0)) ≫ p₀' := by
            apply ConcreteCategory.hom_ext
            intro x
            have hz' := ConcreteCategory.congr_hom hzero x
            convert hz' using 1
            · exact hT.symm
            · cases hS
              cases hT
              rfl
            · cases hS
              cases hT
              rfl
          have hφ₀ := congrArg (fun k => k ≫ p₀') hφ
          have hφ₀' := congrArg (fun k => k ≫ p₀') hφ'
          have hmid :
              (φ.app (op (SimplexCategory.mk m)) ≫ C.map q) ≫ p₀' =
                (φ'.app (op (SimplexCategory.mk m)) ≫ C.map q) ≫ p₀' := by
            rw [← hφ₀, ← hφ₀']
            simpa only [Category.assoc] using
              congrArg (fun k => R.map q ≫ k) hzero'
          exact hmid
        · have hε' := congr_app hε (op (SimplexCategory.mk m))
          dsimp [ε, coskMinusOneAugmentation, C, coskMinusOne, F]
          change φ.app (op (SimplexCategory.mk m)) ≫
              WidePullback.base (fun _ : Fin (m + 1) => F.hom) =
            φ'.app (op (SimplexCategory.mk m)) ≫
              WidePullback.base (fun _ : Fin (m + 1) => F.hom) at hε'
          exact hε'
  · intro R a b comm
    let c := (SSet.truncation 0).map
      ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))
    let g₀ : R.obj (op (SimplexCategory.mk 0)) ⟶ A :=
      a.app (op (SimplexCategory.mk 0)) ≫ εA.app z
    have hn₀ : ((SSet.truncation 0).map
        ((SSet.Truncated.cosk 0).map c)).app z ≫ εB.app z =
        εA.app z ≫ c.app z := by
      exact congr_app ((SSet.coskAdj 0).counit.naturality c) z
    have hut : u.app (op (SimplexCategory.mk 0)) ≫ εB.app z =
        𝟙 _ := by
      have h := (SSet.coskAdj 0).homEquiv_symm_unit
        ((SimplicialObject.const (Type u)).obj B)
      change (SSet.truncation 0).map u ≫ εB = 𝟙 _ at h
      have hz := congr_app h z
      change u.app (op (SimplexCategory.mk 0)) ≫ εB.app z = 𝟙 _ at hz
      exact hz
    have hg₀ : g₀ ≫ TypeCat.ofHom f =
        b.app (op (SimplexCategory.mk 0)) := by
      apply ConcreteCategory.hom_ext
      intro x
      change f (εA.app z (a.app (op (SimplexCategory.mk 0)) x)) =
        b.app (op (SimplexCategory.mk 0)) x
      have hcommx := ConcreteCategory.congr_hom
        (congr_app comm (op (SimplexCategory.mk 0))) x
      change (coskZeroMap f).app (op (SimplexCategory.mk 0))
          (a.app (op (SimplexCategory.mk 0)) x) =
        u.app (op (SimplexCategory.mk 0))
          (b.app (op (SimplexCategory.mk 0)) x) at hcommx
      have hnx := ConcreteCategory.congr_hom hn₀
        (a.app (op (SimplexCategory.mk 0)) x)
      change εB.app z ((coskZeroMap f).app
          (op (SimplexCategory.mk 0))
          (a.app (op (SimplexCategory.mk 0)) x)) =
        (c.app z) (εA.app z (a.app (op (SimplexCategory.mk 0)) x)) at hnx
      have hux := ConcreteCategory.congr_hom hut
        (b.app (op (SimplexCategory.mk 0)) x)
      change εB.app z (u.app (op (SimplexCategory.mk 0))
          (b.app (op (SimplexCategory.mk 0)) x)) =
        b.app (op (SimplexCategory.mk 0)) x at hux
      have hc := congrArg (fun y => εB.app z y) hcommx
      rw [hnx, hux] at hc
      change f (εA.app z (a.app (op (SimplexCategory.mk 0)) x)) =
        b.app (op (SimplexCategory.mk 0)) x at hc
      exact hc
    let l := cechNerve_lift_of_zero f this b g₀ hg₀
    refine ⟨l, ?_, ?_⟩
    · change l ≫ top' = a
      let a' : R ⟶ (SSet.Truncated.cosk 0).obj T := by
        change R ⟶ Unit19.coskZero A
        exact a
      change l ≫ top' = a'
      apply ((SSet.coskAdj 0).homEquiv R T).symm.injective
      rw [(SSet.coskAdj 0).homEquiv_naturality_left_symm l top']
      have hp' : ((SSet.coskAdj 0).homEquiv C T).symm top' = p := by
        dsimp [top']
        simp
      rw [hp']
      have hright :
          ((SSet.coskAdj 0).homEquiv R T).symm a' =
            (SSet.truncation 0).map a' ≫ εA := by
        rw [← Category.comp_id a']
        rw [(SSet.coskAdj 0).homEquiv_naturality_left_symm
          a' (𝟙 _)]
        change _ = _ ≫ (SSet.coskAdj 0).counit.app T
        rw [← (SSet.coskAdj 0).homEquiv_symm_id T]
        simp [Functor.map_comp, Category.assoc]
      rw [hright]
      apply SSet.Truncated.hom_ext
      intro X
      cases hX X
      dsimp [z, z₀]
      change ((SSet.truncation 0).map l).app z ≫ p.app z =
        ((SSet.truncation 0).map a').app z ≫ εA.app z
      have hp : p.app z = TypeCat.ofHom p₀ := by
        dsimp [p]
        simp
      have hp0e : p.app z ≫ eT = eqToHom hS ≫ p₀' := by
        rw [hp]
        dsimp [p₀, eT]
        simp [Category.assoc]
      apply (cancel_mono eT).1
      rw [Category.assoc, hp0e]
      apply ConcreteCategory.hom_ext
      intro x
      have hcomp : ((SSet.truncation 0).map l).app z ≫ eqToHom hS ≫ p₀' =
          ((SSet.truncation 0).map a').app z ≫ εA.app z ≫ eT := by
        have hR : ((SSet.truncation 0).obj R).obj z =
            R.obj (op z₀.obj) := by
          dsimp [z, z₀]
          rfl
        have hC : C.obj (op z₀.obj) =
            (coskMinusOne f).obj (op z₀.obj) := by
          dsimp [C]
        have htrunc : ((SSet.truncation 0).map l).app z ≫ eqToHom hS =
            eqToHom hR ≫ l.app (op z₀.obj) ≫ eqToHom hC.symm := by
          cases hS
          cases hR
          cases hC
          dsimp [z, z₀]
          rw [Formalization.Books.Simplicial.Unit12.truncation_map_app]
          convert rfl using 1 <;> simp
          all_goals
            apply ConcreteCategory.hom_ext
            intro x
            rfl
        have hlπ : l.app (op z₀.obj) ≫ eqToHom hC.symm ≫ p₀' = g₀ := by
          cases hC
          dsimp [l, cechNerve_lift_of_zero, p₀', C, coskMinusOne, F]
          change WidePullback.lift _ _ _ ≫ WidePullback.π _ 0 = _
          rw [WidePullback.lift_π]
          have hconst : (SimplexCategory.const z₀.obj z₀.obj 0).op =
              𝟙 (op z₀.obj) := by
            apply Opposite.unop_injective
            apply SimplexCategory.Hom.ext
            ext i
            simp
          rw [hconst, R.map_id, Category.id_comp]
        rw [← Category.assoc, htrunc]
        simp only [Category.assoc, hlπ]
        rw [eqToHom_comp_iff hR]
        cases hT
        dsimp [a', eT, g₀]
        rw [Formalization.Books.Simplicial.Unit12.truncation_map_app]
        dsimp [z, z₀]
        convert rfl using 1 <;> try simp [Category.assoc]
        all_goals
          apply ConcreteCategory.hom_ext
          intro x
          rfl
      exact ConcreteCategory.congr_hom hcomp x
    · apply SSet.hom_ext
      intro X
      cases X with
      | op X =>
        cases X with
        | mk m =>
          dsimp [l, cechNerve_lift_of_zero, ε,
            coskMinusOneAugmentation, C, coskMinusOne, F]
          dsimp [Arrow.augmentedCechNerve]
          change WidePullback.lift _ _ _ ≫ WidePullback.base _ = _
          simp only [WidePullback.lift_base]

/-- A surjection of sets gives a trivial Kan fibration from its Čech nerve
to the constant simplicial set on the target. -/
theorem coskMinusOne_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskMinusOneAugmentation f) := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  let C : SSet.{u} := coskMinusOne f
  let ε : C ⟶ (SimplicialObject.const (Type u)).obj B :=
    coskMinusOneAugmentation f
  let q : Unit19.coskZero A ⟶ Unit19.coskZero B := coskZeroMap f
  let u := (SSet.coskAdj 0).unit.app
    ((SimplicialObject.const (Type u)).obj B)
  obtain ⟨top, hpb⟩ := coskMinusOne_isPullback f
  let P := pullback q u
  let p : P ⟶ (SimplicialObject.const (Type u)).obj B :=
    pullback.snd q u
  have hp : Unit30.TrivialKanFibration p := by
    dsimp [p, q, u]
    apply Unit30.trivialKanFibration_baseChange
    exact coskZeroMap_trivialKanFibration f hf
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hp.1 y
    let x' : (Δ[0] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm x
    have hx' : x' ≫ p = SSet.yonedaEquiv.symm y := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      simpa [x', p, SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_const] using hx
    let l : (Δ[0] : SSet.{u}) ⟶ C :=
      hpb.lift
        (x' ≫ pullback.fst q u) (x' ≫ pullback.snd q u)
        (by
          dsimp [q, u]
          convert congrArg (fun z => x' ≫ z)
            (pullback.condition :
              pullback.fst (coskZeroMap f)
                  ((SSet.coskAdj 0).unit.app
                    ((SimplicialObject.const (Type u)).obj B)) ≫
                coskZeroMap f =
              pullback.snd (coskZeroMap f)
                  ((SSet.coskAdj 0).unit.app
                    ((SimplicialObject.const (Type u)).obj B)) ≫
            (SSet.coskAdj 0).unit.app
                  ((SimplicialObject.const (Type u)).obj B)) using 1 <;>
            rfl)
    refine ⟨SSet.yonedaEquiv l, ?_⟩
    have hl : l ≫ ε = x' ≫ p := by
      dsimp [l]
      simpa [p, ε] using
        (hpb.lift_snd
          (x' ≫ pullback.fst q u) (x' ≫ pullback.snd q u) _)
    rw [← SSet.yonedaEquiv_comp, hl, hx']
    exact SSet.yonedaEquiv_const y
  · intro n hn a b comm
    let i := (SSet.boundary n).ι
    let aP : (∂Δ[n] : SSet.{u}) ⟶ P :=
      pullback.lift (a ≫ top) (a ≫ ε) (by
        change (a ≫ top) ≫ coskZeroMap f =
          (a ≫ ε) ≫ (SSet.coskAdj 0).unit.app
            ((SimplicialObject.const (Type u)).obj B)
        dsimp [ε]
        convert congrArg (fun z => a ≫ z) hpb.w using 1 <;>
          rfl)
    have aPp : aP ≫ p = i ≫ b := by
      calc
        aP ≫ p = a ≫ ε := by
          simpa [aP, p] using
            (pullback.lift_snd (f := q) (g := u)
              (a ≫ top) (a ≫ ε) _)
        _ = i ≫ b := comm
    have hi : Unit30.TermwiseInjective i := by
      intro m
      have hm : Mono (i.app (op (SimplexCategory.mk m))) := by
        have hi' : Mono i := by infer_instance
        exact (NatTrans.mono_iff_mono_app i).mp hi'
          (op (SimplexCategory.mk m))
      rw [mono_iff_injective] at hm
      exact hm
    obtain ⟨c, hc₁, hc₂⟩ := Unit30.trivialKanFibration_lift
      p hp i hi aP b aPp
    let l : (Δ[n] : SSet.{u}) ⟶ C :=
      hpb.lift
        (c ≫ pullback.fst q u) (c ≫ pullback.snd q u)
        (by
          dsimp [q, u]
          convert congrArg (fun z => c ≫ z)
            (pullback.condition :
              pullback.fst (coskZeroMap f)
                  ((SSet.coskAdj 0).unit.app
                    ((SimplicialObject.const (Type u)).obj B)) ≫
                coskZeroMap f =
              pullback.snd (coskZeroMap f)
                  ((SSet.coskAdj 0).unit.app
                    ((SimplicialObject.const (Type u)).obj B)) ≫
                (SSet.coskAdj 0).unit.app
                  ((SimplicialObject.const (Type u)).obj B)) using 1 <;>
            rfl)
    have hl_top : l ≫ top = c ≫ pullback.fst q u := by
      dsimp [l]
      simpa using
        (hpb.lift_fst
          (c ≫ pullback.fst q u) (c ≫ pullback.snd q u) _)
    have hl_bot : l ≫ ε = c ≫ pullback.snd q u := by
      dsimp [l]
      simpa [ε] using
        (hpb.lift_snd
          (c ≫ pullback.fst q u) (c ≫ pullback.snd q u) _)
    refine ⟨l, ?_, ?_⟩
    · apply hpb.hom_ext
      · rw [Category.assoc, hl_top, ← Category.assoc, hc₁]
        simpa [aP] using
          (pullback.lift_fst (f := q) (g := u)
            (a ≫ top) (a ≫ ε) _)
      · rw [Category.assoc, hl_bot, ← Category.assoc, hc₁]
        simpa [aP] using
          (pullback.lift_snd (f := q) (g := u)
            (a ≫ top) (a ≫ ε) _)
    · rw [hl_bot]
      simpa [p] using hc₂

end Formalization.Books.Simplicial.Unit32
