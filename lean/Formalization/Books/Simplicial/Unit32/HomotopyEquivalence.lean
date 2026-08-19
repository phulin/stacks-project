import Formalization.Books.Simplicial.Unit20.Augmentations
import Formalization.Books.Simplicial.Unit26.Homotopies
import Formalization.Books.Simplicial.Unit30.TrivialKanFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

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

/-- The constant simplicial set with value `A`. -/
def constantSSet (A : Type u) : SSet.{u} :=
  (SimplicialObject.const (Type u)).obj A

/-- The source's `cosk₀(A)`. -/
def coskZero (A : Type u) : SSet.{u} :=
  (SSet.cosk 0).obj (constantSSet A)

/-- The simplicial map associated to a map of sets `f : A → B`. -/
def coskZeroMap {A B : Type u} (f : A → B) : coskZero A ⟶ coskZero B :=
  (SSet.cosk 0).map
    ((SimplicialObject.const (Type u)).map (TypeCat.ofHom f))

/-- The canonical map from a simplicial set to its `n`-coskeleton. -/
def canonicalCoskeletonMap (n : ℕ) (X : SSet.{u}) :
    X ⟶ (SSet.cosk n).obj X :=
  (SSet.coskAdj n).unit.app X

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
      ((SSet.truncation 0).obj (constantSSet A))
    let eA : (coskZero A).obj (op (SimplexCategory.mk 0)) → A :=
      εA.app ⟨SimplexCategory.mk 0, by simp⟩
    let h₀ : ((coskZero A ⊗ (Δ[1] : SSet)).obj
        (op (SimplexCategory.mk 0))) → B := by
      intro x
      change (coskZero A).obj _ × (Δ[1] : SSet).obj _ at x
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
    let S := (SSet.truncation 0).obj (coskZero A ⊗ (Δ[1] : SSet))
    let T := (SSet.truncation 0).obj (constantSSet B)
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
    let h : (coskZero A ⊗ (Δ[1] : SSet)) ⟶
        (SSet.Truncated.cosk 0).obj ((SSet.truncation 0).obj (constantSSet B)) :=
      (SSet.coskAdj 0).homEquiv _ _ q
    have hε :
        ((SSet.coskAdj 0).homEquiv
          ((SSet.Truncated.cosk 0).obj ((SSet.truncation 0).obj (constantSSet A)))
          ((SSet.truncation 0).obj (constantSSet A))).symm
            (𝟙 ((SSet.Truncated.cosk 0).obj
              ((SSet.truncation 0).obj (constantSSet A)))) = εA := by
      exact (SSet.coskAdj 0).homEquiv_symm_id
        ((SSet.truncation 0).obj (constantSSet A))
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
      apply ((SSet.coskAdj 0).homEquiv (coskZero A) T).symm.injective
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
      have hfst := SSet.ι₀_app_fst (X := coskZero A) x
      have hsnd := SSet.ι₀_app_snd_apply (X := coskZero A) x (0 : Fin 1)
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
      apply ((SSet.coskAdj 0).homEquiv (coskZero A) T).symm.injective
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
      have hfst := SSet.ι₁_app_fst (X := coskZero A) x
      have hsnd := SSet.ι₁_app_snd_apply (X := coskZero A) x (0 : Fin 1)
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

private lemma boundaryTruncationMap_isIso (n k : ℕ) (h : n < k) :
    IsIso ((SSet.truncation n).map (SSet.boundary k).ι) := by
  let g := (SSet.truncation n).map (SSet.boundary k).ι
  letI : ∀ X, IsIso (g.app X) := by
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
          simp only [SSet.boundary_obj_eq_univ i k (lt_of_le_of_lt hX h)]
          constructor
          · intro x y hxy
            exact Subtype.ext hxy
          · intro y
            have hy : y ∈ (SSet.boundary k).obj (op ⦋i⦌) := by
              rw [SSet.boundary_obj_eq_univ i k (lt_of_le_of_lt hX h)]
              exact Set.mem_univ y
            exact ⟨⟨y, hy⟩, rfl⟩
  exact CategoryTheory.NatIso.isIso_of_isIso_app g

private lemma coskeletal_extension {X : SSet.{u}} (n k : ℕ) (h : n < k)
    (hX : IsIso (canonicalCoskeletonMap n X))
    (a : (∂Δ[k] : SSet.{u}) ⟶ X) :
    ∃ l : (Δ[k] : SSet.{u}) ⟶ X, (SSet.boundary k).ι ≫ l = a := by
  letI : IsIso (canonicalCoskeletonMap n X) := hX
  let i := (SSet.truncation n).map (SSet.boundary k).ι
  letI : IsIso i := boundaryTruncationMap_isIso n k h
  let q : (SSet.truncation n).obj (Δ[k] : SSet.{u}) ⟶
      (SSet.truncation n).obj X :=
    inv i ≫ (SSet.truncation n).map a
  let l' : (Δ[k] : SSet.{u}) ⟶
      (SSet.Truncated.cosk n).obj ((SSet.truncation n).obj X) :=
    (SSet.coskAdj n).homEquiv _ _ q
  let l : (Δ[k] : SSet.{u}) ⟶ X :=
    l' ≫ inv (canonicalCoskeletonMap n X)
  refine ⟨l, ?_⟩
  apply (cancel_mono (canonicalCoskeletonMap n X)).1
  simp only [l, Category.assoc, IsIso.inv_hom_id_assoc]
  exact sorry

/-- If a map is bijective below degree `n`, surjective in degree `n`, and
both simplicial sets are `n`-coskeletal, then it is a trivial Kan fibration.
-/
theorem section_lemma {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (h_bijective : ∀ i : ℕ, i < n →
      Function.Bijective (f.app (op (SimplexCategory.mk i))))
    (h_surjective : Function.Surjective
      (f.app (op (SimplexCategory.mk n))))
    (hU : IsIso (canonicalCoskeletonMap n U))
    (hV : IsIso (canonicalCoskeletonMap n V)) :
    Unit30.TrivialKanFibration f := by
  sorry

/-- The degree-zero case of `section_lemma` for a surjective map of sets. -/
theorem coskZeroMap_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskZeroMap f) := by
  sorry

/-! ## Homotopy from agreement below the coskeleton degree -/

/-- Maps agreeing below degree `n` are homotopic when both simplicial sets are
`n`-coskeletal. -/
theorem homotopy_lemma {V U : SSet.{u}} (f₀ f₁ : V ⟶ U) (n : ℕ)
    (h_equal : ∀ i : ℕ, i < n →
      f₀.app (op (SimplexCategory.mk i)) =
        f₁.app (op (SimplexCategory.mk i)))
    (hU : IsIso (canonicalCoskeletonMap n U))
    (hV : IsIso (canonicalCoskeletonMap n V)) :
    Unit26.Homotopic f₀ f₁ := by
  sorry

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
    coskMinusOne f ⟶ constantSSet B := by
  letI : ∀ n : ℕ, HasWidePullback B
      (fun _ : Fin (n + 1) => A) (fun _ => TypeCat.ofHom f) :=
    hasCechNerveOfFunction f
  exact (Arrow.mk (TypeCat.ofHom f)).augmentedCechNerve.hom

/-- The Čech nerve is the pullback of `cosk₀(A)` along the canonical map
from the constant simplicial set on `B`. -/
theorem coskMinusOne_isPullback {A B : Type u} (f : A → B) :
    ∃ top : coskMinusOne f ⟶ coskZero A,
      IsPullback top (coskMinusOneAugmentation f)
        (coskZeroMap f) (canonicalCoskeletonMap 0 (constantSSet B)) := by
  sorry

/-- A surjection of sets gives a trivial Kan fibration from its Čech nerve
to the constant simplicial set on the target. -/
theorem coskMinusOne_trivialKanFibration {A B : Type u} (f : A → B)
    (hf : Function.Surjective f) :
    Unit30.TrivialKanFibration (coskMinusOneAugmentation f) := by
  sorry

end Formalization.Books.Simplicial.Unit32
