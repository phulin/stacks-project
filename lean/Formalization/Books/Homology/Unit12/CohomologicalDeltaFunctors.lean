import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homological Algebra, Chapter 12: Cohomological delta-functors

The source packages a family of additive functors together with connecting
morphisms for short exact sequences.  The exactness of the resulting long
sequence is recorded by `LongExactness`; Mathlib's `ShortComplex.Exact` is
used at each three-term portion of that sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open scoped ZeroObject

universe v u v' u'

namespace Formalization.Books.Homology.Unit12

/-! ## Exact portions of a long sequence -/

/-- A composable pair of morphisms together with its exactness. -/
structure ExactPair
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop where
  zero : f ≫ g = 0
  exact : (ShortComplex.mk f g zero).Exact

/-- The four kinds of exact portions in the long sequence attached to a
short exact sequence.  The `at_left` field starts in degree one, since the
degree-zero left endpoint is the explicit zero object in `at_zero`. -/
structure LongExactness
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : ℕ → A ⥤ B)
    (delta : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁)
    (S : ShortComplex A) (hS : S.ShortExact) : Prop where
  at_zero :
    ExactPair
      (0 : (0 : B) ⟶ (F 0).obj S.X₁)
      ((F 0).map S.f)
  at_left : ∀ n : ℕ,
    ExactPair
      (delta S hS n)
      ((F (n + 1)).map S.f)
  at_middle : ∀ n : ℕ,
    ExactPair
      ((F n).map S.f)
      ((F n).map S.g)
  at_right : ∀ n : ℕ,
    ExactPair
      ((F n).map S.g)
      (delta S hS n)

/-! ## Cohomological delta-functors -/

/-- A cohomological delta-functor from one abelian category to another. -/
structure CohomologicalDeltaFunctor
    (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type u') [Category.{v'} B] [Abelian B] where
  /-- The additive functor in each nonnegative degree. -/
  functor : ℕ → A ⥤ B
  /-- Additivity of every member of the family. -/
  additive : ∀ n : ℕ, (functor n).Additive
  /-- The connecting morphism for every short exact sequence and degree. -/
  delta : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
    (functor n).obj S.X₃ ⟶ (functor (n + 1)).obj S.X₁
  /-- Exactness of the long sequence associated to every short exact sequence. -/
  exact : ∀ (S : ShortComplex A) (hS : S.ShortExact),
    LongExactness functor delta S hS
  /-- Naturality of the connecting morphisms in morphisms of short exact sequences. -/
  natural : ∀ {S₁ S₂ : ShortComplex A}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ),
    delta S₁ h₁ n ≫ (functor (n + 1)).map φ.τ₁ =
      (functor n).map φ.τ₃ ≫ delta S₂ h₂ n

/-- The observation in the source that the degree-zero functor is left exact. -/
theorem CohomologicalDeltaFunctor.isLeftExact_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) :
    IsLeftExact (F.functor 0) := by
  change PreservesFiniteLimits (F.functor 0)
  let _ := F.additive 0
  exact (CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 (fun S hS =>
    ⟨by simpa [ShortComplex.map] using (F.exact S hS).at_middle 0 |>.exact,
     (ShortComplex.exact_iff_mono _ (by simp)).1 (F.exact S hS).at_zero.exact⟩)

/-! ## Morphisms and universal delta-functors -/

/-- A morphism of cohomological delta-functors. -/
structure DeltaFunctorMorphism
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B) where
  /-- The natural transformation in each degree. -/
  app : ∀ n : ℕ, F.functor n ⟶ G.functor n
  /-- Compatibility with the connecting morphisms. -/
  comm : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
    F.delta S hS n ≫ (app (n + 1)).app S.X₁ =
      (app n).app S.X₃ ≫ G.delta S hS n

namespace CohomologicalDeltaFunctor

/-- The universal property of a cohomological delta-functor. -/
def IsUniversal
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (G : CohomologicalDeltaFunctor A B)
    (t : F.functor 0 ⟶ G.functor 0),
    ∃! φ : DeltaFunctorMorphism F G, φ.app 0 = t

/-- Effaceability in every positive degree. -/
def IsEffaceable
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (X : A),
    ∃ (Y : A) (u : X ⟶ Y),
      Mono u ∧ (F.functor n).map u = 0

end CohomologicalDeltaFunctor

/-- An effaceable cohomological delta-functor is universal. -/
theorem effaceable_isUniversal
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : CohomologicalDeltaFunctor A B)
    (hF : F.IsEffaceable) :
    F.IsUniversal := by
  intro G t
  let extend (n : ℕ) (α : F.functor n ⟶ G.functor n) :
      { β : F.functor (n + 1) ⟶ G.functor (n + 1) //
        (∀ (S : ShortComplex A) (hS : S.ShortExact),
          F.delta S hS n ≫ (β).app S.X₁ =
            (α).app S.X₃ ≫ G.delta S hS n) ∧
        (∀ (X Y : A) (f : X ⟶ Y),
          (F.functor (n + 1)).map f ≫ (β).app Y =
            (β).app X ≫ (G.functor (n + 1)).map f) ∧
        (∀ (β₁ β₂ : F.functor (n + 1) ⟶ G.functor (n + 1)),
          (∀ (S : ShortComplex A) (hS : S.ShortExact),
            F.delta S hS n ≫ (β₁).app S.X₁ =
              (α).app S.X₃ ≫ G.delta S hS n) →
          (∀ (S : ShortComplex A) (hS : S.ShortExact),
            F.delta S hS n ≫ (β₂).app S.X₁ =
              (α).app S.X₃ ≫ G.delta S hS n) →
          β₁ = β₂) } := by
    let data (X : A) := hF (n + 1) (Nat.zero_lt_succ n) X
    let Y (X : A) := Classical.choose (data X)
    let u (X : A) := Classical.choose (Classical.choose_spec (data X))
    have hu (X : A) : Mono (u X) :=
      (Classical.choose_spec (Classical.choose_spec (data X))).1
    have hu0 (X : A) : (F.functor (n + 1)).map (u X) = 0 :=
      (Classical.choose_spec (Classical.choose_spec (data X))).2
    let canonical (X Z : A) (v : X ⟶ Z) : ShortComplex A :=
      ShortComplex.mk v (cokernel.π v) (cokernel.condition v)
    have canonical_exact (X Z : A) (v : X ⟶ Z) (hv : Mono v) :
        (canonical X Z v).ShortExact := by
      dsimp [canonical]
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hv inferInstance
    have delta_epi (S : ShortComplex A) (hS : S.ShortExact)
        (hz : (F.functor (n + 1)).map S.f = 0) :
        Epi (F.delta S hS n) := by
      let T := ShortComplex.mk
        (F.delta S hS n)
        ((F.functor (n + 1)).map S.f)
        ((F.exact S hS).at_left n).zero
      have hT : T.Exact := (F.exact S hS).at_left n |>.exact
      exact (T.exact_iff_epi hz).1 hT
    have delta_coker (S : ShortComplex A) (hS : S.ShortExact)
        (hz : (F.functor (n + 1)).map S.f = 0) :
        IsColimit (CokernelCofork.ofπ (F.delta S hS n)
          ((F.exact S hS).at_right n).zero) := by
      let T := ShortComplex.mk
        ((F.functor n).map S.g)
        (F.delta S hS n)
        ((F.exact S hS).at_right n).zero
      have hT : T.Exact := (F.exact S hS).at_right n |>.exact
      exact ((T.exact_and_epi_g_iff_g_is_cokernel).1
        ⟨hT, delta_epi S hS hz⟩).some
    have a_zero (S : ShortComplex A) (hS : S.ShortExact) :
        (F.functor n).map S.g ≫
            ((α).app S.X₃ ≫ G.delta S hS n) = 0 := by
      rw [← Category.assoc, α.naturality, Category.assoc,
        (G.exact S hS).at_right n |>.zero, comp_zero]
    let betaFor (S : ShortComplex A) (hS : S.ShortExact)
        (hz : (F.functor (n + 1)).map S.f = 0) :
        (F.functor (n + 1)).obj S.X₁ ⟶ (G.functor (n + 1)).obj S.X₁ :=
      (delta_coker S hS hz).desc
        (CokernelCofork.ofπ (α.app S.X₃ ≫ G.delta S hS n) (a_zero S hS))
    have betaFor_eq (S : ShortComplex A) (hS : S.ShortExact)
        (hz : (F.functor (n + 1)).map S.f = 0) :
        F.delta S hS n ≫ betaFor S hS hz =
          α.app S.X₃ ≫ G.delta S hS n := by
      dsimp [betaFor]
      exact Cofork.IsColimit.π_desc (delta_coker S hS hz)
    let S (X : A) : ShortComplex A := canonical X (Y X) (u X)
    have hS (X : A) : (S X).ShortExact :=
      canonical_exact X (Y X) (u X) (hu X)
    let b (X : A) : (F.functor (n + 1)).obj X ⟶ (G.functor (n + 1)).obj X :=
      betaFor (S X) (hS X) (hu0 X)
    have hb (X : A) :
        F.delta (S X) (hS X) n ≫ b X =
          α.app (S X).X₃ ≫ G.delta (S X) (hS X) n :=
      betaFor_eq (S X) (hS X) (hu0 X)
    have compare (X Z : A) (v : X ⟶ Z) (hv : Mono v)
        (hz : (F.functor (n + 1)).map v = 0) :
        b X = betaFor (canonical X Z v) (canonical_exact X Z v hv) hz := by
      let W : ShortComplex A :=
        ShortComplex.mk
          (biprod.lift (u X) v)
          (cokernel.π (biprod.lift (u X) v))
          (cokernel.condition (biprod.lift (u X) v))
      let _ := hu X
      have hW : W.ShortExact := by
        dsimp [W]
        exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
          inferInstance inferInstance
      have hzW : (F.functor (n + 1)).map W.f = 0 := by
        let _ := F.additive (n + 1)
        dsimp [W]
        simp [biprod.lift_eq, Functor.map_add, hu0 X, hz]
      let q₁ : W.X₃ ⟶ (S X).X₃ :=
        cokernel.desc W.f (biprod.fst ≫ (S X).g) (by
          dsimp [W]
          rw [← Category.assoc, biprod.lift_fst]
          exact (S X).zero)
      let q₂ : W.X₃ ⟶ (canonical X Z v).X₃ :=
        cokernel.desc W.f (biprod.snd ≫ (canonical X Z v).g) (by
          dsimp [W]
          rw [← Category.assoc, biprod.lift_snd]
          exact (canonical X Z v).zero)
      let φ₁ : W ⟶ S X :=
        { τ₁ := 𝟙 _
          τ₂ := biprod.fst
          τ₃ := q₁
          comm₁₂ := by
            dsimp [W, S, canonical]
            simpa only [Category.id_comp] using (biprod.lift_fst (u X) v).symm
          comm₂₃ := by
            dsimp [W, q₁]
            simp }
      let φ₂ : W ⟶ canonical X Z v :=
        { τ₁ := 𝟙 _
          τ₂ := biprod.snd
          τ₃ := q₂
          comm₁₂ := by
            dsimp [W, canonical]
            simpa only [Category.id_comp] using (biprod.lift_snd (u X) v).symm
          comm₂₃ := by
            dsimp [W, q₂]
            simp }
      have h₁ : F.delta W hW n ≫ b X =
          α.app W.X₃ ≫ G.delta W hW n := by
        have hF₁ := F.natural hW (hS X) φ₁ n
        dsimp [φ₁] at hF₁
        have hG₁ := G.natural hW (hS X) φ₁ n
        dsimp [φ₁] at hG₁
        have hG₁' : G.delta W hW n =
            (G.functor n).map q₁ ≫ G.delta (S X) (hS X) n := by
          simpa using hG₁
        calc
          F.delta W hW n ≫ b X =
              F.delta W hW n ≫ (F.functor (n + 1)).map (𝟙 _) ≫ b X := by simp
          _ = (F.functor n).map q₁ ≫
              F.delta (S X) (hS X) n ≫ b X := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ b X) hF₁
          _ = (F.functor n).map q₁ ≫
              (α.app (S X).X₃ ≫ G.delta (S X) (hS X) n) := by rw [hb]
          _ = α.app W.X₃ ≫ (G.functor n).map q₁ ≫
              G.delta (S X) (hS X) n := by
                rw [← Category.assoc, α.naturality q₁, Category.assoc]
          _ = α.app W.X₃ ≫ G.delta W hW n := by
                have hG₁ := G.natural hW (hS X) φ₁ n
                dsimp [φ₁] at hG₁
                simpa using
                  congrArg (fun k => α.app W.X₃ ≫ k) hG₁'.symm
      have h₂ : F.delta W hW n ≫
          betaFor (canonical X Z v) (canonical_exact X Z v hv) hz =
            α.app W.X₃ ≫ G.delta W hW n := by
        calc
          F.delta W hW n ≫
              betaFor (canonical X Z v) (canonical_exact X Z v hv) hz =
              F.delta W hW n ≫ (F.functor (n + 1)).map (𝟙 _) ≫
                betaFor (canonical X Z v) (canonical_exact X Z v hv) hz := by simp
          _ = (F.functor n).map q₂ ≫
              F.delta (canonical X Z v) (canonical_exact X Z v hv) n ≫
                betaFor (canonical X Z v) (canonical_exact X Z v hv) hz := by
                have hF₂ := F.natural hW (canonical_exact X Z v hv) φ₂ n
                dsimp [φ₂] at hF₂
                simpa only [Category.assoc] using congrArg
                  (fun k => k ≫ betaFor (canonical X Z v)
                    (canonical_exact X Z v hv) hz) hF₂
          _ = (F.functor n).map q₂ ≫
              (α.app (canonical X Z v).X₃ ≫
                G.delta (canonical X Z v) (canonical_exact X Z v hv) n) := by
                rw [betaFor_eq]
          _ = α.app W.X₃ ≫ (G.functor n).map q₂ ≫
              G.delta (canonical X Z v) (canonical_exact X Z v hv) n := by
                rw [← Category.assoc, α.naturality q₂, Category.assoc]
          _ = α.app W.X₃ ≫ G.delta W hW n := by
                have hG₂ := G.natural hW (canonical_exact X Z v hv) φ₂ n
                dsimp [φ₂] at hG₂
                simpa [Category.assoc] using
                  congrArg (fun k => α.app W.X₃ ≫ k) hG₂.symm
      let := delta_epi W hW hzW
      apply (cancel_epi (F.delta W hW n)).1
      rw [h₁, h₂]
    have beta_natural : ∀ (X Y : A) (f : X ⟶ Y),
        (F.functor (n + 1)).map f ≫ b Y =
          b X ≫ (G.functor (n + 1)).map f := by
      intro X Z f
      let W : ShortComplex A :=
        ShortComplex.mk
          (biprod.lift (u X) (f ≫ u Z))
          (cokernel.π (biprod.lift (u X) (f ≫ u Z)))
          (cokernel.condition (biprod.lift (u X) (f ≫ u Z)))
      let _ := hu X
      have hW : W.ShortExact := by
        dsimp [W]
        exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
          inferInstance inferInstance
      have hzW : (F.functor (n + 1)).map W.f = 0 := by
        let _ := F.additive (n + 1)
        dsimp [W]
        simp [biprod.lift_eq, Functor.map_add, hu0 X, hu0 Z]
      let q₁ : W.X₃ ⟶ (S X).X₃ :=
        cokernel.desc W.f (biprod.fst ≫ (S X).g) (by
          dsimp [W]
          rw [← Category.assoc, biprod.lift_fst]
          exact (S X).zero)
      let q₂ : W.X₃ ⟶ (S Z).X₃ :=
        cokernel.desc W.f (biprod.snd ≫ (S Z).g) (by
          dsimp [W]
          rw [← Category.assoc, biprod.lift_snd]
          simpa only [Category.assoc, comp_zero] using
            congrArg (fun k => f ≫ k) (S Z).zero)
      let φ₁ : W ⟶ S X :=
        { τ₁ := 𝟙 _
          τ₂ := biprod.fst
          τ₃ := q₁
          comm₁₂ := by
            dsimp [W, S, canonical]
            simpa only [Category.id_comp] using
              (biprod.lift_fst (u X) (f ≫ u Z)).symm
          comm₂₃ := by
            dsimp [W, q₁]
            simp }
      let φ₂ : W ⟶ S Z :=
        { τ₁ := f
          τ₂ := biprod.snd
          τ₃ := q₂
          comm₁₂ := by
            dsimp [W, S, canonical]
            exact (biprod.lift_snd (u X) (f ≫ u Z)).symm
          comm₂₃ := by
            dsimp [W, q₂]
            simp }
      have h₁ : F.delta W hW n ≫ b X =
          α.app W.X₃ ≫ G.delta W hW n := by
        have hF₁ := F.natural hW (hS X) φ₁ n
        dsimp [φ₁] at hF₁
        have hG₁ := G.natural hW (hS X) φ₁ n
        dsimp [φ₁] at hG₁
        have hG₁' : G.delta W hW n =
            (G.functor n).map q₁ ≫ G.delta (S X) (hS X) n := by
          simpa using hG₁
        calc
          F.delta W hW n ≫ b X =
              F.delta W hW n ≫ (F.functor (n + 1)).map (𝟙 _) ≫ b X := by simp
          _ = (F.functor n).map q₁ ≫
              F.delta (S X) (hS X) n ≫ b X := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ b X) hF₁
          _ = (F.functor n).map q₁ ≫
              (α.app (S X).X₃ ≫ G.delta (S X) (hS X) n) := by rw [hb]
          _ = α.app W.X₃ ≫ (G.functor n).map q₁ ≫
              G.delta (S X) (hS X) n := by
                rw [← Category.assoc, α.naturality q₁, Category.assoc]
          _ = α.app W.X₃ ≫ G.delta W hW n := by
                simpa only [Functor.map_id, Category.comp_id, Category.assoc] using
                  congrArg (fun k => α.app W.X₃ ≫ k) hG₁'.symm
      have h₂ : F.delta W hW n ≫
          (F.functor (n + 1)).map f ≫ b Z =
            α.app W.X₃ ≫ G.delta W hW n ≫
              (G.functor (n + 1)).map f := by
        have hF₂ := F.natural hW (hS Z) φ₂ n
        dsimp [φ₂] at hF₂
        have hG₂ := G.natural hW (hS Z) φ₂ n
        dsimp [φ₂] at hG₂
        calc
          F.delta W hW n ≫ (F.functor (n + 1)).map f ≫ b Z =
              (F.functor n).map q₂ ≫
                F.delta (S Z) (hS Z) n ≫ b Z := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => k ≫ b Z) hF₂
          _ = (F.functor n).map q₂ ≫
              (α.app (S Z).X₃ ≫ G.delta (S Z) (hS Z) n) := by rw [hb]
          _ = α.app W.X₃ ≫ (G.functor n).map q₂ ≫
              G.delta (S Z) (hS Z) n := by
                rw [← Category.assoc, α.naturality q₂, Category.assoc]
          _ = α.app W.X₃ ≫ G.delta W hW n ≫
              (G.functor (n + 1)).map f := by
                simpa only [Category.assoc] using
                  congrArg (fun k => α.app W.X₃ ≫ k) hG₂.symm
      let := delta_epi W hW hzW
      apply (cancel_epi (F.delta W hW n)).1
      rw [h₂]
      simpa only [Category.assoc] using
        (congrArg (fun k => k ≫ (G.functor (n + 1)).map f) h₁).symm
    have comm_all : ∀ (T : ShortComplex A) (hT : T.ShortExact),
        F.delta T hT n ≫ b T.X₁ = α.app T.X₃ ≫ G.delta T hT n := by
      intro T hT
      let data' := hF (n + 1) (Nat.zero_lt_succ n) T.X₂
      let Z := Classical.choose (data')
      let w := Classical.choose (Classical.choose_spec data')
      have hw : Mono w :=
        (Classical.choose_spec (Classical.choose_spec data')).1
      have hw0 : (F.functor (n + 1)).map w = 0 :=
        (Classical.choose_spec (Classical.choose_spec data')).2
      let v : T.X₁ ⟶ Z := T.f ≫ w
      have hv : Mono v := by
        let _ := hT.mono_f
        exact inferInstance
      have hzv : (F.functor (n + 1)).map v = 0 := by
        simp [v, Functor.map_comp, hw0]
      let U := canonical T.X₁ Z v
      have hU : U.ShortExact := canonical_exact T.X₁ Z v hv
      let q : T.X₃ ⟶ U.X₃ :=
        Cofork.IsColimit.desc hT.gIsCokernel (w ≫ U.g) (by
          dsimp [U, canonical, v]
          rw [← Category.assoc, cokernel.condition]
          simp)
      let φ : T ⟶ U :=
        { τ₁ := 𝟙 _
          τ₂ := w
          τ₃ := q
          comm₁₂ := by
            dsimp [U, v, canonical]
            simp
          comm₂₃ := by
            dsimp [q]
            simpa [q] using
              (Cofork.IsColimit.π_desc' hT.gIsCokernel (w ≫ U.g) _).symm }
      have hTU := betaFor_eq U hU hzv
      have heq := compare T.X₁ Z v hv hzv
      calc
        F.delta T hT n ≫ b T.X₁ =
            F.delta T hT n ≫ (F.functor (n + 1)).map (𝟙 _) ≫ b T.X₁ := by simp
        _ = (F.functor n).map q ≫ F.delta U hU n ≫ b T.X₁ := by
          have hFφ := F.natural hT hU φ n
          dsimp [φ] at hFφ
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ b T.X₁) hFφ
        _ = (F.functor n).map q ≫ F.delta U hU n ≫ betaFor U hU hzv := by
          rw [heq]
        _ = (F.functor n).map q ≫
            (α.app U.X₃ ≫ G.delta U hU n) := by rw [hTU]
        _ = α.app T.X₃ ≫ (G.functor n).map q ≫ G.delta U hU n := by
          rw [← Category.assoc, α.naturality q, Category.assoc]
        _ = α.app T.X₃ ≫ G.delta T hT n := by
          have hGφ := G.natural hT hU φ n
          dsimp [φ] at hGφ
          simpa [Category.assoc] using
            congrArg (fun k => α.app T.X₃ ≫ k) hGφ.symm
    have unique (β₁ β₂ : F.functor (n + 1) ⟶ G.functor (n + 1))
        (h₁ : ∀ (S : ShortComplex A) (hS : S.ShortExact),
          F.delta S hS n ≫ (β₁).app S.X₁ = α.app S.X₃ ≫ G.delta S hS n)
        (h₂ : ∀ (S : ShortComplex A) (hS : S.ShortExact),
          F.delta S hS n ≫ (β₂).app S.X₁ = α.app S.X₃ ≫ G.delta S hS n) :
        β₁ = β₂ := by
      ext X
      let := delta_epi (S X) (hS X) (hu0 X)
      apply (cancel_epi (F.delta (S X) (hS X) n)).1
      rw [h₁, h₂]
    refine ⟨{ app := b, naturality := beta_natural }, comm_all, beta_natural, unique⟩
  let app : ∀ n : ℕ, F.functor n ⟶ G.functor n :=
    Nat.rec t (fun n α => (extend n α).1)
  have app_natural : ∀ (n : ℕ) (X Y : A) (f : X ⟶ Y),
      (F.functor n).map f ≫ (app n).app Y =
        (app n).app X ≫ (G.functor n).map f := by
    intro n
    cases n with
    | zero =>
        intro X Y f
        change (F.functor 0).map f ≫ t.app Y =
          t.app X ≫ (G.functor 0).map f
        exact t.naturality f
    | succ n =>
        intro X Y f
        change (F.functor (n + 1)).map f ≫
            (extend n (app n)).1.app Y =
          (extend n (app n)).1.app X ≫ (G.functor (n + 1)).map f
        exact (extend n (app n)).2.2.1 X Y f
  have app_comm : ∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
      F.delta S hS n ≫ (app (n + 1)).app S.X₁ =
        (app n).app S.X₃ ≫ G.delta S hS n := by
    intro S hS n
    cases n with
    | zero =>
        change F.delta S hS 0 ≫ (extend 0 t).1.app S.X₁ =
          t.app S.X₃ ≫ G.delta S hS 0
        exact (extend 0 t).2.1 S hS
    | succ n =>
        change F.delta S hS (n + 1) ≫
            (extend (n + 1) (app (n + 1))).1.app S.X₁ =
          (app (n + 1)).app S.X₃ ≫ G.delta S hS (n + 1)
        exact (extend (n + 1) (app (n + 1))).2.1 S hS
  let φ : DeltaFunctorMorphism F G :=
    { app := app
      comm := app_comm }
  have hφapp : ∀ n : ℕ, φ.app n = app n := by
    intro n
    rfl
  refine ⟨φ, ?_, ?_⟩
  · change app 0 = t
    rfl
  · intro ψ hψ
    have huniq : ∀ n : ℕ, ψ.app n = app n := by
      intro n
      induction n with
      | zero =>
          change ψ.app 0 = t at hψ
          rw [show app 0 = t from rfl]
          exact hψ
      | succ n ih =>
          apply (extend n (app n)).2.2.2 (ψ.app (n + 1)) (app (n + 1))
          · intro S hS
            simpa [ih] using ψ.comm S hS n
          · intro S hS
            change F.delta S hS n ≫ (extend n (app n)).1.app S.X₁ =
              (app n).app S.X₃ ≫ G.delta S hS n
            exact (extend n (app n)).2.1 S hS
    cases ψ with
    | mk ψapp ψcomm =>
        have happ : ψapp = app := funext huniq
        cases happ
        rfl

/-! ## Isomorphisms and uniqueness -/

/-- An isomorphism of cohomological delta-functors, degree by degree. -/
structure DeltaFunctorIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B) where
  hom : DeltaFunctorMorphism F G
  inv : DeltaFunctorMorphism G F
  hom_inv_id : ∀ n : ℕ, hom.app n ≫ inv.app n = 𝟙 _
  inv_hom_id : ∀ n : ℕ, inv.app n ≫ hom.app n = 𝟙 _

/-- Universal delta-functors are uniquely isomorphic once the degree-zero
natural isomorphism is fixed.  Taking the identity when the degree-zero
functors are equal gives the source's uniqueness statement. -/
theorem universal_deltaFunctor_unique_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F G : CohomologicalDeltaFunctor A B)
    (hF : F.IsUniversal) (hG : G.IsUniversal)
    (e₀ : F.functor 0 ≅ G.functor 0) :
    ∃! e : DeltaFunctorIso F G, e.hom.app 0 = e₀.hom := by
  let idMorphism (H : CohomologicalDeltaFunctor A B) : DeltaFunctorMorphism H H :=
    { app := fun n => 𝟙 _
      comm := by
        intro S hS n
        simp }
  let compMorphism (H I J : CohomologicalDeltaFunctor A B)
      (α : DeltaFunctorMorphism H I) (β : DeltaFunctorMorphism I J) :
      DeltaFunctorMorphism H J :=
    { app := fun n => α.app n ≫ β.app n
      comm := by
        intro S hS n
        simp only [NatTrans.comp_app]
        rw [← Category.assoc, α.comm, Category.assoc, β.comm, ← Category.assoc] }
  let hom : DeltaFunctorMorphism F G := Classical.choose (hF G e₀.hom)
  let inv : DeltaFunctorMorphism G F := Classical.choose (hG F e₀.inv)
  have hom_zero : hom.app 0 = e₀.hom :=
    (Classical.choose_spec (hF G e₀.hom)).1
  have inv_zero : inv.app 0 = e₀.inv :=
    (Classical.choose_spec (hG F e₀.inv)).1
  have hom_inv_zero : (compMorphism F G F hom inv).app 0 = (idMorphism F).app 0 := by
    change hom.app 0 ≫ inv.app 0 = 𝟙 _
    rw [hom_zero, inv_zero, e₀.hom_inv_id]
  have inv_hom_zero : (compMorphism G F G inv hom).app 0 = (idMorphism G).app 0 := by
    change inv.app 0 ≫ hom.app 0 = 𝟙 _
    rw [inv_zero, hom_zero, e₀.inv_hom_id]
  have hom_inv : compMorphism F G F hom inv = idMorphism F :=
    (hF F (𝟙 _)).unique hom_inv_zero
      (by rfl)
  have inv_hom : compMorphism G F G inv hom = idMorphism G :=
    (hG G (𝟙 _)).unique inv_hom_zero
      (by rfl)
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, hom_zero, ?_⟩
  · intro n
    have h := congrArg (fun x : DeltaFunctorMorphism F F => x.app n) hom_inv
    simpa [compMorphism, idMorphism] using h
  · intro n
    have h := congrArg (fun x : DeltaFunctorMorphism G G => x.app n) inv_hom
    simpa [compMorphism, idMorphism] using h
  · intro e he
    rcases e with ⟨hom', inv', hom_inv_id', inv_hom_id'⟩
    have hom'_zero : hom'.app 0 = e₀.hom := he
    have inv'_zero : inv'.app 0 = e₀.inv := by
      apply (cancel_epi e₀.hom).1
      calc
        e₀.hom ≫ inv'.app 0 = 𝟙 _ := by simpa [hom'_zero] using hom_inv_id' 0
        _ = e₀.hom ≫ e₀.inv := e₀.hom_inv_id.symm
    have hhom : hom' = hom :=
      (hF G e₀.hom).unique hom'_zero hom_zero
    have hinv : inv' = inv :=
      (hG F e₀.inv).unique inv'_zero inv_zero
    cases hhom
    cases hinv
    rfl

end Formalization.Books.Homology.Unit12
