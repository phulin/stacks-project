import Formalization.Books.Algebra.Unit56
import Formalization.Books.Algebra.Unit87
import Formalization.Books.Algebra.Unit96
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 98: Taking limits of modules

The inverse systems in the source are indexed by the positive natural numbers.
The declarations below use the inverse-system and graded-module interfaces from
Chapters 56 and 87, and the canonical adic completion from Chapter 96.
-/

namespace Formalization.Books.Algebra.Unit98

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open Formalization.Books.Algebra.Unit56
open Formalization.Books.Algebra.Unit87
open Formalization.Books.Algebra.Unit96
open scoped TensorProduct

universe u w

noncomputable section

/-! ## Adic limits of modules -/

/-- An inverse system is annihilated by the indicated power of `I` at every stage. -/
def IsPowerAnnihilated {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) : Prop :=
  ∀ n : ℕ+,
    Module.IsTorsionBySet A (F.obj (Opposite.op n))
      ((I ^ (n : ℕ) : Ideal A) : Set A)

/-- The quotient module occurring in the `n`th step of an `I`-adic system. -/
abbrev quotientModule {A : Type u} [CommRing A] (I : Ideal A)
    (M : ModuleCat.{w} A) (n : ℕ) : ModuleCat.{w} A :=
  ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))

/-- A source-faithful presentation of the transition map as a quotient map. -/
structure QuotientStep {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) (n : ℕ+) where
  equivalence : quotientModule I (F.obj (Opposite.op (n + 1))) (n : ℕ) ≅
    F.obj (Opposite.op n)
  transition_eq :
    ModuleCat.ofHom
        (equivalence.hom.hom.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))))) =
      transitionMap F (i := n + 1) (j := n)
        (PNat.lt_add_right n 1).le

/-- The transition maps of `F` are the canonical quotient maps by powers of `I`. -/
def IsQuotientInverseSystem {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) : Prop :=
  ∀ n : ℕ+, Nonempty (QuotientStep I F n)

/-- A quotient identification of the inverse limit with one of its stages. -/
structure LimitQuotientPresentation {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) (n : ℕ+) where
  equivalence :
    (inverseLimitModule F ⧸
      (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) ≃ₗ[A]
        F.obj (Opposite.op n)
  projection_eq :
    ModuleCat.ofHom
        (equivalence.toLinearMap.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (inverseLimitModule F))))) =
      limit.π F (Opposite.op n)

private theorem power_smul_top_eq_bot_of_torsion
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type w} [AddCommGroup M] [Module A M] (n : ℕ)
    (hM : Module.IsTorsionBySet A M ((I ^ n : Ideal A) : Set A)) :
    I ^ n • (⊤ : Submodule A M) = ⊥ := by
  apply le_antisymm
  · refine Submodule.smul_le.mpr ?_
    intro a ha x hx
    exact @hM x ⟨a, show a ∈ (I ^ n : Ideal A) from ha⟩
  · exact bot_le

private theorem isAdicComplete_of_completion_retraction
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type w} [AddCommGroup M] [Module A M]
    (hI : I.FG)
    (r : AdicCompletion I M →ₗ[A] M)
    (hr : r.comp (AdicCompletion.of I M) = LinearMap.id) :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨?_⟩
    intro x hx
    have hzero : AdicCompletion.of I M x = 0 := by
      apply IsHausdorff.haus (I := I)
        (inferInstance : IsHausdorff I (AdicCompletion I M))
      intro n
      rw [SModEq.sub_mem]
      have hmap :
          Submodule.map (AdicCompletion.of I M)
              (I ^ n • (⊤ : Submodule A M)) ≤
            I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right _ le_top
      have hxmem := hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hx n)))
      simpa using hxmem
    have hrex := congrArg (fun f => f x) hr
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hrex
    rw [← hrex, hzero, map_zero]
  · refine ⟨?_⟩
    intro f hf
    obtain ⟨z, hz⟩ := (AdicCompletion.isAdicComplete hI).toIsPrecomplete.prec'
      (fun n => AdicCompletion.of I M (f n)) (by
        intro m n hmn
        rw [SModEq.sub_mem]
        have hmap :
            Submodule.map (AdicCompletion.of I M)
                (I ^ m • (⊤ : Submodule A M)) ≤
              I ^ m • (⊤ : Submodule A (AdicCompletion I M)) := by
          rw [Submodule.map_smul'', Submodule.map_top]
          exact smul_mono_right _ le_top
        exact hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hf hmn))))
    refine ⟨r z, ?_⟩
    intro n
    rw [SModEq.sub_mem]
    have hmap :
        Submodule.map r (I ^ n • (⊤ : Submodule A (AdicCompletion I M))) ≤
          I ^ n • (⊤ : Submodule A M) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    have hzmem := hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hz n)))
    have hrex := congrArg (fun g => g (f n)) hr
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hrex
    simpa [map_sub, hrex] using hzmem

/-- The limit of a power-annihilated inverse system is adically complete. -/
theorem limit_complete_pre {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsPowerAnnihilated I F) :
    IsAdicComplete I (inverseLimitModule F) := by
  let hker (n : ℕ+) :
      I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) ≤
        LinearMap.ker (limit.π F (Opposite.op n)).hom := by
    refine Submodule.smul_le.mpr ?_
    intro a ha x hx
    change (limit.π F (Opposite.op n)).hom (a • x) = 0
    rw [map_smul]
    exact @hF n ((limit.π F (Opposite.op n)).hom x) ⟨a, ha⟩
  let q (n : ℕ+) :
      (inverseLimitModule F ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) →ₗ[A]
        F.obj (Opposite.op n) :=
    (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).liftQ
      (limit.π F (Opposite.op n)).hom (hker n)
  let c : Cone F :=
    { pt := ModuleCat.of A (AdicCompletion I (inverseLimitModule F))
      π :=
        { app := fun i =>
            ModuleCat.ofHom
              ((q i.unop).comp
                (AdicCompletion.eval I (inverseLimitModule F) (i.unop : ℕ)))
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            ext x
            apply AdicCompletion.induction_on I (inverseLimitModule F) x
            intro b
            have hproj :
                (F.map f).hom.comp (limit.π F i).hom =
                  (limit.π F j).hom := by
              exact congrArg ModuleCat.Hom.hom (limit.w F f)
            have hji : j.unop ≤ i.unop := leOfHom f.unop
            have hdiff : b.val j.unop - b.val i.unop ∈
                I ^ (j.unop : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) :=
              SModEq.sub_mem.mp (b.property hji)
            have hzero := hker j.unop hdiff
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hzero
            change
              (limit.π F j).hom (b.val j.unop) =
                (F.map f).hom ((limit.π F i).hom (b.val i.unop))
            calc
              (limit.π F j).hom (b.val j.unop) =
                  (limit.π F j).hom (b.val i.unop) := hzero
              _ = (F.map f).hom ((limit.π F i).hom (b.val i.unop)) := by
                exact (congrArg (fun y => y (b.val i.unop)) hproj).symm
      }
    }
  let r : AdicCompletion I (inverseLimitModule F) →ₗ[A]
      inverseLimitModule F :=
    (limit.lift F c).hom
  apply isAdicComplete_of_completion_retraction I hI r
  apply LinearMap.ext
  intro x
  apply Concrete.limit_ext F
  intro n
  change (limit.π F n).hom
      ((limit.lift F c).hom (AdicCompletion.of I (inverseLimitModule F) x)) =
    (limit.π F n).hom x
  rw [← ConcreteCategory.comp_apply, limit.lift_π]
  rfl

/-- A compatible quotient system has the expected quotients and complete limit. -/
theorem limit_complete {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsQuotientInverseSystem I F) :
    (∀ n : ℕ+, Nonempty (LimitQuotientPresentation I F n)) ∧
      IsAdicComplete I (inverseLimitModule F) := by
  /-
  Proof roadmap (Stacks, Algebra, Lemma `limit-complete`).

  The existing `QuotientStep` API identifies only successive maps.  In
  particular, neither `hF` nor `limit_complete_pre` currently supplies the two
  facts needed to use `Submodule.quotEquivOfEq`: surjectivity of `limit.π` and
  `ker (limit.π F (op n)).hom = I ^ n • ⊤`.  Prove those facts as follows.

  1. First extract from `s : QuotientStep I F k` that the successive map is
     surjective, using `s.transition_eq`, `Submodule.mkQ_surjective`, and
     an explicit preimage through `s.equivalence.inv` (the equality follows by
     `Iso.inv_hom_id_apply`).  Extend this to every transition by induction on
     `PNat` and `transitionMap_comp` from
     `Formalization/Books/Algebra/Unit87/InverseSystems.lean`.

  2. Add a local helper saying that every projection of a `NaturalInverseSystem`
     with surjective transitions is surjective.  For a prescribed element at
     stage `n`, use the functor of its compatible fibres and apply
     `Functor.isMittagLeffler_of_surjective` together with
     `Formalization.Books.Algebra.Unit86.nonempty_limit_of_countable_mittagLeffler`
     from `Unit86/MittagLefflerSystems.lean`.  Turn the resulting section into an
     element of the chosen module limit with `Types.isLimitEquivSections` and
     `isLimitOfPreserves (forget (ModuleCat.{w} A)) (limit.isLimit F)`.  This
     avoids the dead end of trying to apply
     `Types.surjective_π_app_zero_of_surjective_map`, which is specialized to an
     `ℕ`-system and only its zeroth projection.

  3. Put `L := inverseLimitModule F`, `p n := (limit.π F (op n)).hom`, and
     `K n := LinearMap.ker (p n)`.  The same calculation already used in the
     second branch below gives `I ^ n • (⊤ : Submodule A L) ≤ K n`.  The missing
     reverse inclusion is the kernel argument from the source.  Form
       `Q n := (K n : Type w) ⧸
         (I ^ n • (⊤ : Submodule A L)).comap (K n).subtype`.
     The denominator is the subtype form of `K n ⊓ I ^ n • ⊤`.
     From a lift through the quotient description at step `n`, prove that
     `K (n + 1) + I ^ n • ⊤` maps onto `K n`; after quotienting this gives
     surjective successive maps `Q (n + 1) ⟶ Q n`.  Package these maps as a
     type-valued inverse system (or a `ModuleCat` system) and use the helper in
     step 2 for its projections.

  4. A compatible family in the `Q n` maps coordinatewise to an element
     `z : AdicCompletion I L`: choose representatives in `K n`, package them
     with `AdicCompletion.AdicCauchySequence.mk`, and apply
     `AdicCompletion.mk`; compatibility is precisely congruence modulo
     `I ^ n • ⊤`.  By `limit_complete_pre I hI F`
     and `isAdicComplete_iff_completion_map_bijective` from
     `Formalization/Books/Algebra/Unit96/Completion.lean`, write
     `z = AdicCompletion.of I L y`.  At coordinate `n`, the representative lies
     in `K n` and `I ^ n • ⊤ ≤ K n`, hence `p n y = 0`.  Then
     `Concrete.limit_ext F` gives `y = 0`, so `z = 0` and every `Q n` is zero
     because its limit projection is surjective.  Thus `K n ≤ I ^ n • ⊤`.

  5. For each `n`, factor `p n` through `Submodule.liftQ`.  The kernel equality
     from step 4 and projection surjectivity from step 2 make the factor map
     bijective; package it with `LinearEquiv.ofBijective`.  Its defining
     equation with `Submodule.mkQ` is exactly `LimitQuotientPresentation.projection_eq`
     after `ModuleCat.hom_ext`.  Return this presentation in the first branch;
     retain the already completed `limit_complete_pre` argument in the second.
  -/
  constructor
  · have hstep : ∀ k : ℕ+, Function.Surjective
        (successiveTransitionMap F k).hom := by
      intro k
      rcases hF k with ⟨s⟩
      intro x
      obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
        (I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1)))))
        (s.equivalence.inv.hom x)
      refine ⟨z, ?_⟩
      have heq := congrArg ModuleCat.Hom.hom s.transition_eq
      rw [successiveTransitionMap, ← heq]
      change s.equivalence.hom.hom
        ((I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1))))).mkQ z) = x
      rw [hz]
      exact s.equivalence.inv_hom_id_apply x
    have hgeneral : ∀ (i j : ℕ+) (h : j ≤ i),
        Function.Surjective (transitionMap F (i := i) (j := j) h).hom := by
      intro i
      induction i using PNat.recOn with
      | one =>
          intro j h
          have hj : j = 1 := le_one_iff_eq_one.mp h
          subst j
          have hh : opHomOfLE h = 𝟙 (Opposite.op (1 : ℕ+)) := Subsingleton.elim _ _
          change Function.Surjective (F.map (opHomOfLE h)).hom
          rw [hh, F.map_id]
          exact Function.surjective_id
      | succ i ih =>
          intro j h
          rcases eq_or_lt_of_le h with rfl | hj
          · have hh : opHomOfLE h = 𝟙 (Opposite.op (i + 1)) := Subsingleton.elim _ _
            change Function.Surjective (F.map (opHomOfLE h)).hom
            rw [hh, F.map_id]
            exact Function.surjective_id
          · have hji : j ≤ i := PNat.lt_add_one_iff.mp hj
            have hcomp : transitionMap F (i := i + 1) (j := j) h =
                successiveTransitionMap F i ≫ transitionMap F (i := i) (j := j) hji := by
              change F.map (opHomOfLE h) =
                F.map (opHomOfLE (PNat.lt_add_right i 1).le) ≫ F.map (opHomOfLE hji)
              rw [← F.map_comp]
              congr 1
            rw [hcomp]
            exact (ih j hji).comp (hstep i)
    have hsurj : ∀ ⦃i j : ℕ+ᵒᵖ⦄ (f : i ⟶ j),
        Function.Surjective (F.map f).hom := by
      intro i j f
      let h : j.unop ≤ i.unop := leOfHom f.unop
      have hf : f = opHomOfLE h := Subsingleton.elim _ _
      rw [hf]
      exact hgeneral i.unop j.unop h
    have hproj_of_surj : ∀ (G : NaturalInverseSystem.{u, w} A),
        (∀ ⦃i j : ℕ+ᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (G.map f).hom) →
        ∀ n : ℕ+, Function.Surjective (limit.π G (Opposite.op n)).hom := by
      intro G hG n x
      have hstepG : ∀ k : ℕ+, Function.Surjective (successiveTransitionMap G k).hom := by
        intro k
        exact hG (opHomOfLE (PNat.lt_add_right k 1).le)
      let y : ∀ i : ℕ+, G.obj (Opposite.op i) := fun i =>
        PNat.recOn i
          (if hn : n = 1 then hn ▸ x else
            (transitionMap G (i := n) (j := 1) (by simp)).hom x)
          (fun i ih => if hni : n ≤ i then (hstepG i ih).choose
            else if hn : n = i + 1 then hn ▸ x
            else (transitionMap G (i := n) (j := i + 1)
              (PNat.add_one_le_iff.mpr (lt_of_not_ge hni))).hom x)
      have hy : ∀ i : ℕ+, (successiveTransitionMap G i).hom (y (i + 1)) = y i := by
        intro i
        induction i using PNat.recOn with
        | one =>
            by_cases hni : n ≤ 1
            · have hn : n = 1 := le_one_iff_eq_one.mp hni
              subst n
              simpa [y] using (hstepG 1 x).choose_spec
            · by_cases hn : n = 1 + 1
              · subst n
                have hn1 : ¬(1 + 1 : ℕ+) = 1 := by
                  exact ne_of_gt (PNat.lt_add_right 1 1)
                have hy2 : y (1 + 1) = x := by simp [y, hn1]
                have hy1 : y 1 =
                    (transitionMap G (i := 1 + 1) (j := 1)
                      (PNat.lt_add_right 1 1).le).hom x := by
                  simp [y, hn1]
                rw [hy2, hy1]
                rfl
              · have hlt : 1 + 1 ≤ n := PNat.add_one_le_iff.mpr (lt_of_not_ge hni)
                have hn1 : ¬n = 1 := by
                  intro hn1
                  subst n
                  exact hni le_rfl
                have hy2 : y (1 + 1) =
                    (transitionMap G (i := n) (j := 1 + 1) hlt).hom x := by
                  simp [y, hni, hn]
                have hy1 : y 1 =
                    (transitionMap G (i := n) (j := 1) (by simp)).hom x := by
                  simp [y, hn1]
                rw [hy2, hy1]
                change ((transitionMap G (i := n) (j := 1 + 1) hlt ≫
                    transitionMap G (i := 1 + 1) (j := 1)
                      (PNat.lt_add_right 1 1).le).hom) x = _
                exact congrArg (fun f => f.hom x)
                  (transitionMap_comp G hlt (PNat.lt_add_right 1 1).le)
        | succ i ih =>
            by_cases hni : n ≤ i + 1
            · have hs := (hstepG (i + 1) (y (i + 1))).choose_spec
              simpa [y, hni] using hs
            · by_cases hn : n = (i + 1) + 1
              · subst n
                have hni0 : ¬(i + 1) + 1 ≤ i + 1 := by
                  intro h
                  exact hni h
                have hni1 : ¬(i + 1) + 1 ≤ i := by
                  intro h
                  exact hni (h.trans (PNat.lt_add_right i 1).le)
                have hn0 : ¬(i + 1) + 1 = i + 1 := by
                  intro h
                  exact hni0 h.le
                have hn1 : ¬(i + 1) + 1 = i := by
                  intro h
                  exact hni1 (h.le)
                have hneq : ¬i + 1 = i := ne_of_gt (PNat.lt_add_right i 1)
                have hy2 : y ((i + 1) + 1) = x := by
                  simp [y, hni]
                have hy1 : y (i + 1) =
                    (transitionMap G (i := (i + 1) + 1) (j := i + 1)
                      (PNat.lt_add_right (i + 1) 1).le).hom x := by
                  simp [y, hni1, hneq]
                rw [hy2, hy1]
                rfl
              · have hni0 : ¬n ≤ i := by
                  intro h
                  exact hni (h.trans (PNat.lt_add_right i 1).le)
                have hlt : i + 1 ≤ n :=
                  PNat.add_one_le_iff.mpr (lt_of_not_ge hni0)
                have hn0 : ¬n = i + 1 := by
                  intro h
                  subst n
                  exact hni le_rfl
                have hlt' : (i + 1) + 1 ≤ n :=
                  PNat.add_one_le_iff.mpr (lt_of_not_ge hni)
                have hy2 : y ((i + 1) + 1) =
                    (transitionMap G (i := n) (j := (i + 1) + 1) hlt').hom x := by
                  simp [y, hni, hn]
                have hy1 : y (i + 1) =
                    (transitionMap G (i := n) (j := i + 1) hlt).hom x := by
                  simp [y, hni0, hn0]
                rw [hy2, hy1]
                change ((transitionMap G (i := n) (j := (i + 1) + 1) hlt' ≫
                    transitionMap G (i := (i + 1) + 1) (j := i + 1)
                      (PNat.lt_add_right (i + 1) 1).le).hom) x = _
                exact congrArg (fun f => f.hom x)
                  (transitionMap_comp G hlt' (PNat.lt_add_right (i + 1) 1).le)
      have hy' : (fun i : ℕ+ᵒᵖ => y i.unop) ∈ successiveCompatibleFamilies G := by
        intro i
        exact hy i
      let s : inverseLimitFamilies G :=
        ⟨fun i => y i.unop,
          (inverseLimitFamilies_iff_successiveCompatibleFamilies G _).2 hy'⟩
      let z : inverseLimitModule G := (inverseLimitModule_equiv_families G).symm s
      refine ⟨z, ?_⟩
      have hz : inverseLimitModule_equiv_families G z = s := by simp [z]
      have hz' := congrArg (fun q => q.1 (Opposite.op n)) hz
      have hcoord :
          (inverseLimitModule_equiv_families G z).1 (Opposite.op n) =
            (limit.π G (Opposite.op n)).hom z := by
        change (Types.limitEquivSections
          (G ⋙ CategoryTheory.forget (ModuleCat.{w} A))
          ((preservesLimitIso (CategoryTheory.forget (ModuleCat.{w} A)) G).hom.hom z)).1
            (Opposite.op n) = (limit.π G (Opposite.op n)).hom z
        rw [Types.limitEquivSections_apply]
        have hπ := congrArg (fun q => q.hom z)
          (preservesLimitIso_hom_π
            (CategoryTheory.forget (ModuleCat.{w} A)) G (Opposite.op n))
        change (limit.π (G ⋙ CategoryTheory.forget (ModuleCat.{w} A))
            (Opposite.op n)).hom
              ((preservesLimitIso (CategoryTheory.forget (ModuleCat.{w} A)) G).hom.hom z) =
            (limit.π G (Opposite.op n)).hom z at hπ
        exact hπ
      rw [hcoord] at hz'
      change (limit.π G (Opposite.op n)).hom z = y n at hz'
      have hyn : y n = x := by
        induction n using PNat.recOn with
        | one => simp [y]
        | succ n ih =>
            have hnot : ¬n + 1 ≤ n :=
              not_le_of_gt (PNat.lt_add_right n 1)
            simp [y, hnot]
      rw [hyn] at hz'
      exact hz'
    have hproj : ∀ n : ℕ+, Function.Surjective
        (limit.π F (Opposite.op n)).hom := hproj_of_surj F hsurj
    have hkerstep : ∀ k : ℕ+,
        LinearMap.ker (successiveTransitionMap F k).hom =
          I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1)))) := by
      intro k
      rcases hF k with ⟨s⟩
      have heq : s.equivalence.hom.hom ∘ₗ
            (I ^ (k : ℕ) • (⊤ : Submodule A
              (F.obj (Opposite.op (k + 1))))).mkQ =
          (successiveTransitionMap F k).hom := by
        have heq' := congrArg ModuleCat.Hom.hom s.transition_eq
        change s.equivalence.hom.hom ∘ₗ
              (I ^ (k : ℕ) • (⊤ : Submodule A
                (F.obj (Opposite.op (k + 1))))).mkQ =
            (successiveTransitionMap F k).hom at heq'
        exact heq'
      apply le_antisymm
      · intro x hx
        have hx' : s.equivalence.hom.hom
            ((I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1))))).mkQ x) = 0 := by
          change (s.equivalence.hom.hom ∘ₗ
            (I ^ (k : ℕ) • (⊤ : Submodule A
              (F.obj (Opposite.op (k + 1))))).mkQ) x = 0
          rw [heq]
          exact hx
        have hmk : (I ^ (k : ℕ) •
            (⊤ : Submodule A (F.obj (Opposite.op (k + 1))))).mkQ x = 0 := by
          have hmk' := congrArg (fun y => s.equivalence.inv.hom y) hx'
          simpa using hmk'
        exact (Submodule.Quotient.mk_eq_zero _).mp hmk
      · refine Submodule.smul_le.mpr ?_
        intro a ha x hx
        change (successiveTransitionMap F k).hom (a • x) = 0
        rw [← heq]
        change s.equivalence.hom.hom
          ((I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1))))).mkQ (a • x)) = 0
        have hmk : (I ^ (k : ℕ) •
            (⊤ : Submodule A (F.obj (Opposite.op (k + 1))))).mkQ (a • x) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact Submodule.smul_mem_smul ha hx
        rw [hmk, map_zero]
    let K (n : ℕ+) : Submodule A (inverseLimitModule F) :=
      LinearMap.ker (limit.π F (Opposite.op n)).hom
    let D (n : ℕ+) : Submodule A (K n) :=
      (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).comap (K n).subtype
    let Q (n : ℕ+) : ModuleCat.{w} A := ModuleCat.of A ((K n : Type w) ⧸ D n)
    have hKmono : ∀ ⦃i j : ℕ+⦄ (h : j ≤ i), K i ≤ K j := by
      intro i j h x hx
      have heq := congrArg ModuleCat.Hom.hom (limit.w F (opHomOfLE h))
      change (limit.π F (Opposite.op j)).hom x = 0
      rw [← heq]
      change (F.map (opHomOfLE h)).hom
        ((limit.π F (Opposite.op i)).hom x) = 0
      rw [hx, map_zero]
    let kinc {i j : ℕ+} (h : j ≤ i) : K i →ₗ[A] K j :=
      { toFun := fun x => ⟨x, hKmono h x.property⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    have hDmap : ∀ ⦃i j : ℕ+⦄ (h : j ≤ i), D i ≤ (D j).comap (kinc h) := by
      intro i j h x hx
      change (x : inverseLimitModule F) ∈ I ^ (j : ℕ) • (⊤ : Submodule A (inverseLimitModule F))
      exact (Submodule.smul_mono_left
        (Ideal.pow_le_pow_right (show (j : ℕ) ≤ i from h))) hx
    let qmap {i j : ℕ+} (h : j ≤ i) : Q i ⟶ Q j :=
      ModuleCat.ofHom ((D i).mapQ (D j) (kinc h) (hDmap h))
    let Qsys : NaturalInverseSystem A :=
      { obj := fun i => Q i.unop
        map := fun {i j} f => qmap (leOfHom f.unop)
        map_id := by
          intro i; apply ModuleCat.hom_ext; ext x
          change (D (Opposite.unop i)).mkQ
              ((kinc (le_rfl : Opposite.unop i ≤ Opposite.unop i)) x) =
            (D (Opposite.unop i)).mkQ x
          rfl
        map_comp := by
          intro i j k f g; apply ModuleCat.hom_ext; ext x
          change (D (Opposite.unop k)).mkQ
              ((kinc (leOfHom (f ≫ g).unop)) x) =
            (D (Opposite.unop k)).mkQ
              ((kinc (leOfHom g.unop))
                ((kinc (leOfHom f.unop)) x))
          congr 1 }
    have hqstep : ∀ k : ℕ+, Function.Surjective
        (Qsys.map (opHomOfLE (PNat.lt_add_right k 1).le)).hom := by
      intro k q
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (D k) q
      have hxtrans : (successiveTransitionMap F k).hom
          ((limit.π F (Opposite.op (k + 1))).hom x) = 0 := by
        have heq := congrArg ModuleCat.Hom.hom
          (limit.w F (opHomOfLE (PNat.lt_add_right k 1).le))
        have heq' := congrArg (fun f => f (x : inverseLimitModule F)) heq
        change (F.map (opHomOfLE (PNat.lt_add_right k 1).le)).hom
            ((limit.π F (Opposite.op (k + 1))).hom (x : inverseLimitModule F)) =
          (limit.π F (Opposite.op k)).hom (x : inverseLimitModule F) at heq'
        change (F.map (opHomOfLE (PNat.lt_add_right k 1).le)).hom
          ((limit.π F (Opposite.op (k + 1))).hom (x : inverseLimitModule F)) = 0
        exact heq'.trans x.property
      have hxmem : (limit.π F (Opposite.op (k + 1))).hom x ∈
          I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1)))) := by
        rw [← hkerstep k]; exact hxtrans
      have hmap : Submodule.map (limit.π F (Opposite.op (k + 1))).hom
          (I ^ (k : ℕ) • (⊤ : Submodule A (inverseLimitModule F))) =
          I ^ (k : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (k + 1)))) := by
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.2 (hproj (k + 1))]
      obtain ⟨z, hz, hpz⟩ :=
        (Submodule.mem_map (f := (limit.π F (Opposite.op (k + 1))).hom)
          (p := I ^ (k : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))).1 (hmap ▸ hxmem)
      have hu : (limit.π F (Opposite.op (k + 1))).hom (x - z) = 0 := by
        rw [map_sub, hpz]; abel
      let u : K (k + 1) := ⟨x - z, hu⟩
      refine ⟨(D (k + 1)).mkQ u, ?_⟩
      rw [← hx]
      change ((D (k + 1)).mapQ (D k) (kinc (PNat.lt_add_right k 1).le)
          (hDmap (PNat.lt_add_right k 1).le))
          ((D (k + 1)).mkQ u) = (D k).mkQ x
      change (D k).mkQ ((kinc (PNat.lt_add_right k 1).le) u) = (D k).mkQ x
      apply (Submodule.Quotient.eq _).2
      change (u : inverseLimitModule F) - (x : inverseLimitModule F) ∈
        I ^ (k : ℕ) • (⊤ : Submodule A (inverseLimitModule F))
      simpa [u] using (Submodule.neg_mem _ hz)
    have hqgeneral : ∀ (i j : ℕ+) (h : j ≤ i),
        Function.Surjective (Qsys.map (opHomOfLE h)).hom := by
      intro i
      induction i using PNat.recOn with
      | one =>
          intro j h
          have hj : j = 1 := le_one_iff_eq_one.mp h
          subst j
          have hh : opHomOfLE h = 𝟙 (Opposite.op (1 : ℕ+)) := Subsingleton.elim _ _
          change Function.Surjective (Qsys.map (opHomOfLE h)).hom
          rw [hh, Qsys.map_id]
          exact Function.surjective_id
      | succ i ih =>
          intro j h
          rcases eq_or_lt_of_le h with rfl | hj
          · have hh : opHomOfLE h = 𝟙 (Opposite.op (i + 1)) := Subsingleton.elim _ _
            change Function.Surjective (Qsys.map (opHomOfLE h)).hom
            rw [hh, Qsys.map_id]
            exact Function.surjective_id
          · have hji : j ≤ i := PNat.lt_add_one_iff.mp hj
            have hcomp : Qsys.map (opHomOfLE h) =
                Qsys.map (opHomOfLE (PNat.lt_add_right i 1).le) ≫
                  Qsys.map (opHomOfLE hji) := by
              rw [← Qsys.map_comp]
            rw [hcomp]
            exact (ih j hji).comp (hqstep i)
    have hQsurj : ∀ ⦃i j : ℕ+ᵒᵖ⦄ (f : i ⟶ j),
        Function.Surjective (Qsys.map f).hom := by
      intro i j f
      let h : j.unop ≤ i.unop := leOfHom f.unop
      have hf : f = opHomOfLE h := Subsingleton.elim _ _
      rw [hf]
      exact hqgeneral i.unop j.unop h
    have hQproj : ∀ n : ℕ+, Function.Surjective
        (limit.π Qsys (Opposite.op n)).hom := hproj_of_surj Qsys hQsurj
    have hpower : IsPowerAnnihilated I F := by
      intro n
      rcases hF n with ⟨s⟩
      intro x a
      obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
        (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1)))))
        (s.equivalence.inv.hom x)
      calc
        (a : A) • x = (a : A) • s.equivalence.hom.hom (s.equivalence.inv.hom x) := by simp
        _ = s.equivalence.hom.hom ((a : A) • s.equivalence.inv.hom x) := by rw [map_smul]
        _ = s.equivalence.hom.hom ((a : A) •
            (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z) := by rw [← hz]
        _ = 0 := by
          have haz : (I ^ (n : ℕ) •
              (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ ((a : A) • z) = 0 := by
            apply (Submodule.Quotient.mk_eq_zero _).mpr
            exact Submodule.smul_mem_smul a.property (by simp)
          rw [show (a : A) •
              (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z =
              (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ ((a : A) • z) by
                simp only [map_smul], haz, map_zero]
    have hLker : ∀ n : ℕ+,
        I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) ≤ K n := by
      intro n
      refine Submodule.smul_le.mpr ?_
      intro a ha x hx
      change (limit.π F (Opposite.op n)).hom (a • x) = 0
      rw [map_smul]
      exact @hpower n ((limit.π F (Opposite.op n)).hom x) ⟨a, ha⟩
    have hcomplete : IsAdicComplete I (inverseLimitModule F) :=
      limit_complete_pre I hI F hpower
    have hof : Function.Bijective (AdicCompletion.of I (inverseLimitModule F)) :=
      (isAdicComplete_iff_completion_map_bijective I (inverseLimitModule F)).mp hcomplete
    have hQlimit_zero : ∀ q : inverseLimitModule Qsys, q = 0 := by
      intro q
      let a : ∀ m : ℕ, K (Nat.succPNat m) := fun m =>
        (Submodule.Quotient.mk_surjective (D (Nat.succPNat m))
          ((limit.π Qsys (Opposite.op (Nat.succPNat m))).hom q)).choose
      have ha : ∀ m : ℕ,
          (D (Nat.succPNat m)).mkQ (a m) =
            (limit.π Qsys (Opposite.op (Nat.succPNat m))).hom q := by
        intro m
        exact (Submodule.Quotient.mk_surjective (D (Nat.succPNat m))
          ((limit.π Qsys (Opposite.op (Nat.succPNat m))).hom q)).choose_spec
      have hcauchy : ∀ m : ℕ,
          (a m : inverseLimitModule F) ≡ (a (m + 1) : inverseLimitModule F)
            [SMOD (I ^ m • (⊤ : Submodule A (inverseLimitModule F)))] := by
        intro m
        apply SModEq.sub_mem.mpr
        have hw := congrArg (fun f => f q)
          (limit.w Qsys (opHomOfLE
            (PNat.lt_add_right (Nat.succPNat m) 1).le))
        have hw' :
            (Qsys.map (opHomOfLE (PNat.lt_add_right (Nat.succPNat m) 1).le)).hom
                ((limit.π Qsys (Opposite.op (Nat.succPNat (m + 1)))).hom q) =
              (limit.π Qsys (Opposite.op (Nat.succPNat m))).hom q := hw
        have ha' (r : ℕ) : (D (Nat.succPNat r)).mkQ (a r) =
            (limit.π Qsys (Opposite.op (Nat.succPNat r))).hom q := ha r
        rw [← ha' (m + 1), ← ha' m] at hw'
        have hmn : Nat.succPNat m ≤ Nat.succPNat (m + 1) := by
          simpa only [Nat.succ_eq_add_one, PNat.add_one, Nat.succPNat_coe] using
            (PNat.lt_add_right (Nat.succPNat m) 1).le
        change (D (Nat.succPNat (m + 1))).mapQ (D (Nat.succPNat m))
            (kinc hmn) (hDmap hmn)
            ((D (Nat.succPNat (m + 1))).mkQ (a (m + 1))) =
          (D (Nat.succPNat m)).mkQ (a m) at hw'
        change (D (Nat.succPNat m)).mkQ (kinc hmn (a (m + 1))) =
          (D (Nat.succPNat m)).mkQ (a m) at hw'
        have hmem := (Submodule.Quotient.eq _).mp hw'
        change (a (m + 1) : inverseLimitModule F) - (a m : inverseLimitModule F) ∈
          I ^ (m + 1) • (⊤ : Submodule A (inverseLimitModule F)) at hmem
        have hmem' := Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (Nat.le_succ m)) hmem
        simpa only [neg_sub] using (Submodule.neg_mem _ hmem')
      let c : AdicCompletion.AdicCauchySequence I (inverseLimitModule F) :=
        AdicCompletion.AdicCauchySequence.mk I (inverseLimitModule F)
          (fun m => (a m : inverseLimitModule F)) hcauchy
      let z := AdicCompletion.mk I (inverseLimitModule F) c
      obtain ⟨y, hy⟩ := hof.2 z
      have hcoord : ∀ m : ℕ+,
          (limit.π F (Opposite.op m)).hom y = 0 := by
        intro m
        have heval := congrArg (AdicCompletion.eval I (inverseLimitModule F) (m : ℕ)) hy
        have heval' :
            (I ^ (m : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).mkQ y =
              (I ^ (m : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).mkQ
                (a m) := by
          simpa [z, c, AdicCompletion.eval_of] using heval
        have hya := (Submodule.Quotient.eq _).mp heval'
        have hzero := hLker m hya
        have haK : (a m : inverseLimitModule F) ∈ K m :=
          hKmono (PNat.lt_add_right m 1).le (a m).property
        have hpa : (limit.π F (Opposite.op m)).hom
            (a m : inverseLimitModule F) = 0 := haK
        change (limit.π F (Opposite.op m)).hom
            (y - (a m : inverseLimitModule F)) = 0 at hzero
        rw [map_sub, hpa] at hzero
        simpa using hzero
      have hyzero : y = 0 := by
        apply Concrete.limit_ext F
        intro m
        simpa using hcoord m.unop
      have hzzero : z = 0 := by
        rw [← hy, hyzero, map_zero]
      apply Concrete.limit_ext Qsys
      intro i
      let n := i.unop
      have heval := congrArg
        (AdicCompletion.eval I (inverseLimitModule F) (n : ℕ)) hzzero
      have hamem : (a n : inverseLimitModule F) ∈
          I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) := by
        have heval' :
            (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).mkQ (a n) = 0 := by
          simpa [z, c, n, AdicCompletion.eval_of] using heval
        exact (Submodule.Quotient.mk_eq_zero _).mp heval'
      have hstepq := congrArg (fun f => f q)
        (limit.w Qsys (opHomOfLE (PNat.lt_add_right n 1).le))
      have hstepq' :
          (Qsys.map (opHomOfLE (PNat.lt_add_right n 1).le)).hom
              ((limit.π Qsys (Opposite.op (n + 1))).hom q) =
            (limit.π Qsys (Opposite.op n)).hom q := hstepq
      have han : (D (n + 1)).mkQ (a n) =
          (limit.π Qsys (Opposite.op (n + 1))).hom q := by
        exact ha n
      rw [← han] at hstepq'
      have hnn : n ≤ n + 1 := (PNat.lt_add_right n 1).le
      change (D (n + 1)).mapQ (D n) (kinc hnn) (hDmap hnn)
          ((D (n + 1)).mkQ (a n)) =
        (limit.π Qsys (Opposite.op n)).hom q at hstepq'
      have hqzero : (D n).mkQ (kinc (PNat.lt_add_right n 1).le (a n)) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change (a n : inverseLimitModule F) ∈
          I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))
        exact hamem
      change (D n).mkQ (kinc hnn (a n)) =
        (limit.π Qsys (Opposite.op n)).hom q at hstepq'
      rw [hqzero] at hstepq'
      simpa using hstepq'.symm
    have hQelt : ∀ (n : ℕ+) (q : Q n), q = 0 := by
      intro n q
      obtain ⟨z, hz⟩ := hQproj n q
      calc
        q = (limit.π Qsys (Opposite.op n)).hom z := hz.symm
        _ = (limit.π Qsys (Opposite.op n)).hom 0 := by rw [hQlimit_zero z]
        _ = 0 := map_zero _
    have hker : ∀ n : ℕ+,
        LinearMap.ker (limit.π F (Opposite.op n)).hom =
          I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) := by
      intro n
      apply le_antisymm
      · intro x hx
        have hq : (D n).mkQ (⟨x, hx⟩ : K n) = 0 := hQelt n ((D n).mkQ ⟨x, hx⟩)
        have hqmem := (Submodule.Quotient.mk_eq_zero (D n)).mp hq
        change (x : inverseLimitModule F) ∈
          I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) at hqmem
        exact hqmem
      · exact hLker n
    intro n
    let q : (inverseLimitModule F ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) →ₗ[A]
        F.obj (Opposite.op n) :=
      (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).liftQ
        (limit.π F (Opposite.op n)).hom (hLker n)
    have hqker : LinearMap.ker q = ⊥ := by
      apply Submodule.ker_liftQ_eq_bot
      rw [hker n]
    have hqinj : Function.Injective q := LinearMap.ker_eq_bot.mp hqker
    have hqsurj : Function.Surjective q := by
      intro y
      obtain ⟨x, hx⟩ := hproj n y
      refine ⟨(I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).mkQ x, ?_⟩
      change (limit.π F (Opposite.op n)).hom x = y
      exact hx
    let e : (inverseLimitModule F ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) ≃ₗ[A]
        F.obj (Opposite.op n) := LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩
    refine ⟨{ equivalence := e, projection_eq := ?_ }⟩
    apply ModuleCat.hom_ext
    ext x
    change e ((I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).mkQ x) =
      (limit.π F (Opposite.op n)).hom x
    have hfactor := Submodule.liftQ_mkQ
      (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))
      (limit.π F (Opposite.op n)).hom (hLker n)
    exact congrArg (fun f => f x) hfactor
  · apply limit_complete_pre I hI F
    intro n
    rcases hF n with ⟨s⟩
    intro x a
    obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
      (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1)))))
      (s.equivalence.inv.hom x)
    calc
      (a : A) • x = (a : A) • s.equivalence.hom.hom (s.equivalence.inv.hom x) := by simp
      _ = s.equivalence.hom.hom ((a : A) • s.equivalence.inv.hom x) := by
        rw [map_smul]
      _ = s.equivalence.hom.hom ((a : A) •
          (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z) := by
        rw [← hz]
      _ = 0 := by
        have haz :
            (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ
                ((a : A) • z) = 0 := by
          change Submodule.Quotient.mk ((a : A) • z) = 0
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact Submodule.smul_mem_smul a.property (by simp)
        calc
          s.equivalence.hom.hom ((a : A) •
              (I ^ (n : ℕ) •
                (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z) =
              s.equivalence.hom.hom
                ((I ^ (n : ℕ) •
                  (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ
                    ((a : A) • z)) := by
            simp only [map_smul]
          _ = 0 := by rw [haz, map_zero]

/-! ## Graded inverse systems -/

/-- An inverse system of internally graded modules whose transition maps preserve degree. -/
structure GradedInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) where
  system : NaturalInverseSystem.{u, w} A
  grading : ∀ n : ℕ+, GradedModuleData G (system.obj (Opposite.op n))
  map_isGraded : ∀ (n m : ℕ+) (h : m ≤ n),
    IsGradedLinearMap G (grading n) (grading m)
      (transitionMap system (i := n) (j := m) h).hom

/-- Finiteness of every module in a graded inverse system. -/
def IsFiniteGradedInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) : Prop :=
  ∀ n : ℕ+, Module.Finite A (F.system.obj (Opposite.op n))

/-- A graded presentation of a quotient by a homogeneous submodule. -/
structure GradedQuotientPresentation {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    {M N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) (n : ℕ) where
  quotient : GradedModuleData G (M ⧸ (I ^ n • (⊤ : Submodule A M)))
  projection_isGraded :
    IsGradedLinearMap G 𝓜 quotient
      (Submodule.mkQ (I ^ n • (⊤ : Submodule A M)))
  equivalence : GradedLinearEquiv G quotient 𝓝

/-- A graded inverse-system step with its canonical quotient map. -/
structure GradedQuotientStep {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, w} G) (n : ℕ+) where
  quotient :
    GradedModuleData G
      (F.system.obj (Opposite.op (n + 1)) ⧸
        (I ^ (n : ℕ) •
          (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))) )
  projection_isGraded :
    IsGradedLinearMap G (F.grading (n + 1)) quotient
      (Submodule.mkQ (I ^ (n : ℕ) •
        (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))))
  equivalence : GradedLinearEquiv G quotient (F.grading n)
  transition_eq :
    ModuleCat.ofHom
        (equivalence.toLinearEquiv.toLinearMap.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))))) =
      transitionMap F.system (i := n + 1) (j := n)
        (PNat.lt_add_right n 1).le

/-- The transition maps of a graded system are quotient maps by powers of `I`. -/
def IsGradedQuotientInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, w} G) : Prop :=
  ∀ n : ℕ+, Nonempty (GradedQuotientStep G I F n)

/-- The finiteness theorem for graded inverse systems. -/
theorem finiteness_graded {A : Type u} [CommRing A] [IsNoetherianRing A]
    (G : GradedRingData A) (I : Ideal A)
    (hI : I ≤ irrelevantIdeal G) (hIhom : I.IsHomogeneous G.component)
    (F : GradedInverseSystem.{u, w} G)
    (hF : IsGradedQuotientInverseSystem G I F)
    (hfinite : IsFiniteGradedInverseSystem G F) :
    ∃ N : ModuleCat.{w} A, ∃ 𝓝 : GradedModuleData G N,
      Module.Finite A N ∧
        ∀ n : ℕ+,
          Nonempty
            (GradedQuotientPresentation G I 𝓝 (F.grading n) (n : ℕ)) := by
  /-
  Proof roadmap (Stacks, Algebra, Lemma `finiteness-graded`).

  The graded-step interface is mathematically sufficient, but it does not yet
  expose a common graded source, homogeneous lifts through a quotient, or the
  degree-stabilization lemma.  Construct those locally; taking the ungraded
  inverse limit as `N` is a dead end (for example it is a power-series module
  and need not carry an internal direct-sum grading).

  1. Use `hfinite 1` and `Module.Finite.exists_fin` to choose finitely many
     generators of stage `1`.  Replace them by their finitely many homogeneous
     pieces using `DirectSum.sum_support_decompose` for `(F.grading 1).component`,
     exactly as in the private helper `graded_finite_homogeneous_generators` in
     `Formalization/Books/Algebra/Unit56/GradedRings.lean`.  Record the resulting
     number `r`, degrees `d : Fin r → ℤ`, and homogeneous generators `x 1 i`.
     Treat `r = 0` separately: graded Nakayama makes every stage zero and the
     zero graded module supplies the conclusion.

  2. For `s : GradedQuotientStep G I F n`, prove that its quotient projection
     is surjective on every homogeneous component.  Given a homogeneous target,
     lift it with `s.equivalence.toLinearEquiv.symm` and
     `Submodule.mkQ_surjective`, decompose an arbitrary source lift, and use
     uniqueness of `DirectSum.decompose` plus `s.projection_isGraded` to retain
     only the requested component.  Recursively choose homogeneous
     `x (n + 1) i` lifting `x n i` with `PNat.recOn`.  Successive compatibility
     extends to all transitions by `transitionMap_comp` (or via
     `inverseLimitFamilies_iff_successiveCompatibleFamilies` in
     `Unit87/InverseSystems.lean`).

  3. Prove by induction on `n - m` that for `m ≤ n` the transition
     `F_n ⟶ F_m` is surjective with kernel
       `I ^ (m : ℕ) • (⊤ : Submodule A (F.system.obj (op n)))`.
     The successor case uses `GradedQuotientStep.transition_eq`,
     `Submodule.Quotient.mk_eq_zero`, `Submodule.map_smul''`, and the nesting
     `I ^ (m + 1) ≤ I ^ m`.  This is the precise bridge absent from `hF`.
     It implies that the lifts `x n i` generate stage `n` modulo
     `I • ⊤`, hence modulo `irrelevantIdeal G • ⊤` by `hI`.  With the local
     instance `letI := hfinite n`, apply `graded_nakayama_generators` from
     `Unit56/GradedRings.lean` to show that the `x n i` generate `F_n`.

  4. Use the compatible families `x n i` and
     `(inverseLimitModule_equiv_families F.system).symm` to obtain
       `ξ i : inverseLimitModule F.system`
     with `(limit.π F.system (op n)).hom (ξ i) = x n i`; verify the equation
     with `Types.isLimitEquivSections_apply`.  Let `L := inverseLimitModule
     F.system` and `Nsub := Submodule.span A (Set.range ξ) ≤ L`.  This choice is
     universe-critical: `L : ModuleCat.{w} A`, so the subtype `Nsub` is still
     `Type w`.  A tempting free presentation `Fin r → A` lives in universe `u`
     and cannot produce the required `ModuleCat.{w} A` when `u` and `w` are
     unrelated.

  5. Establish the low-degree lemma: if `e < min_i(d i) + m`, then the
     degree-`e` part of `I ^ m • F_n` is zero.  Decompose coefficients using
     `Ideal.IsHomogeneous.mem_iff` (with powers obtained inductively from
     `hIhom.mul`), use `hI : I ≤ irrelevantIdeal G`, and
     `HomogeneousIdeal.mem_irrelevant_iff` to see that every nonzero homogeneous
     factor from `I` has degree at least one; then use the homogeneous
     generators from step 3.  Consequently the transition map identifies the
     degree-`e` pieces of stages `n` and `m` once `m ≤ n` and
     `e < min_i(d i) + m`.

  6. Grade `Nsub` by compatible homogeneous families: its degree-`e`
     `AddSubgroup` consists of the `z : Nsub` such that every coordinate
     `(limit.π F.system (op n)).hom z` lies in `(F.grading n).component e`.
     Existence of a finite homogeneous decomposition follows by
     `Submodule.span_induction` on the generators `ξ i`, decomposing each scalar
     with `DirectSum.sum_support_decompose G.component`.  Uniqueness follows
     coordinatewise from the stage decompositions and then from
     `Concrete.limit_ext F.system`.  Scalar compatibility is coordinatewise
     `F.grading n |>.gradedSMul.smul_mem`.  These facts give
       `𝓝 : GradedModuleData G Nsub`.
     Set `N := ModuleCat.of A Nsub`; the equality defining `Nsub` as the span of
     the finite set `Set.range ξ` directly supplies `Module.Finite A Nsub`
     (`Module.Finite` is `Submodule.FG` for `⊤`).

  7. Restrict each limit projection to
     `p n : Nsub →ₗ[A] F.system.obj (op n)`.
     It is graded by the definition in step 6 and surjective because the
     coordinates `x n i` generate stage `n`.  Its kernel is exactly
     `I ^ n • (⊤ : Submodule A Nsub)`: power annihilation gives
     `I ^ n • ⊤ ≤ LinearMap.ker (p n)`; for the reverse inclusion, decompose a
     kernel element into finitely many homogeneous pieces, choose a stage above
     all of their stabilization bounds from step 5, lift the resulting
     `I ^ n`-multiples using the generators `ξ i`, and use the eventual
     component isomorphisms plus `Concrete.limit_ext F.system`.

     Factor `p n` through `Submodule.liftQ` and use
     `LinearEquiv.ofBijective` to obtain the required equivalence.
     Transport the stage grading back along that equivalence to define the
     quotient grading; the equation with the factored `p n` proves
     `projection_isGraded`, while the map and its inverse preserve components
     by construction.  These fields assemble
     `GradedQuotientPresentation G I 𝓝 (F.grading n) n`.
  -/
  sorry

/-! ## The Daniel--Litt comparison -/

/-- A compatible system of degree-preserving maps from one graded module. -/
structure GradedCompatibleMap {A : Type u} [CommRing A]
    (G : GradedRingData A) {M : Type w} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (F : GradedInverseSystem.{u, w} G) where
  map : ∀ n : ℕ+, M →ₗ[A] F.system.obj (Opposite.op n)
  isGraded : ∀ n : ℕ+, IsGradedLinearMap G 𝓜 (F.grading n) (map n)
  compatible : ∀ (n m : ℕ+) (h : m ≤ n),
    (transitionMap F.system (i := n) (j := m) h).hom.comp (map n) = map m

/-- The component map of a transition morphism between graded modules. -/
def gradedComponentMap {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    AddCommGrpCat.of ((F.grading i.unop).component d) ⟶
      AddCommGrpCat.of ((F.grading j.unop).component d) :=
  AddCommGrpCat.ofHom
    (componentAddHom G (F.grading i.unop) (F.grading j.unop)
      (transitionMap F.system (leOfHom f.unop)).hom
      (F.map_isGraded i.unop j.unop (leOfHom f.unop)) d)

theorem gradedComponentMap_id {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    (i : ℕ+ᵒᵖ) :
    gradedComponentMap G F d (𝟙 i) = 𝟙 _ := by
  simp only [gradedComponentMap, transitionMap_refl]
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

theorem gradedComponentMap_comp {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    {i j k : ℕ+ᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    gradedComponentMap G F d (f ≫ g) =
      gradedComponentMap G F d f ≫ gradedComponentMap G F d g := by
  simp only [gradedComponentMap]
  apply AddCommGrpCat.hom_ext
  ext x
  change (transitionMap F.system (leOfHom (f ≫ g).unop)).hom x =
    (transitionMap F.system (leOfHom g.unop)).hom
      ((transitionMap F.system (leOfHom f.unop)).hom x)
  rw [← ConcreteCategory.comp_apply, transitionMap_comp]

/-- The inverse system of degree-`d` components. -/
def gradedComponentSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ) :
    InverseSystem ℕ+ (AddCommGrpCat.{w}) where
  obj i := AddCommGrpCat.of ((F.grading i.unop).component d)
  map := gradedComponentMap G F d
  map_id := by
    intro i
    exact gradedComponentMap_id G F d i
  map_comp := by
    intro i j k f g
    exact gradedComponentMap_comp G F d f g

/-- The limit of the degree-`d` components of a graded inverse system. -/
abbrev gradedComponentLimit {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ) :
    AddCommGrpCat.{w} :=
  InverseSystemLimit (gradedComponentSystem G F d)

/- The following three declarations expose the canonical coordinatewise map
   `M ⊗ A' → G_n` and the induced map to the inverse limit.  The quotient-module
   action is Mathlib's `Module.IsTorsionBySet.module`, transported along the
   canonical map `A' → A/I^n`. -/

noncomputable abbrev completionModule {A : Type u} [CommRing A] (I : Ideal A)
    (n : ℕ) {N : Type w} [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A)) :
    Module (ringCompletion I) N := by
  letI : SMul (A ⧸ I ^ n) N := hN.hasSMul
  letI : Module (A ⧸ I ^ n) N := hN.module
  exact Module.compHom N (AdicCompletion.evalₐ I n).toRingHom

theorem completionModuleScalarTower {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {N : Type w} [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A)) :
    @IsScalarTower A (ringCompletion I) N Algebra.toSMul
      (completionModule I n hN).toSMul _ :=
  letI : Module (A ⧸ I ^ n) N := hN.module
  by
    let completionSMul : SMul (ringCompletion I) N :=
      (completionModule I n hN).toSMul
    refine @IsScalarTower.mk A (ringCompletion I) N Algebra.toSMul
      completionSMul _ ?_
    intro a b x
    have hsmul (c : ringCompletion I) (y : N) :
        completionSMul.smul c y = (AdicCompletion.evalₐ I n c) • y := by
      change
        (letI : SMul (A ⧸ I ^ n) N := hN.hasSMul
         letI : Module (A ⧸ I ^ n) N := hN.module
         (Module.compHom N (AdicCompletion.evalₐ I n).toRingHom).toSMul).smul c y = _
      rfl
    rw [Algebra.smul_def]
    change completionSMul.smul ((algebraMap A (ringCompletion I)) a * b) x =
      a • completionSMul.smul b x
    rw [hsmul, hsmul]
    rw [map_mul]
    have halg :
        (AdicCompletion.evalₐ I n) ((algebraMap A (ringCompletion I)) a) =
          Ideal.Quotient.mk (I ^ n) a := by
      rw [show algebraMap A (ringCompletion I) a = AdicCompletion.of I A a by rfl,
        AdicCompletion.evalₐ_of]
    rw [halg, @SemigroupAction.mul_smul (A ⧸ I ^ n) N _
      hN.module.toDistribMulAction.toSemigroupAction]
    simpa only [Module.IsTorsionBySet.module] using
      (Module.IsTorsionBySet.mk_smul hN a
        ((AdicCompletion.evalₐ I n) b • x))

noncomputable def completionTensorCoordinate {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {M N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A))
    (f : M →ₗ[A] N) :
    M ⊗[A] ringCompletion I →ₗ[A] N := by
  letI : Module (A ⧸ I ^ n) N := hN.module
  letI : Module (ringCompletion I) N := completionModule I n hN
  letI : IsScalarTower A (ringCompletion I) N :=
    completionModuleScalarTower I n hN
  exact TensorProduct.lift
    (((Algebra.lsmul (R := A) (A := ringCompletion I) (B := A) N).toLinearMap.flip).comp f)

theorem completionTensorCoordinate_naturality
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    (F.system.map f).hom.comp
        (completionTensorCoordinate I (i.unop : ℕ) (hF i.unop)
          (φ.map i.unop)) =
      completionTensorCoordinate I (j.unop : ℕ) (hF j.unop)
        (φ.map j.unop) := by
  let : Module (A ⧸ I ^ (i.unop : ℕ)) (F.system.obj i) := (hF i.unop).module
  let : Module (A ⧸ I ^ (j.unop : ℕ)) (F.system.obj j) := (hF j.unop).module
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m r =>
    induction r using AdicCompletion.induction_on I A with
    | _ a =>
      change (F.system.map f).hom
          ((AdicCompletion.evalₐ I (i.unop : ℕ) (AdicCompletion.mk I A a)) •
            (φ.map i.unop) m) =
        (AdicCompletion.evalₐ I (j.unop : ℕ) (AdicCompletion.mk I A a)) •
          (φ.map j.unop) m
      rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
      change (F.system.map f).hom ((a.val i.unop) • (φ.map i.unop) m) =
        (a.val j.unop) • (φ.map j.unop) m
      rw [map_smul]
      have hcompat :=
        φ.compatible i.unop j.unop (leOfHom f.unop)
      have hmap :
          (F.system.map f).hom.comp (φ.map i.unop) = φ.map j.unop := by
        rw [← hcompat]
        congr 1
      have hmap_apply :
          (F.system.map f).hom ((φ.map i.unop) m) = (φ.map j.unop) m := by
        exact DFunLike.congr_fun hmap m
      rw [hmap_apply]
      have ha := (a.property (leOfHom f.unop)).symm
      have hmem : a.val i.unop - a.val j.unop ∈
          (I ^ (j.unop : ℕ) : Ideal A) := by
        have hmem' : a.val i.unop - a.val j.unop ∈
            (I ^ (j.unop : ℕ)) • (⊤ : Submodule A A) :=
          (SModEq.sub_mem
            (U := (I ^ (j.unop : ℕ)) • (⊤ : Submodule A A))).mp ha
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hmem'
      have hzero := @hF j.unop ((φ.map j.unop) m)
        ⟨a.val i.unop - a.val j.unop,
          hmem⟩
      rw [← sub_eq_zero, ← sub_smul]
      simpa using hzero

/-- The map induced by a compatible graded system of maps after tensoring with `A'`. -/
noncomputable def inducedTensorLimitMap
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F) :
    M ⊗[A] ringCompletion I →ₗ[A] inverseLimitModule F.system := by
  let c : Cone F.system :=
    { pt := ModuleCat.of A (M ⊗[A] ringCompletion I)
      π :=
        { app := fun i =>
            ModuleCat.ofHom
              (completionTensorCoordinate I (i.unop : ℕ) (hF i.unop)
                (φ.map i.unop))
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            simpa using
              (completionTensorCoordinate_naturality G I F hF 𝓜 φ f).symm } }
  exact (limit.lift F.system c).hom

theorem inducedTensorLimitMap_projection
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    (n : ℕ+) :
    (limit.π F.system (Opposite.op n)).hom.comp
        (inducedTensorLimitMap G I F hF 𝓜 φ) =
      completionTensorCoordinate I (n : ℕ) (hF n) (φ.map n) := by
  change (limit.π F.system (Opposite.op n)).hom.comp
      (limit.lift F.system _).hom = _
  apply LinearMap.ext
  intro x
  change (limit.π F.system (Opposite.op n)).hom
      ((limit.lift F.system _).hom x) = _
  rw [← ConcreteCategory.comp_apply, limit.lift_π]
  rfl

/-- The Daniel--Litt lemma: an isomorphism after completion is detected degreewise. -/
theorem daniel_litt {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (hI : I ≤ irrelevantIdeal G) (hIhom : I.IsHomogeneous G.component)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    (hφ : Function.Bijective (inducedTensorLimitMap G I F hF 𝓜 φ)) :
    ∀ d : ℤ, ∃ e : (𝓜.component d) ≃+ gradedComponentLimit G F d,
      ∀ n : ℕ+, ∀ x : 𝓜.component d,
        (limit.π (gradedComponentSystem G F d) (Opposite.op n)).hom (e x) =
          componentAddHom G 𝓜 (F.grading n) (φ.map n) (φ.isGraded n) d x := by
  /-
  Proof roadmap (Stacks, Algebra, Lemma `daniel-litt`).

  `inducedTensorLimitMap_projection` controls the ungraded coordinates, but
  there is presently no grading on `ringCompletion I`, no inclusion from a
  component limit into `inverseLimitModule F.system`, and no theorem saying
  that completion preserves a fixed low degree.  Thus `hφ.injective` or
  `hφ.surjective` cannot be applied directly to the displayed component goal.
  Supply the following local bridges.

  1. For fixed `d`, form a cone on `gradedComponentSystem G F d` with point
     `AddCommGrpCat.of (𝓜.component d)` and legs
       `componentAddHom G 𝓜 (F.grading n) (φ.map n) (φ.isGraded n) d`.
     Here the cone and its limit must be instantiated in
     `AddCommGrpCat.{max u w}`, matching `M`, `F.system`, and the tensor source;
     do not let Lean infer a fresh smaller universe.
     Naturality is `φ.compatible` restricted to components.  Let
       `η d : 𝓜.component d →+ gradedComponentLimit G F d`
     be `(limit.lift _ cone).hom`; `limit.lift_π` gives exactly the coordinate
     equation required in the conclusion.  It remains to prove `η d`
     bijective and use `AddEquiv.ofBijective`.

  2. Prove the pure-tensor coordinate formula
       `completionTensorCoordinate I n (hF n) (φ.map n)
          (x ⊗ₜ[A] (1 : ringCompletion I)) = φ.map n x`.
     This unfolds `completionTensorCoordinate` and uses
     `AdicCompletion.evalₐ_of`/`map_one`.  Together with
     `inducedTensorLimitMap_projection` and `Concrete.limit_ext F.system`, it
     says that `η d x = 0` forces
       `inducedTensorLimitMap G I F hF 𝓜 φ (x ⊗ₜ 1) = 0`.

  3. Establish the low-degree completion lemma used in both directions.  From
     `hIhom`, obtain homogeneity of `I ^ n` inductively with
     `Ideal.IsHomogeneous.mul`; from `hI` and
     `HomogeneousIdeal.mem_irrelevant_iff`, prove that `I ^ n` has zero
     homogeneous components in degrees `< n`.  It follows that representatives
     of `AdicCompletion.evalₐ I n f'` have canonical, stage-independent
     components in degrees `< n`.  Package this as a truncation statement: for
     any finite bound `b` and `f' : ringCompletion I`, choose homogeneous
     `f_j ∈ G.component j` for `0 ≤ j ≤ b` and a tail `g'` such that
       `f' = (∑ j ≤ b, AdicCompletion.of I A f_j) + g'`,
     and every quotient representative of `g'` has zero components through
     degree `b`.  Use `AdicCompletion.evalₐ_mk`, `AdicCompletion.evalₐ_of`, and
     `AdicCompletion.ext_evalₐ` from
     `Mathlib/RingTheory/AdicCompletion/Algebra.lean`; no existing declaration
     currently combines these with `G` and `hIhom`.

  4. Injectivity of `η d`: after step 2 and `hφ.injective`, one has
     `x ⊗ₜ 1 = 0`.  Prove the finite-witness lemma for this tensor equality:
     there is a finitely generated graded submodule `M' ≤ M`, generated by
     finitely many homogeneous elements of degrees `d_i`, containing `x`, in
     which the same equality already holds in `M' ⊗[A] ringCompletion I`.
     Obtain it by expanding the finite tensor relation and decomposing its
     finitely many module entries with `DirectSum.sum_support_decompose` (the
     finite-sum API is `TensorProduct.exists_sum_tmul_eq` in
     `Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean`, if that focused
     import is added).  Choose `n > d - min_i d_i`; apply
     `id ⊗ AdicCompletion.evalₐ I n` and
     `TensorProduct.tensorQuotEquivQuotSMul M' (I ^ n)` from the focused module
     `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`, which identifies
     `M' ⊗[A] (A ⧸ I ^ n)` with `M' ⧸ I ^ n • ⊤`.  Step 3 says the degree-`d`
     part of the quotient map is injective, so `x = 0`.  The finite submodule is
     essential; attempting this directly in possibly unbounded-below `M` is a
     known dead end.

  5. For surjectivity, turn
     `y : gradedComponentLimit G F d` into an element of the full module limit:
     its coordinates are the subtype values of
     `(limit.π (gradedComponentSystem G F d) (op n)).hom y`.  Their
     compatibility defines an `inverseLimitFamilies F.system`; apply
     `(inverseLimitModule_equiv_families F.system).symm` from
     `Unit87/InverseSystems.lean`.  Use `hφ.surjective` to write this element as
     the image of `z : M ⊗[A] ringCompletion I`.  Express `z` as a finite sum
     `∑ i, x_i ⊗ₜ f'_i`, and decompose the finitely many `x_i` so they are
     homogeneous of degrees `d_i`.

  6. Apply the truncation lemma of step 3 to every `f'_i`, with bound at least
     `d - d_i`.  Terms of coefficient degree `< d - d_i` map to components
     below `d`; each tail maps to zero in every component of degree at most
     `d`; and terms above the bound cannot contribute to degree `d`.  Since the
     image of `z` is the pure degree-`d` family `y`, uniqueness of the stagewise
     graded decompositions leaves
       `x := ∑ i, f_{i, d-d_i} • x_i ∈ 𝓜.component d`
     with `η d x = y`.  This proves surjectivity, and
     `AddEquiv.ofBijective (η d) ⟨injective, surjective⟩` finishes while
     `limit.lift_π` supplies the requested coordinate identity.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit98
