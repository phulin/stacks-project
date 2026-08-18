import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.Order.JordanHolder
import Mathlib.Order.RelSeries

/-!
# Homological Algebra, Chapter 9: Jordan-Hölder

The source's notions of simple objects, Artinian objects, and Noetherian objects
are represented by Mathlib's `Simple`, `IsArtinianObject`, and
`IsNoetherianObject`.  The remaining interfaces below record the source's
finite filtrations and Jordan-Hölder statement for abelian categories.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit09

/-! ## Simple, Artinian, and Noetherian objects and categories -/

/- The source's definition of a simple object is Mathlib's `CategoryTheory.Simple`.
   In an abelian category, `CategoryTheory.simple_iff_subobject_isSimpleOrder`
   identifies it with the source formulation that the only subobjects are zero
   and the whole object; the nonzero clause is built into `Simple`. -/

/- Mathlib's `IsArtinianObject` and `IsNoetherianObject` are the source's
   descending and ascending chain conditions on subobjects. -/

/- Mathlib's `CategoryTheory.Artinian` and `CategoryTheory.Noetherian` also
   require essential smallness.  The source only says that every object has
   the corresponding chain condition, so these predicates retain exactly the
   source's hypothesis. -/

def IsArtinianCategory (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsArtinianObject X

def IsNoetherianCategory (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsNoetherianObject X

/-! ## Local bridges for short exact sequences and Jordan-Hölder lattices -/

/- The abelian subobject lattice is modular.  This is the categorical
   counterpart of the modular law behind the second (diamond) isomorphism;
   Mathlib's `JordanHolderLattice` instance is then available for
   `Subobject A`. -/
instance subobject_isModularLattice
    {C : Type u} [Category.{v} C] [Abelian C] (A : C) :
    IsModularLattice (Subobject A) := by
  have sup_epi {X Y : Subobject A} :
      Epi (biprod.desc (Subobject.ofLE X (X ⊔ Y) le_sup_left)
        (Subobject.ofLE Y (X ⊔ Y) le_sup_right)) := by
    let e := biprod.desc (Subobject.ofLE X (X ⊔ Y) le_sup_left)
      (Subobject.ofLE Y (X ⊔ Y) le_sup_right)
    let c := cokernel.π e
    have hX : X ≤ (Subobject.map (X ⊔ Y).arrow).obj
        (Subobject.mk (kernel.ι c)) := by
      have h0 : Subobject.ofLE X (X ⊔ Y) le_sup_left ≫ c = 0 := by
        rw [← biprod.inl_desc (Subobject.ofLE X (X ⊔ Y) le_sup_left)
          (Subobject.ofLE Y (X ⊔ Y) le_sup_right)]
        rw [Category.assoc, cokernel.condition]
        simp
      rw [Subobject.map_mk]
      apply Subobject.le_mk_of_comm (kernel.lift c
        (Subobject.ofLE X (X ⊔ Y) le_sup_left) h0)
      simp [c]
    have hY : Y ≤ (Subobject.map (X ⊔ Y).arrow).obj
        (Subobject.mk (kernel.ι c)) := by
      have h0 : Subobject.ofLE Y (X ⊔ Y) le_sup_right ≫ c = 0 := by
        rw [← biprod.inr_desc (Subobject.ofLE X (X ⊔ Y) le_sup_left)
          (Subobject.ofLE Y (X ⊔ Y) le_sup_right)]
        rw [Category.assoc, cokernel.condition]
        simp
      rw [Subobject.map_mk]
      apply Subobject.le_mk_of_comm (kernel.lift c
        (Subobject.ofLE Y (X ⊔ Y) le_sup_right) h0)
      simp [c]
    have hmap : (Subobject.map (X ⊔ Y).arrow).obj
          (Subobject.mk (kernel.ι c)) = X ⊔ Y := by
      apply le_antisymm
      · calc
          (Subobject.map (X ⊔ Y).arrow).obj (Subobject.mk (kernel.ι c)) ≤
              (Subobject.map (X ⊔ Y).arrow).obj
                (⊤ : Subobject (Subobject.underlying.obj (X ⊔ Y))) :=
            Functor.monotone (Subobject.map (X ⊔ Y).arrow) le_top
          _ = Subobject.mk (X ⊔ Y).arrow := Subobject.map_top _
          _ = X ⊔ Y := Subobject.mk_arrow _
      · exact sup_le hX hY
    have hK : Subobject.mk (kernel.ι c) =
        (⊤ : Subobject (Subobject.underlying.obj (X ⊔ Y))) := by
      apply (Subobject.map_obj_injective (X ⊔ Y).arrow)
      rw [hmap, Subobject.map_top, Subobject.mk_arrow]
    have hi : IsIso (kernel.ι c) := by
      apply (Subobject.isIso_iff_mk_eq_top _).mpr
      exact hK
    apply Abelian.epi_of_cokernel_π_eq_zero
    change c = 0
    rcases hi.out with ⟨i, hi₁, hi₂⟩
    calc
      c = 𝟙 _ ≫ c := by simp
      _ = (i ≫ kernel.ι c) ≫ c := by rw [hi₂]
      _ = i ≫ (kernel.ι c ≫ c) := by rw [Category.assoc]
      _ = 0 := by simp
  exact ⟨fun {x} y {z} h => by
    let u := x ⊔ y
    let w := u ⊓ z
    let v := x ⊔ (y ⊓ z)
    let e := biprod.desc (Subobject.ofLE x u le_sup_left)
      (Subobject.ofLE y u le_sup_right)
    let q := Subobject.ofLE w u inf_le_left
    have he : Epi e := by
      dsimp [e, u]
      exact sup_epi
    have hp : Epi (pullback.snd e q) := by
      exact Abelian.epi_snd_of_isLimit e q (limit.isLimit (cospan e q))
    let l := pullback.fst e q
    let p := pullback.snd e q
    have htotal : l ≫ biprod.desc x.arrow y.arrow =
        p ≫ w.arrow := by
      calc
        l ≫ biprod.desc x.arrow y.arrow = l ≫ e ≫ u.arrow := by
          simp [e, Subobject.ofLE_arrow, biprod.desc_eq]
        _ = (l ≫ e) ≫ u.arrow := by rw [Category.assoc]
        _ = (p ≫ q) ≫ u.arrow := by rw [pullback.condition]
        _ = p ≫ w.arrow := by simp [q, u, w]
    let lx := l ≫ biprod.fst
    let ly := l ≫ biprod.snd
    let ay := (p ≫ Subobject.ofLE w z inf_le_right) -
      (lx ≫ Subobject.ofLE x z h)
    have hay : ay ≫ z.arrow = ly ≫ y.arrow := by
      calc
        ay ≫ z.arrow =
            (p ≫ Subobject.ofLE w z inf_le_right) ≫ z.arrow -
              (lx ≫ Subobject.ofLE x z h) ≫ z.arrow := by
          simp [ay, Preadditive.sub_comp]
        _ = p ≫ w.arrow - lx ≫ x.arrow := by
          simp [Subobject.ofLE_arrow]
        _ = l ≫ biprod.desc x.arrow y.arrow - lx ≫ x.arrow := by rw [htotal]
        _ = ly ≫ y.arrow := by simp [lx, ly, biprod.desc_eq]
    let lyz := (Subobject.inf_isPullback y z).lift ly ay hay.symm
    have hlyz : lyz ≫ (y ⊓ z).arrow = ly ≫ y.arrow := by
      dsimp [lyz]
      rw [← Subobject.inf_comp_left y z, ← Category.assoc]
      exact congrArg (fun f => f ≫ y.arrow)
        ((Subobject.inf_isPullback y z).lift_fst ly ay hay.symm)
    let g := (lx ≫ Subobject.ofLE x v le_sup_left) +
      (lyz ≫ Subobject.ofLE (y ⊓ z) v le_sup_right)
    have hg : g ≫ v.arrow = p ≫ w.arrow := by
      calc
        g ≫ v.arrow = lx ≫ x.arrow + lyz ≫ (y ⊓ z).arrow := by
          simp [g, Subobject.ofLE_arrow, Preadditive.add_comp]
        _ = lx ≫ x.arrow + ly ≫ y.arrow := by
          rw [hlyz]
        _ = l ≫ biprod.desc x.arrow y.arrow := by
          simp [lx, ly, biprod.desc_eq]
        _ = p ≫ w.arrow := htotal
    let c := cokernel.π v.arrow
    have hzero : w.arrow ≫ c = 0 := by
      apply hp.left_cancellation
      calc
        p ≫ (w.arrow ≫ c) = (p ≫ w.arrow) ≫ c := by rw [← Category.assoc]
        _ = (g ≫ v.arrow) ≫ c := by rw [hg]
        _ = g ≫ (v.arrow ≫ c) := by rw [Category.assoc]
        _ = p ≫ 0 := by simp [c]
    exact Subobject.le_of_comm (Abelian.monoLift v.arrow w.arrow hzero)
      (Abelian.monoLift_comp v.arrow w.arrow hzero)
    ⟩

/- The two quotient-closure interfaces are kept separate from the
   short-exact equivalences below.  This lets their users reuse the
   categorical quotient argument without duplicating a chain-condition proof. -/
theorem isArtinianObject_of_shortExact_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₂ : IsArtinianObject S.X₂) :
    IsArtinianObject S.X₃ := by
  have hN : IsNoetherianObject (Opposite.op S.X₂) := by
    rw [isNoetherianObject_iff_not_strictMono]
    intro f hf
    let e := Abelian.subobjectIsoSubobjectOp S.X₂
    let g : ℕ → Subobject S.X₂ :=
      fun n => e.symm (show (Subobject (Opposite.op S.X₂))ᵒᵈ from f n)
    have hnot := (isArtinianObject_iff_not_strictAnti S.X₂).1 h₂
    apply hnot g
    intro a b hab
    apply (e.symm.lt_iff_lt).2
    change f a < f b
    exact hf hab
  let _ : IsNoetherianObject (Opposite.op S.X₂) := hN
  have hSop := hS.op
  let _ : Mono S.g.op := hSop.mono_f
  have hN3 : IsNoetherianObject (Opposite.op S.X₃) :=
    isNoetherianObject_of_mono S.g.op
  rw [isArtinianObject_iff_not_strictAnti]
  intro f hf
  let e := Abelian.subobjectIsoSubobjectOp S.X₃
  let g : ℕ → Subobject (Opposite.op S.X₃) := fun n => e (f n)
  have hnot :=
    (isNoetherianObject_iff_not_strictMono (Opposite.op S.X₃)).1 hN3
  apply hnot g
  intro a b hab
  apply (e.lt_iff_lt).2
  exact hf hab

theorem isNoetherianObject_of_shortExact_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₂ : IsNoetherianObject S.X₂) :
    IsNoetherianObject S.X₃ := by
  have hA : IsArtinianObject (Opposite.op S.X₂) := by
    rw [isArtinianObject_iff_not_strictAnti]
    intro f hf
    let e := Abelian.subobjectIsoSubobjectOp S.X₂
    let g : ℕ → Subobject S.X₂ :=
      fun n => e.symm (show (Subobject (Opposite.op S.X₂))ᵒᵈ from f n)
    have hnot := (isNoetherianObject_iff_not_strictMono S.X₂).1 h₂
    apply hnot g
    intro a b hab
    apply (e.symm.lt_iff_lt).2
    change f b < f a
    exact hf hab
  let _ : IsArtinianObject (Opposite.op S.X₂) := hA
  have hSop := hS.op
  let _ : Mono S.g.op := hSop.mono_f
  have hA3 : IsArtinianObject (Opposite.op S.X₃) :=
    isArtinianObject_of_mono S.g.op
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  let e := Abelian.subobjectIsoSubobjectOp S.X₃
  let g : ℕ → Subobject (Opposite.op S.X₃) := fun n => e (f n)
  have hnot :=
    (isArtinianObject_iff_not_strictAnti (Opposite.op S.X₃)).1 hA3
  apply hnot g
  intro a b hab
  change (e (f a) : (Subobject (Opposite.op S.X₃))ᵒᵈ) < e (f b)
  apply (e.lt_iff_lt).mpr
  exact hf hab

/- These are the checked subobject halves of the same two interfaces.  In
   particular, retain `hS.mono_f` as the explicit monomorphism argument to
   Mathlib's subobject chain-condition lemmas. -/
theorem isArtinianObject_of_shortExact_subobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₂ : IsArtinianObject S.X₂) :
    IsArtinianObject S.X₁ := by
  letI : IsArtinianObject S.X₂ := h₂
  letI : Mono S.f := hS.mono_f
  exact isArtinianObject_of_mono S.f

theorem isNoetherianObject_of_shortExact_subobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₂ : IsNoetherianObject S.X₂) :
    IsNoetherianObject S.X₁ := by
  letI : IsNoetherianObject S.X₂ := h₂
  letI : Mono S.f := hS.mono_f
  exact isNoetherianObject_of_mono S.f

/-! ## Stability under short exact sequences -/

theorem isArtinianObject_iff_of_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔
      IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  sorry

theorem isNoetherianObject_iff_of_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔
      IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  sorry

/-! ## Finite-length filtrations -/

noncomputable def subobjectQuotient
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    (P Q : Subobject A) (h : P ≤ Q) : C :=
  cokernel (Subobject.ofLE P Q h)

/- A simple categorical quotient is exactly a cover in the subobject
   lattice.  This is the relation conversion required by
   `CompositionSeries`. -/
theorem simple_subobjectQuotient_iff_covBy
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    {P Q : Subobject A} (hPQ : P ≤ Q) :
    Simple (subobjectQuotient P Q hPQ) ↔ P ⋖ Q := by
  have hsq {R : Subobject A} (hPR : P ≤ R) (hRQ : R ≤ Q) :
      IsPullback (Subobject.ofLE P R hPR) (𝟙 (P : C))
        (Subobject.ofLE R Q hRQ) (Subobject.ofLE P Q (hPR.trans hRQ)) := by
    apply IsPullback.mk'
    · simp [Subobject.ofLE_comp_ofLE]
    · intro W a b hab hab'
      exact (cancel_mono (Subobject.ofLE P R hPR)).1 hab
    · intro W a b hab
      refine ⟨b, ?_, by simp⟩
      apply (cancel_mono (Subobject.ofLE R Q hRQ)).1
      simpa [Subobject.ofLE_comp_ofLE] using hab.symm
  have hSR {R : Subobject A} (hPR : P ≤ R) :
      (ShortComplex.mk (Subobject.ofLE P R hPR)
        (cokernel.π (Subobject.ofLE P R hPR))).ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (Subobject.ofLE P R hPR))
    · infer_instance
    · change Epi (coequalizer.π (Subobject.ofLE P R hPR) 0)
      exact inferInstanceAs (Epi (coequalizer.π (Subobject.ofLE P R hPR) 0))
  have hmap_mono {R : Subobject A} (hPR : P ≤ R) (hRQ : R ≤ Q) :
      Mono (cokernel.map (Subobject.ofLE P R hPR)
        (Subobject.ofLE P Q (hPR.trans hRQ)) (𝟙 (P : C))
        (Subobject.ofLE R Q hRQ) (by simp [Subobject.ofLE_comp_ofLE])) := by
    exact Abelian.mono_cokernel_map_of_isPullback (hsq hPR hRQ)
  have heq_of_iso_ofLE {X Y : Subobject A} (hXY : X ≤ Y)
      (hiso : IsIso (Subobject.ofLE X Y hXY)) : X = Y := by
    rcases hiso.out with ⟨i, hi, ih⟩
    apply le_antisymm hXY
    apply Subobject.le_of_comm i
    rw [← Subobject.ofLE_arrow hXY, ← Category.assoc, ih, Category.id_comp]
  have hp (T : Subobject (subobjectQuotient P Q hPQ)) :
      Subobject.mk (Subobject.ofLE P Q hPQ) ≤
        (Subobject.pullback (cokernel.π (Subobject.ofLE P Q hPQ))).obj T := by
    apply Subobject.le_of_comm
      ((Subobject.underlyingIso (Subobject.ofLE P Q hPQ)).hom ≫
        (Subobject.isPullback (cokernel.π (Subobject.ofLE P Q hPQ)) T).lift 0
          (Subobject.ofLE P Q hPQ) (by simp))
    simp
  have hp_epi (T : Subobject (subobjectQuotient P Q hPQ)) :
      Epi (Subobject.pullbackπ (cokernel.π (Subobject.ofLE P Q hPQ)) T) := by
    have hπ : Epi (cokernel.π (Subobject.ofLE P Q hPQ)) := by
      change Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0)
      exact inferInstanceAs (Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0))
    exact @Abelian.epi_fst_of_isLimit C _ _ _ _ _ _ (T.arrow)
      (cokernel.π (Subobject.ofLE P Q hPQ)) hπ
      (Subobject.isPullback (cokernel.π (Subobject.ofLE P Q hPQ)) T).cone
      (Subobject.isPullback (cokernel.π (Subobject.ofLE P Q hPQ)) T).isLimit
  constructor
  · intro hs
    rw [covBy_iff_lt_and_eq_or_eq]
    have hne : P ≠ Q := by
      intro h
      subst Q
      have hfi : IsIso (Subobject.ofLE P P hPQ) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      have hz : IsZero (subobjectQuotient P P hPQ) :=
        (ShortComplex.ShortExact.isIso_f_iff (hSR hPQ)).mp hfi
      exact (@Simple.not_isZero _ _ _ _ hs) hz
    refine ⟨lt_of_le_of_ne hPQ hne, ?_⟩
    intro R hPR hRQ
    let φ :
        (ShortComplex.mk (Subobject.ofLE P R hPR)
          (cokernel.π (Subobject.ofLE P R hPR))) ⟶
        (ShortComplex.mk (Subobject.ofLE P Q (hPR.trans hRQ))
          (cokernel.π (Subobject.ofLE P Q (hPR.trans hRQ)))) :=
      ShortComplex.homMk (𝟙 (P : C)) (Subobject.ofLE R Q hRQ)
        (cokernel.map (Subobject.ofLE P R hPR)
          (Subobject.ofLE P Q (hPR.trans hRQ)) (𝟙 (P : C))
          (Subobject.ofLE R Q hRQ) (by simp [Subobject.ofLE_comp_ofLE]))
        (by simp [Subobject.ofLE_comp_ofLE]) (by simp [cokernel.map])
    by_cases hz : φ.τ₃ = 0
    · have hzero : IsZero (subobjectQuotient P R hPR) :=
        @IsZero.of_mono_eq_zero _ _ _ _ _ φ.τ₃ (hmap_mono hPR hRQ) hz
      have hfi : IsIso (Subobject.ofLE P R hPR) :=
        (ShortComplex.ShortExact.isIso_f_iff (hSR hPR)).mpr hzero
      exact Or.inl (heq_of_iso_ofLE (X := P) (Y := R) hPR hfi).symm
    · have hτ1 : IsIso φ.τ₁ := by
        dsimp [φ]
        change IsIso (𝟙 (P : C))
        infer_instance
      have hτ3 : IsIso φ.τ₃ :=
        @isIso_of_mono_of_nonzero _ _ _ _ _ hs φ.τ₃ (hmap_mono hPR hRQ) hz
      have hm := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ (hSR hPR)
        (hSR (hPR.trans hRQ)) hτ1 hτ3
      exact Or.inr (heq_of_iso_ofLE (X := R) (Y := Q) hRQ hm)
  · intro hcov
    apply (simple_iff_subobject_isSimpleOrder _).mpr
    have hnotzero : ¬IsZero (subobjectQuotient P Q hPQ) := by
      intro hz
      have hfi : IsIso (Subobject.ofLE P Q hPQ) :=
        (ShortComplex.ShortExact.isIso_f_iff (hSR hPQ)).mpr hz
      exact hcov.ne (heq_of_iso_ofLE (X := P) (Y := Q) hPQ hfi)
    refine { eq_bot_or_eq_top := ?_, exists_pair_ne := ?_ }
    · exact (Subobject.nontrivial_of_not_isZero hnotzero).exists_pair_ne
    · intro T
      change Subobject (cokernel (Subobject.ofLE P Q hPQ)) at T
      change T = (⊥ : Subobject (cokernel (Subobject.ofLE P Q hPQ))) ∨
        T = (⊤ : Subobject (cokernel (Subobject.ofLE P Q hPQ)))
      let R := (Subobject.pullback (cokernel.π (Subobject.ofLE P Q hPQ))).obj T
      let S := (Subobject.map Q.arrow).obj R
      have hmapP :
          (Subobject.map Q.arrow).obj
              (Subobject.mk (Subobject.ofLE P Q hPQ)) = P := by
        rw [Subobject.map_mk]
        apply Subobject.mk_eq_of_comm (Subobject.ofLE P Q hPQ ≫ Q.arrow)
          (Iso.refl _)
        simp
      have hmapTop :
          (Subobject.map Q.arrow).obj (⊤ : Subobject (Q : C)) = Q := by
        rw [Subobject.map_top, Subobject.mk_arrow]
      have hPS : P ≤ S := by
        rw [← hmapP]
        exact Functor.monotone (Subobject.map Q.arrow) (hp T)
      have hSQ : S ≤ Q := by
        calc
          S ≤ (Subobject.map Q.arrow).obj ⊤ :=
            Functor.monotone (Subobject.map Q.arrow) le_top
          _ = Q := hmapTop
      rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 S hPS hSQ with hSP | hSQ
      · have hR : R = Subobject.mk (Subobject.ofLE P Q hPQ) := by
          apply Subobject.map_obj_injective Q.arrow
          dsimp [S] at hSP
          rw [hSP, hmapP]
        have hzero :
            Subobject.pullbackπ (cokernel.π (Subobject.ofLE P Q hPQ)) T ≫ T.arrow = 0 := by
          rw [(Subobject.isPullback
            (cokernel.π (Subobject.ofLE P Q hPQ)) T).w]
          change R.arrow ≫ cokernel.π (Subobject.ofLE P Q hPQ) = 0
          rw [hR]
          apply (cancel_epi
            (Subobject.underlyingIso (Subobject.ofLE P Q hPQ)).inv).1
          rw [← Category.assoc, Subobject.underlyingIso_arrow,
            cokernel.condition]
          simp
        have hTzero : T.arrow = 0 := by
          apply (hp_epi T).left_cancellation
          simpa only [comp_zero] using hzero
        have hbot :
            Subobject.mk T.arrow =
              (⊥ : Subobject (cokernel (Subobject.ofLE P Q hPQ))) :=
          Subobject.mk_eq_bot_iff_zero.mpr hTzero
        exact Or.inl (by simpa only [Subobject.mk_arrow] using hbot)
      · have hR : R = (⊤ : Subobject (Q : C)) := by
          apply Subobject.map_obj_injective Q.arrow
          dsimp [S] at hSQ
          rw [hSQ, hmapTop]
        have hπ : Epi (cokernel.π (Subobject.ofLE P Q hPQ)) := by
          change Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0)
          exact inferInstanceAs (Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0))
        have hcomp : Epi
            (Subobject.pullbackπ (cokernel.π (Subobject.ofLE P Q hPQ)) T ≫ T.arrow) := by
          rw [(Subobject.isPullback
            (cokernel.π (Subobject.ofLE P Q hPQ)) T).w]
          change Epi (R.arrow ≫ cokernel.π (Subobject.ofLE P Q hPQ))
          rw [hR]
          constructor
          intro Z f g h
          apply hπ.left_cancellation
          apply (cancel_epi (⊤ : Subobject (Q : C)).arrow).1
          simpa only [Category.assoc] using h
        have hEpiT : Epi T.arrow := by
          constructor
          intro Z f g h
          apply hcomp.left_cancellation
          simp only [Category.assoc]
          rw [h]
        exact Or.inr (by simpa only [Subobject.mk_arrow] using
          (Subobject.epi_iff_mk_eq_top T.arrow).mp hEpiT
          )

/- The diamond relation generated by Mathlib's `JordanHolderLattice` is
   interpreted as an isomorphism of the corresponding categorical
   subobject quotients. -/
theorem jordanHolderLattice_iso_subobjectQuotient
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    {P Q R T : Subobject A} (hPQ : P ≤ Q) (hRT : R ≤ T)
    (h : JordanHolderLattice.Iso (P, Q) (R, T)) :
    Nonempty (subobjectQuotient P Q hPQ ≅ subobjectQuotient R T hRT) := by
  let e : (Subobject A × Subobject A) → (Subobject A × Subobject A) → Prop :=
    fun x y =>
      (¬x.1 ≤ x.2 ∧ ¬y.1 ≤ y.2) ∨
        (∃ hx : x.1 ≤ x.2, ∃ hy : y.1 ≤ y.2,
          Nonempty (subobjectQuotient x.1 x.2 hx ≅ subobjectQuotient y.1 y.2 hy))
  have he : e (P, Q) (R, T) := by
    apply JordanHolderLattice.Iso.rel e
    · intro x
      rcases x with ⟨x₁, x₂⟩
      by_cases hx : x₁ ≤ x₂
      · exact Or.inr ⟨hx, hx, ⟨Iso.refl _⟩⟩
      · exact Or.inl ⟨hx, hx⟩
    · intro x y hxy
      rcases hxy with ⟨hxy, hyx⟩ | ⟨hx, hy, ⟨i⟩⟩
      · exact Or.inl ⟨hyx, hxy⟩
      · exact Or.inr ⟨hy, hx, ⟨i.symm⟩⟩
    · intro x y z hxy hyz
      rcases hxy with ⟨hxy, hyx⟩ | ⟨hx, hy, ⟨i⟩⟩
      · rcases hyz with ⟨hyz, hzy⟩ | ⟨hy, hz, _⟩
        · exact Or.inl ⟨hxy, hzy⟩
        · exact False.elim (hyx hy)
      · rcases hyz with ⟨hyz, hzy⟩ | ⟨_, hz, ⟨j⟩⟩
        · exact False.elim (hyz hy)
        · exact Or.inr ⟨hx, hz, ⟨i ≪≫ j⟩⟩
    · intro x y hm
      change x ⋖ x ⊔ y at hm
      have hiy : x ⊓ y ⋖ y := inf_covBy_of_covBy_sup_left hm
      have hsq :
          IsPullback (Subobject.ofLE (x ⊓ y) y inf_le_right)
            (Subobject.ofLE (x ⊓ y) x inf_le_left)
            (Subobject.ofLE y (x ⊔ y) le_sup_right)
            (Subobject.ofLE x (x ⊔ y) le_sup_left) := by
        apply IsPullback.mk'
        · simp [Subobject.ofLE_comp_ofLE]
        · intro W a b hab hab'
          exact (Subobject.inf_isPullback x y).flip.hom_ext
            (by simpa using hab) (by simpa using hab')
        · intro W a b hab
          have hab' : a ≫ y.arrow = b ≫ x.arrow := by
            simpa only [Category.assoc, Subobject.ofLE_arrow] using
              congrArg (fun k => k ≫ (x ⊔ y).arrow) hab
          rcases (Subobject.inf_isPullback x y).flip.exists_lift a b hab' with
            ⟨l, hl₁, hl₂⟩
          exact ⟨l, by simpa using hl₁, by simpa using hl₂⟩
      let φ := cokernel.map
        (Subobject.ofLE (x ⊓ y) y inf_le_right)
        (Subobject.ofLE x (x ⊔ y) le_sup_left)
        (Subobject.ofLE (x ⊓ y) x inf_le_left)
        (Subobject.ofLE y (x ⊔ y) le_sup_right)
        (by simp [Subobject.ofLE_comp_ofLE])
      have hφmono : Mono φ := by
        dsimp [φ]
        exact Abelian.mono_cokernel_map_of_isPullback hsq
      letI : Simple (cokernel (Subobject.ofLE x (x ⊔ y) le_sup_left)) := by
        change Simple (subobjectQuotient x (x ⊔ y) le_sup_left)
        exact (simple_subobjectQuotient_iff_covBy le_sup_left).mpr hm
      letI : Simple (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)) := by
        change Simple (subobjectQuotient (x ⊓ y) y inf_le_right)
        exact (simple_subobjectQuotient_iff_covBy inf_le_right).mpr hiy
      have hφne : φ ≠ 0 := by
        intro hφzero
        have hsourcezero : IsZero (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)) :=
          @IsZero.of_mono_eq_zero _ _ _ _ _ φ hφmono hφzero
        exact (Simple.not_isZero (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)))
          hsourcezero
      letI : IsIso φ := isIso_of_mono_of_nonzero hφne
      exact Or.inr ⟨le_sup_left, inf_le_right, ⟨(asIso φ).symm⟩⟩
    exact h
  rcases he with hbad | ⟨_, _, ⟨i⟩⟩
  · exact False.elim (hbad.1 hPQ)
  · simpa only [Prod.fst, Prod.snd] using (Nonempty.intro i)

structure FiniteLengthFiltration
    {C : Type u} [Category.{v} C] [Abelian C] (A : C) where
  series : RelSeries {(P, Q) : (Subobject A) × (Subobject A) | P < Q}
  head_eq_bot : series.head = ⊥
  last_eq_top : series.last = ⊤
  simple_factor :
    ∀ i : Fin series.length,
      Simple (subobjectQuotient (series (Fin.castSucc i)) (series i.succ)
        (le_of_lt (by simpa using series.step i)))

namespace FiniteLengthFiltration

variable {C : Type u} [Category.{v} C] [Abelian C] {A : C}

noncomputable def factor (F : FiniteLengthFiltration A) (i : Fin F.series.length) : C :=
  subobjectQuotient (F.series (Fin.castSucc i)) (F.series i.succ)
    (le_of_lt (by simpa using F.series.step i))

/- Reinterpret a finite-length filtration as the composition series whose
   adjacent relation is `CovBy`; the relation is supplied by the preceding
   simple-quotient bridge. -/
noncomputable def toCompositionSeries (F : FiniteLengthFiltration A) :
    CompositionSeries (Subobject A) where
  length := F.series.length
  toFun := F.series
  step := fun i =>
    (simple_subobjectQuotient_iff_covBy
      (le_of_lt (by simpa using F.series.step i))).mp (F.simple_factor i)

end FiniteLengthFiltration

theorem finite_length_iff
    {C : Type u} [Category.{v} C] [Abelian C] (A : C) :
    IsArtinianObject A ∧ IsNoetherianObject A ↔
      Nonempty (FiniteLengthFiltration A) := by
  sorry

/-! ## Jordan-Hölder uniqueness -/

theorem jordan_holder
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    (_hA : IsArtinianObject A ∧ IsNoetherianObject A)
    (F G : FiniteLengthFiltration A) :
    F.series.length = G.series.length ∧
      ∃ σ : Fin F.series.length ≃ Fin G.series.length,
        ∀ i, Nonempty (F.factor i ≅ G.factor (σ i)) := by
  sorry

end Formalization.Books.Homology.Unit09
