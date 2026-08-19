import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Category.GaloisConnection
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
  let : IsArtinianObject S.X₂ := h₂
  let : Mono S.f := hS.mono_f
  exact isArtinianObject_of_mono S.f

theorem isNoetherianObject_of_shortExact_subobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₂ : IsNoetherianObject S.X₂) :
    IsNoetherianObject S.X₁ := by
  let : IsNoetherianObject S.X₂ := h₂
  let : Mono S.f := hS.mono_f
  exact isNoetherianObject_of_mono S.f

/-! ## Stability under short exact sequences -/

theorem isArtinianObject_iff_of_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔
      IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  constructor
  · intro h₂
    exact ⟨isArtinianObject_of_shortExact_subobject S hS h₂,
      isArtinianObject_of_shortExact_quotient S hS h₂⟩
  · rintro ⟨h₁, h₃⟩
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let : Mono S.g.op := by infer_instance
    let : IsArtinianObject S.X₁ := h₁
    let : IsArtinianObject S.X₃ := h₃
    let K : Subobject S.X₂ := Subobject.mk S.f
    let f₁ : Subobject (K : C) → Subobject S.X₂ := (Subobject.map K.arrow).obj
    let f₂ : Subobject S.X₂ → Subobject (K : C) := (Subobject.pullback K.arrow).obj
    let eK : Subobject (K : C) ≃o Subobject S.X₁ :=
      Subobject.mapIsoToOrderIso (Subobject.underlyingIso S.f)
    let : WellFoundedLT (Subobject (K : C)) :=
      eK.toOrderEmbedding.wellFoundedLT
    let e₂ := Abelian.subobjectIsoSubobjectOp S.X₂
    let e₃ := Abelian.subobjectIsoSubobjectOp S.X₃
    let g₁ : Subobject S.X₃ → Subobject S.X₂ :=
      fun x => e₂.symm (OrderDual.toDual
        ((Subobject.map S.g.op).obj (OrderDual.ofDual (e₃ x))))
    let g₂ : Subobject S.X₂ → Subobject S.X₃ :=
      fun x => e₃.symm (OrderDual.toDual
        ((Subobject.pullback S.g.op).obj (OrderDual.ofDual (e₂ x))))
    have hgconn : GaloisConnection g₂ g₁ := by
      intro a b
      dsimp [g₁, g₂]
      conv_lhs => rw [← e₃.symm_apply_apply b]
      conv_rhs => rw [← e₂.symm_apply_apply a]
      rw [e₃.symm.le_iff_le, e₂.symm.le_iff_le]
      exact ((Subobject.mapPullbackAdj S.g.op).gc
        (show Subobject (Opposite.op S.X₃) from e₃ b)
        (show Subobject (Opposite.op S.X₂) from e₂ a)).symm
    have gi : GaloisInsertion g₂ g₁ := by
      apply hgconn.toGaloisInsertion
      intro x
      apply le_of_eq
      symm
      apply e₃.injective
      dsimp [g₁, g₂]
      simp [Subobject.pullback_map_self]
    have gci : GaloisCoinsertion f₁ f₂ :=
      { choice := fun x _ => f₂ x
        gc := (Subobject.mapPullbackAdj K.arrow).gc
        u_l_le := fun x => by
          exact le_of_eq (by simp [f₁, f₂])
        choice_eq := fun _ _ => rfl }
    have hfg : ∀ a, f₁ (f₂ a) = a ⊓ K := by
      intro a
      dsimp [f₁, f₂, K]
      rw [inf_comm]
      exact (Subobject.inf_eq_map_pullback K a).symm
    have hgg : ∀ a, g₁ (g₂ a) = a ⊔ K := by
      have hK : e₂ K = OrderDual.toDual (Subobject.mk S.g.op) := by
        change (cokernelOrderHom S.X₂) (Subobject.mk S.f) =
          OrderDual.toDual (Subobject.mk S.g.op)
        change OrderDual.toDual (Subobject.mk (cokernel.π S.f).op) =
          OrderDual.toDual (Subobject.mk S.g.op)
        change Subobject.mk (cokernel.π S.f).op = Subobject.mk S.g.op
        let i : cokernel S.f ≅ S.X₃ :=
          IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f)
            hS.gIsCokernel
        symm
        apply Subobject.mk_eq_mk_of_comm S.g.op (cokernel.π S.f).op i.op
        have hi : cokernel.π S.f ≫ i.hom = S.g := by
          simpa using (IsColimit.comp_coconePointUniqueUpToIso_hom
            (cokernelIsCokernel S.f) hS.gIsCokernel (.one))
        simpa [Iso.op_hom] using congrArg Quiver.Hom.op hi
      have hmap : ∀ q : Subobject (Opposite.op S.X₂),
          (Subobject.map S.g.op).obj ((Subobject.pullback S.g.op).obj q) =
            (Subobject.mk S.g.op) ⊓ q := by
        intro q
        change (Subobject.map S.g.op).obj ((Subobject.pullback S.g.op).obj q) =
          (Subobject.inf.obj (Quotient.mk'' (MonoOver.mk S.g.op))).obj q
        exact (Subobject.inf_eq_map_pullback' (MonoOver.mk S.g.op) q).symm
      intro a
      apply e₂.injective
      dsimp [g₁, g₂]
      simp [e₃.apply_symm_apply, e₂.apply_symm_apply]
      rw [hmap]
      rw [hK]
      change (OrderDual.toDual (Subobject.mk S.g.op) ⊔ e₂ a) =
        e₂ a ⊔ OrderDual.toDual (Subobject.mk S.g.op)
      exact sup_comm _ _
    apply (isArtinianObject_iff_not_strictAnti S.X₂).2
    let : WellFoundedLT (Subobject S.X₂) :=
      wellFounded_lt_exact_sequence K f₁ f₂ g₁ g₂ gci gi hfg hgg
    exact fun chain => not_strictAnti_of_wellFoundedLT chain

theorem isNoetherianObject_iff_of_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔
      IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := by
  constructor
  · intro h₂
    exact ⟨isNoetherianObject_of_shortExact_subobject S hS h₂,
      isNoetherianObject_of_shortExact_quotient S hS h₂⟩
  · rintro ⟨h₁, h₃⟩
    have hA1 : IsArtinianObject (Opposite.op S.X₁) := by
      rw [isArtinianObject_iff_not_strictAnti]
      intro f hf
      let e := Abelian.subobjectIsoSubobjectOp S.X₁
      let g : ℕ → Subobject S.X₁ := fun n =>
        e.symm (show (Subobject (Opposite.op S.X₁))ᵒᵈ from f n)
      have hnot := (isNoetherianObject_iff_not_strictMono S.X₁).1 h₁
      apply hnot g
      intro a b hab
      apply (e.symm.lt_iff_lt).2
      change f b < f a
      exact hf hab
    have hA3 : IsArtinianObject (Opposite.op S.X₃) := by
      rw [isArtinianObject_iff_not_strictAnti]
      intro f hf
      let e := Abelian.subobjectIsoSubobjectOp S.X₃
      let g : ℕ → Subobject S.X₃ := fun n =>
        e.symm (show (Subobject (Opposite.op S.X₃))ᵒᵈ from f n)
      have hnot := (isNoetherianObject_iff_not_strictMono S.X₃).1 h₃
      apply hnot g
      intro a b hab
      apply (e.symm.lt_iff_lt).2
      change f b < f a
      exact hf hab
    have hA2 : IsArtinianObject (Opposite.op S.X₂) :=
      (isArtinianObject_iff_of_shortExact S.op hS.op).2 ⟨hA3, hA1⟩
    rw [isNoetherianObject_iff_not_strictMono]
    intro f hf
    let e := Abelian.subobjectIsoSubobjectOp S.X₂
    let g : ℕ → Subobject (Opposite.op S.X₂) := fun n => e (f n)
    have hnot :=
      (isArtinianObject_iff_not_strictAnti (Opposite.op S.X₂)).1 hA2
    apply hnot g
    intro a b hab
    change (e (f a) : (Subobject (Opposite.op S.X₂))ᵒᵈ) < e (f b)
    apply (e.lt_iff_lt).mpr
    exact hf hab

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
      let : Simple (cokernel (Subobject.ofLE x (x ⊔ y) le_sup_left)) := by
        change Simple (subobjectQuotient x (x ⊔ y) le_sup_left)
        exact (simple_subobjectQuotient_iff_covBy le_sup_left).mpr hm
      let : Simple (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)) := by
        change Simple (subobjectQuotient (x ⊓ y) y inf_le_right)
        exact (simple_subobjectQuotient_iff_covBy inf_le_right).mpr hiy
      have hφne : φ ≠ 0 := by
        intro hφzero
        have hsourcezero : IsZero (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)) :=
          @IsZero.of_mono_eq_zero _ _ _ _ _ φ hφmono hφzero
        exact (Simple.not_isZero (cokernel (Subobject.ofLE (x ⊓ y) y inf_le_right)))
          hsourcezero
      let : IsIso φ := isIso_of_mono_of_nonzero hφne
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
  constructor
  · rintro ⟨hA, hN⟩
    let : IsArtinianObject A := hA
    let : IsNoetherianObject A := hN
    let : WellFoundedLT (Subobject A) := inferInstance
    let : WellFoundedGT (Subobject A) := inferInstance
    obtain ⟨a, ha, n, hn, hstep⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
        (α := Subobject A) (x := (⊥ : Subobject A)) (y := (⊤ : Subobject A)) bot_le
    let series : RelSeries {(P, Q) : (Subobject A) × (Subobject A) | P < Q} :=
      { length := n
        toFun := fun i => a i
        step := fun i => by
          simpa using (hstep i i.isLt).1 }
    have hcov (i : Fin series.length) :
        series (Fin.castSucc i) ⋖ series i.succ := by
      dsimp [series]
      simpa using hstep i i.isLt
    refine ⟨⟨series, ?_, ?_, ?_⟩⟩
    · simp [series, RelSeries.head, ha]
    · simp [series, RelSeries.last, hn]
    · intro i
      exact (simple_subobjectQuotient_iff_covBy
        (le_of_lt (by simpa using series.step i))).mpr (hcov i)
  · rintro ⟨F⟩
    have hchain : ∀ {B : C}, FiniteLengthFiltration B →
        IsArtinianObject B ∧ IsNoetherianObject B := by
      intro B F
      induction hlen : F.series.length using Nat.strong_induction_on generalizing B F with
      | h n ih =>
        by_cases hn : n = 0
        · have hbot_top : (⊥ : Subobject B) = ⊤ := by
            rw [← F.head_eq_bot, ← F.last_eq_top]
            have hi : (0 : Fin (F.series.length + 1)) = Fin.last F.series.length := by
              apply Fin.ext
              simp [hlen, hn]
            exact congrArg F.series hi
          have hsub : Subsingleton (Subobject B) := by
            constructor
            intro P Q
            apply le_antisymm
            · calc
                P ≤ (⊤ : Subobject B) := le_top
                _ = ⊥ := hbot_top.symm
                _ ≤ Q := bot_le
            · calc
                Q ≤ (⊤ : Subobject B) := le_top
                _ = ⊥ := hbot_top.symm
                _ ≤ P := bot_le
          refine ⟨?_, ?_⟩
          · rw [isArtinianObject_iff_not_strictAnti]
            intro f hanti
            have hlt : f 1 < f 0 := hanti (Nat.zero_lt_succ 0)
            have heq : f 1 = f 0 := hsub.elim _ _
            exact (ne_of_lt hlt) heq
          · rw [isNoetherianObject_iff_not_strictMono]
            intro f hmono
            have hlt : f 0 < f 1 := hmono (Nat.zero_lt_succ 0)
            have heq : f 0 = f 1 := hsub.elim _ _
            exact (ne_of_lt hlt) heq
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          let S := F.toCompositionSeries
          let P : Subobject B := S.eraseLast.last
          let eP := Subobject.subobjectOrderIso P
          have hle (i : Fin (S.eraseLast.length + 1)) : S.eraseLast i ≤ P := by
            exact (CompositionSeries.strictMono S.eraseLast).monotone (Fin.le_last i)
          have hcov_subtype {x y : Subobject B} (hx : x ≤ P) (hy : y ≤ P)
              (hxy : x ⋖ y) :
              (⟨x, hx⟩ : Set.Iic P) ⋖ ⟨y, hy⟩ := by
            apply covBy_iff_lt_and_eq_or_eq.mpr
            refine ⟨hxy.1, ?_⟩
            intro z hz₁ hz₂
            have hz₁' : x ≤ z.1 := hz₁
            have hz₂' : z.1 ≤ y := hz₂
            rcases hxy.eq_or_eq hz₁' hz₂' with h | h
            · exact Or.inl (Subtype.ext h)
            · exact Or.inr (Subtype.ext h)
          let prevComp : CompositionSeries (Subobject (P : C)) :=
            { length := S.eraseLast.length
              toFun := fun i => eP.symm ⟨S.eraseLast i, hle i⟩
              step := fun i => by
                change _ ⋖ _
                apply (apply_covBy_apply_iff eP.symm).2
                exact hcov_subtype (hle _) (hle _) (S.eraseLast.step i) }
          let prevSeries : RelSeries
              {(U, V) : (Subobject (P : C)) × (Subobject (P : C)) | U < V} :=
            { length := prevComp.length
              toFun := prevComp
              step := fun i => (prevComp.step i).lt }
          have hprev_head : prevSeries.head = ⊥ := by
            apply eP.injective
            simp only [prevSeries, prevComp, RelSeries.head, eP.apply_symm_apply, eP.map_bot]
            apply Subtype.ext
            change (S.eraseLast).head = (⊥ : Subobject B)
            rw [RelSeries.head_eraseLast]
            change F.series.head = (⊥ : Subobject B)
            exact F.head_eq_bot
          have hprev_last : prevSeries.last = ⊤ := by
            apply eP.injective
            simp only [prevSeries, prevComp, RelSeries.last, eP.apply_symm_apply, eP.map_top]
            rfl
          let prevF : FiniteLengthFiltration (P : C) :=
            { series := prevSeries
              head_eq_bot := hprev_head
              last_eq_top := hprev_last
              simple_factor := fun i =>
                (simple_subobjectQuotient_iff_covBy
                  (le_of_lt (by simpa using prevSeries.step i))).mpr
                  (prevComp.step i) }
          have hprev_len : prevF.series.length < n := by
            have hSlen : S.length = n := by
              change F.series.length = n
              exact hlen
            simp [prevF, prevSeries, prevComp, hSlen]
            exact Nat.pred_lt (by simpa using Nat.ne_of_gt hnpos)
          obtain ⟨hPArt, hPNoeth⟩ := ih _ hprev_len prevF rfl
          have hPtop : IsCoatom P := by
            have hSlen : S.length = n := by
              change F.series.length = n
              exact hlen
            have hS0 : S.length ≠ 0 := by simpa [hSlen] using hn
            have hrel := S.eraseLast_last_rel_last hS0
            change P ⋖ S.last at hrel
            have hSl : S.last = (⊤ : Subobject B) := by
              change F.series.last = (⊤ : Subobject B)
              exact F.last_eq_top
            rw [hSl] at hrel
            have hrel' : P ⋖ (⊤ : Subobject B) := by
              exact hrel
            exact hrel'.isCoatom
          let Q : Subobject B := Subobject.mk (𝟙 B)
          have hQtop : Q = (⊤ : Subobject B) := by
            dsimp [Q]
            exact Subobject.mk_eq_top_of_isIso _
          have hPQlt : P < Q := by rw [hQtop]; exact hPtop.lt_top
          have hPQ : P ≤ Q := le_of_lt hPQlt
          let T : ShortComplex C :=
            ShortComplex.mk (Subobject.ofLE P Q hPQ)
              (cokernel.π (Subobject.ofLE P Q hPQ))
              (cokernel.condition (Subobject.ofLE P Q hPQ))
          have hT : T.ShortExact := by
            apply ShortComplex.ShortExact.mk'
            · exact ShortComplex.exact_of_g_is_cokernel _
                (cokernelIsCokernel (Subobject.ofLE P Q hPQ))
            · infer_instance
            · change Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0)
              exact inferInstanceAs (Epi (coequalizer.π (Subobject.ofLE P Q hPQ) 0))
          have hsimpleQ : Simple T.X₃ := by
            change Simple (subobjectQuotient P Q hPQ)
            apply (simple_subobjectQuotient_iff_covBy hPQ).mpr
            exact hQtop ▸ hPtop.covBy_top
          let : Simple T.X₃ := hsimpleQ
          have hQArt : IsArtinianObject T.X₃ := by
            rw [isArtinianObject_iff_not_strictAnti]
            intro f hanti
            have h01 := hanti (Nat.zero_lt_succ 0)
            rcases IsSimpleOrder.eq_bot_or_eq_top (f 0) with h0 | h0
            · exact (not_lt_of_ge bot_le) (h0 ▸ h01)
            · rcases IsSimpleOrder.eq_bot_or_eq_top (f 1) with h1 | h1
              · have h12 := hanti (show 1 < 2 by decide)
                exact (not_lt_of_ge bot_le) (h1 ▸ h12)
              · exact (lt_irrefl _ (h1 ▸ h0 ▸ h01))
          have hQNoeth : IsNoetherianObject T.X₃ := by
            rw [isNoetherianObject_iff_not_strictMono]
            intro f hmono
            have h01 := hmono (Nat.zero_lt_succ 0)
            rcases IsSimpleOrder.eq_bot_or_eq_top (f 1) with h1 | h1
            · rcases IsSimpleOrder.eq_bot_or_eq_top (f 0) with h0 | h0
              · exact (lt_irrefl _ (h0 ▸ h1 ▸ h01))
              · exact (not_lt_of_ge bot_le) (h1 ▸ h0 ▸ h01)
            · have h12 := hmono (show 1 < 2 by decide)
              exact (not_lt_of_ge le_top) (h1 ▸ h12)
          have hBArt : IsArtinianObject T.X₂ :=
            (isArtinianObject_iff_of_shortExact T hT).2 ⟨hPArt, hQArt⟩
          have hBNoeth : IsNoetherianObject T.X₂ :=
            (isNoetherianObject_iff_of_shortExact T hT).2 ⟨hPNoeth, hQNoeth⟩
          have hBArt' : IsArtinianObject B := by
            rw [isArtinianObject_iff_not_strictAnti]
            intro f hanti
            let e := Subobject.mapIsoToOrderIso (Subobject.underlyingIso (𝟙 B))
            let g : ℕ → Subobject T.X₂ := fun n => e.symm (f n)
            have hnot := (isArtinianObject_iff_not_strictAnti T.X₂).1 hBArt
            apply hnot g
            intro a b hab
            apply (e.symm.lt_iff_lt).2
            exact hanti hab
          have hBNoeth' : IsNoetherianObject B := by
            rw [isNoetherianObject_iff_not_strictMono]
            intro f hmono
            let e := Subobject.mapIsoToOrderIso (Subobject.underlyingIso (𝟙 B))
            let g : ℕ → Subobject T.X₂ := fun n => e.symm (f n)
            have hnot := (isNoetherianObject_iff_not_strictMono T.X₂).1 hBNoeth
            apply hnot g
            intro a b hab
            apply (e.symm.lt_iff_lt).2
            exact hmono hab
          exact ⟨hBArt', hBNoeth'⟩
    exact hchain F

/-! ## Jordan-Hölder uniqueness -/

theorem jordan_holder
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    (_hA : IsArtinianObject A ∧ IsNoetherianObject A)
    (F G : FiniteLengthFiltration A) :
    F.series.length = G.series.length ∧
      ∃ σ : Fin F.series.length ≃ Fin G.series.length,
        ∀ i, Nonempty (F.factor i ≅ G.factor (σ i)) := by
  let SF := F.toCompositionSeries
  let SG := G.toCompositionSeries
  have hhead : SF.head = SG.head := by
    change F.series.head = G.series.head
    rw [F.head_eq_bot, G.head_eq_bot]
  have hlast : SF.last = SG.last := by
    change F.series.last = G.series.last
    rw [F.last_eq_top, G.last_eq_top]
  have heq : CompositionSeries.Equivalent SF SG :=
    CompositionSeries.jordan_holder SF SG hhead hlast
  refine ⟨CompositionSeries.Equivalent.length_eq heq, ?_⟩
  refine ⟨heq.choose, ?_⟩
  intro i
  have hi := heq.choose_spec i
  let hFi : F.series (Fin.castSucc i) ≤ F.series i.succ :=
    le_of_lt (by simpa using F.series.step i)
  let hGi : G.series (Fin.castSucc (heq.choose i)) ≤ G.series (heq.choose i).succ :=
    le_of_lt (G.series.step (heq.choose i))
  change Nonempty (subobjectQuotient (F.series (Fin.castSucc i)) (F.series i.succ) hFi ≅
    subobjectQuotient (G.series (Fin.castSucc (heq.choose i)))
      (G.series (heq.choose i).succ) hGi)
  exact jordanHolderLattice_iso_subobjectQuotient hFi hGi hi

end Formalization.Books.Homology.Unit09
