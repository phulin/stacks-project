import Formalization.Books.Dpa.Unit02
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ZMod.Basic

/-!
# Divided Power Algebra, Chapter 3: Divided power rings

This file formalizes the source section “Divided power rings”.  The
divided-power operations themselves are Mathlib's `DividedPowers`; this file
only bundles a ring, an ideal, and that existing structure into the category
used by the chapter.
-/

namespace Formalization.Books.Dpa.Unit03

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/-! ## Divided power rings and their homomorphisms -/

/-- A commutative ring equipped with an ideal and divided powers on it. -/
structure DividedPowerRing where
  toCommRing : CommRingCat.{u}
  ideal : Ideal (toCommRing : Type u)
  dividedPowers : DividedPowers ideal

namespace DividedPowerRing

instance : CoeSort (DividedPowerRing.{u}) (Type u) :=
  ⟨fun A => A.toCommRing⟩

/-!
`DividedPowers.DPMorphism` is Mathlib's bundled morphism for divided power
structures. The following abbreviation makes it the morphism type of the
chapter's ring objects; the pointwise constructor and lemmas below are the
form used by the source definition.
-/
abbrev Hom (A B : DividedPowerRing.{u}) : Type u :=
  DividedPowers.DPMorphism A.dividedPowers B.dividedPowers

/- The name is retained as a projection bridge for earlier chapter consumers. -/
abbrev Hom.hom {A B : DividedPowerRing.{u}} (f : Hom A B) :
    (A : Type u) →+* (B : Type u) := f.toRingHom

def Hom.ofRingHom {A B : DividedPowerRing.{u}} (f : (A : Type u) →+* (B : Type u))
    (ideal_map : ∀ {x : A}, x ∈ A.ideal → f x ∈ B.ideal)
    (dpow_comm : ∀ {n : ℕ} {x : A}, x ∈ A.ideal →
      B.dividedPowers.dpow n (f x) = f (A.dividedPowers.dpow n x)) : Hom A B :=
  DividedPowers.DPMorphism.mk'
    ⟨by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact ideal_map hx,
      by
        intro n x hx
        exact dpow_comm hx⟩

theorem Hom.ideal_map {A B : DividedPowerRing.{u}} (f : Hom A B)
    {x : A} (hx : x ∈ A.ideal) : f x ∈ B.ideal :=
  f.ideal_comp (Ideal.mem_map_of_mem f.toRingHom hx)

theorem Hom.dpow_comm {A B : DividedPowerRing.{u}} (f : Hom A B)
    {n : ℕ} {x : A} (hx : x ∈ A.ideal) :
    B.dividedPowers.dpow n (f x) = f (A.dividedPowers.dpow n x) :=
  f.dpow_comp x hx

@[ext]
theorem Hom.ext {A B : DividedPowerRing.{u}} {f g : Hom A B}
    (h : f.toRingHom = g.toRingHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (DividedPowerRing.{u}) where
  Hom := Hom
  id A := DividedPowers.DPMorphism.id A.dividedPowers
  comp f g := DividedPowers.DPMorphism.comp g f
  id_comp := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  comp_id := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    apply Hom.ext
    ext x
    rfl

end DividedPowerRing

open DividedPowerRing

/-- The underlying-ring forgetful functor. -/
def forget : DividedPowerRing.{u} ⥤ CommRingCat.{u} where
  obj A := A.toCommRing
  map f := CommRingCat.ofHom f.toRingHom

/-- The property that `B` admits a divided-power-ring map from `A`. -/
def IsDividedPowerAlgebra (A B : DividedPowerRing.{u}) : Prop :=
  Nonempty (A ⟶ B)

/-! ## Limits and Brown's representability criterion -/

/-- The category of divided-power rings has all limits. -/
theorem hasLimits : HasLimits (DividedPowerRing.{u}) := by
  classical
  let product (J : Type u) (A : J → DividedPowerRing.{u}) : DividedPowerRing.{u} :=
    { toCommRing := CommRingCat.of (∀ j, (A j : Type u))
      ideal := Ideal.pi (fun j ↦ (A j).ideal)
      dividedPowers :=
        { dpow := fun n x ↦
            if hx : x ∈ Ideal.pi (fun j ↦ (A j).ideal) then
              fun j ↦ (A j).dividedPowers.dpow n (x j)
            else 0
          dpow_null := by
            intro n x hx
            simp only [dif_neg hx]
          dpow_zero := by
            intro x hx
            rw [dif_pos hx]
            funext j
            exact (A j).dividedPowers.dpow_zero ((Ideal.mem_pi _ x).mp hx j)
          dpow_one := by
            intro x hx
            rw [dif_pos hx]
            funext j
            exact (A j).dividedPowers.dpow_one ((Ideal.mem_pi _ x).mp hx j)
          dpow_mem := by
            intro n x hn hx
            rw [dif_pos hx]
            exact (Ideal.mem_pi _ _).mpr fun j ↦
              (A j).dividedPowers.dpow_mem hn ((Ideal.mem_pi _ x).mp hx j)
          dpow_add := by
            intro n x y hx hy
            simp only [dif_pos (Ideal.add_mem _ hx hy), dif_pos hx, dif_pos hy]
            funext j
            simpa only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply] using
              (A j).dividedPowers.dpow_add (n := n)
                ((Ideal.mem_pi _ x).mp hx j) ((Ideal.mem_pi _ y).mp hy j)
          dpow_mul := by
            intro n a x hx
            rw [dif_pos ((Ideal.pi _).mul_mem_left a hx), dif_pos hx]
            funext j
            exact (A j).dividedPowers.dpow_mul ((Ideal.mem_pi _ x).mp hx j)
          mul_dpow := by
            intro m n x hx
            rw [dif_pos hx, dif_pos hx, dif_pos hx]
            funext j
            exact (A j).dividedPowers.mul_dpow ((Ideal.mem_pi _ x).mp hx j)
          dpow_comp := by
            intro m n x hn hx
            have hnx :
                (fun j ↦ (A j).dividedPowers.dpow n (x j)) ∈
                  Ideal.pi (fun j ↦ (A j).ideal) :=
              (Ideal.mem_pi _ _).mpr fun j ↦
                (A j).dividedPowers.dpow_mem hn ((Ideal.mem_pi _ x).mp hx j)
            simp only [dif_pos hx, dif_pos hnx]
            funext j
            exact (A j).dividedPowers.dpow_comp hn ((Ideal.mem_pi _ x).mp hx j) } }
  let productFan (J : Type u) (A : J → DividedPowerRing.{u}) :
      Fan A :=
    Fan.mk (product J A) (fun j ↦
      Hom.ofRingHom (Pi.evalRingHom (fun j ↦ (A j : Type u)) j)
        (by
          intro x hx
          exact (Ideal.mem_pi _ x).mp hx j)
        (by
          intro n x hx
          change (A j).dividedPowers.dpow n (x j) =
            (if h : x ∈ Ideal.pi (fun j ↦ (A j).ideal) then
              fun j ↦ (A j).dividedPowers.dpow n (x j) else 0) j
          change x ∈ Ideal.pi (fun j ↦ (A j).ideal) at hx
          rw [dif_pos hx]))
  let productFanIsLimit (J : Type u) (A : J → DividedPowerRing.{u}) :
      IsLimit (productFan J A) := by
    refine Fan.IsLimit.mk _ (fun s ↦ ?_) (fun s j ↦ ?_) (fun s m hm ↦ ?_)
    · exact
        Hom.ofRingHom (RingHom.pi (fun j ↦ (s.proj j).toRingHom))
          (by
            intro x hx
            exact (Ideal.mem_pi _ _).mpr fun j ↦
              (s.proj j).ideal_map hx)
          (by
            intro n x hx
            have hmap :
                (RingHom.pi (fun j ↦ (s.proj j).toRingHom) x) ∈
                  Ideal.pi (fun j ↦ (A j).ideal) :=
              (Ideal.mem_pi _ _).mpr fun j ↦
                (s.proj j).ideal_map hx
            change (if h : (RingHom.pi (fun j ↦ (s.proj j).toRingHom) x) ∈
                Ideal.pi (fun j ↦ (A j).ideal) then
                fun j ↦ (A j).dividedPowers.dpow n
                  ((s.proj j).toRingHom x) else 0) =
              RingHom.pi (fun j ↦ (s.proj j).toRingHom)
                (s.pt.dividedPowers.dpow n x)
            rw [dif_pos hmap]
            funext j
            exact (s.proj j).dpow_comm hx)
    · apply DividedPowerRing.Hom.ext
      ext x
      rfl
    · apply DividedPowerRing.Hom.ext
      ext x
      funext j
      exact congrArg (fun q ↦ q.toRingHom x) (hm j)
  let : HasProducts (DividedPowerRing.{u}) :=
    hasProducts_of_limit_fans
      (fun {J} A ↦ productFan J A)
      (fun {J} A ↦ productFanIsLimit J A)
  let equalizer (A B : DividedPowerRing.{u}) (f g : A ⟶ B) :
      DividedPowerRing.{u} :=
    let E := RingHom.eqLocus f.toRingHom g.toRingHom
    let e := E.subtype
    { toCommRing := CommRingCat.of E
      ideal := Ideal.comap e A.ideal
      dividedPowers :=
        { dpow := fun n x ↦
            ⟨A.dividedPowers.dpow n (e x), by
              change f.toRingHom (A.dividedPowers.dpow n (e x)) =
                g.toRingHom (A.dividedPowers.dpow n (e x))
              by_cases hx : e x ∈ A.ideal
              · calc
                  f.toRingHom (A.dividedPowers.dpow n (e x)) =
                      B.dividedPowers.dpow n (f.toRingHom (e x)) :=
                    (f.dpow_comm (n := n) (x := e x) hx).symm
                  _ = B.dividedPowers.dpow n (g.toRingHom (e x)) :=
                    congrArg (B.dividedPowers.dpow n) x.property
                  _ = g.toRingHom (A.dividedPowers.dpow n (e x)) :=
                    g.dpow_comm (n := n) (x := e x) hx
              · simp only [A.dividedPowers.dpow_null hx, map_zero]⟩
          dpow_null := by
            intro n x hx
            change e x ∉ A.ideal at hx
            apply Subtype.ext
            apply A.dividedPowers.dpow_null
            exact hx
          dpow_zero := by
            intro x hx
            change e x ∈ A.ideal at hx
            apply Subtype.ext
            exact A.dividedPowers.dpow_zero hx
          dpow_one := by
            intro x hx
            change e x ∈ A.ideal at hx
            apply Subtype.ext
            exact A.dividedPowers.dpow_one hx
          dpow_mem := by
            intro n x hn hx
            change e x ∈ A.ideal at hx
            exact A.dividedPowers.dpow_mem hn hx
          dpow_add := by
            intro n x y hx hy
            change e x ∈ A.ideal at hx
            change e y ∈ A.ideal at hy
            apply Subtype.ext
            change A.dividedPowers.dpow n (e x + e y) = _
            simpa using
              (A.dividedPowers.dpow_add (n := n) hx hy)
          dpow_mul := by
            intro n a x hx
            change e x ∈ A.ideal at hx
            apply Subtype.ext
            exact A.dividedPowers.dpow_mul hx
          mul_dpow := by
            intro m n x hx
            change e x ∈ A.ideal at hx
            apply Subtype.ext
            exact A.dividedPowers.mul_dpow hx
          dpow_comp := by
            intro m n x hn hx
            change e x ∈ A.ideal at hx
            apply Subtype.ext
            exact A.dividedPowers.dpow_comp hn hx } }
  let equalizerFork (A B : DividedPowerRing.{u}) (f g : A ⟶ B) :
      Fork f g :=
    let E := equalizer A B f g
    let eHom : E ⟶ A :=
      Hom.ofRingHom (RingHom.eqLocus f.toRingHom g.toRingHom).subtype
        (by
          intro x hx
          exact hx)
        (by
          intro n x hx
          rfl)
    Fork.ofι eHom
      (by
        apply DividedPowerRing.Hom.ext
        ext x
        exact x.property)
  let equalizerForkIsLimit (A B : DividedPowerRing.{u}) (f g : A ⟶ B) :
      IsLimit (equalizerFork A B f g) := by
    refine Fork.IsLimit.mk' _ (fun s ↦ ?_)
    let E := equalizer A B f g
    let e := (RingHom.eqLocus f.toRingHom g.toRingHom).subtype
    let l : s.pt ⟶ E :=
      Hom.ofRingHom
        (s.ι.toRingHom.codRestrict (RingHom.eqLocus f.toRingHom g.toRingHom)
          (fun x ↦ by
            have h := congrArg (fun q : s.pt ⟶ B ↦ q.toRingHom x) s.condition
            change f.toRingHom (s.ι.toRingHom x) = g.toRingHom (s.ι.toRingHom x) at h
            exact h))
        (by
          intro x hx
          exact s.ι.ideal_map hx)
        (by
          intro n x hx
          apply Subtype.ext
          exact s.ι.dpow_comm hx)
    refine ⟨l, ?_, ?_⟩
    · apply DividedPowerRing.Hom.ext
      ext x
      change s.ι.toRingHom x = s.ι.toRingHom x
      rfl
    · intro m hm
      apply DividedPowerRing.Hom.ext
      ext x
      apply Subtype.ext
      have h := congrArg (fun q : s.pt ⟶ A ↦ q.toRingHom x) hm
      change (RingHom.eqLocus f.toRingHom g.toRingHom).subtype (m.toRingHom x) =
        s.ι.toRingHom x at h
      change (RingHom.eqLocus f.toRingHom g.toRingHom).subtype (m.toRingHom x) =
        s.ι.toRingHom x
      exact h
  let : ∀ {A B : DividedPowerRing.{u}} (f g : A ⟶ B),
      HasLimit (parallelPair f g) := by
    intro A B f g
    exact HasLimit.mk ⟨equalizerFork A B f g, equalizerForkIsLimit A B f g⟩
  let : HasEqualizers (DividedPowerRing.{u}) :=
    hasEqualizers_of_hasLimit_parallelPair (C := DividedPowerRing.{u})
  exact has_limits_of_hasEqualizers_and_products

/-- The underlying-ring functor preserves the limits of divided-power rings. -/
theorem forget_preserves_limits :
    PreservesLimits (forget : DividedPowerRing.{u} ⥤ CommRingCat.{u}) := by
  sorry

/-- The small-source hypothesis in the chapter's version of Brown's lemma. -/
def IsCardinallyGenerated
    (F : DividedPowerRing.{u} ⥤ Type u) (κ : Cardinal.{u}) : Prop :=
  ∀ (A : DividedPowerRing.{u}) (f : F.obj A),
    ∃ (A' : DividedPowerRing.{u}) (g : A' ⟶ A) (f' : F.obj A'),
      Cardinal.mk (A' : Type u) ≤ κ ∧ F.map g f' = f

/-- A covariant set-valued functor is representable by `B`. -/
def IsRepresentableBy (F : DividedPowerRing.{u} ⥤ Type u)
    (B : DividedPowerRing.{u}) : Prop :=
  Nonempty (F.CorepresentableBy B)

/-- Brown's criterion as stated for divided-power rings. -/
theorem representable_of_cardinallyGenerated_of_preservesLimits
    (F : DividedPowerRing.{u} ⥤ Type u) (κ : Cardinal.{u})
    (hsmall : IsCardinallyGenerated F κ)
    (hlim : PreservesLimits F) :
    ∃ B : DividedPowerRing.{u}, IsRepresentableBy F B := by
  sorry

/-! ## Colimits -/

/-- The category of divided-power rings has all colimits. -/
theorem hasColimits : HasColimits (DividedPowerRing.{u}) := by
  sorry

/-! ## Pushouts -/

/-- A pushout square in the category of divided-power rings, expressed by its
universal property.  This is the source's pushout diagram without choosing a
particular Mathlib pushout object. -/
structure PushoutData where
  base : DividedPowerRing.{u}
  leftObject : DividedPowerRing.{u}
  rightObject : DividedPowerRing.{u}
  pushoutObject : DividedPowerRing.{u}
  left : DividedPowerRing.Hom base leftObject
  right : DividedPowerRing.Hom base rightObject
  inl : DividedPowerRing.Hom leftObject pushoutObject
  inr : DividedPowerRing.Hom rightObject pushoutObject
  condition : inl.toRingHom.comp left.toRingHom = inr.toRingHom.comp right.toRingHom
  isPushout : IsColimit
    (PushoutCocone.mk (C := DividedPowerRing.{u}) (X := base)
      (Y := leftObject) (Z := rightObject) (W := pushoutObject)
      (f := left) (g := right) inl inr (by
      apply DividedPowerRing.Hom.ext
      exact condition))

/-- The underlying ring pushout, i.e. the tensor product of the two rings over
the common base, attached to a divided-power pushout square. -/
noncomputable def ringPushout (P : PushoutData) : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom P.left.toRingHom) (CommRingCat.ofHom P.right.toRingHom)

/-- The ideal of the underlying ring pushout generated by the two input
divided-power ideals. -/
noncomputable def ringPushoutIdeal (P : PushoutData) :
    Ideal (ringPushout P : Type u) :=
  Ideal.map (pushout.inl (CommRingCat.ofHom P.left.toRingHom)
      (CommRingCat.ofHom P.right.toRingHom)).hom P.leftObject.ideal ⊔
    Ideal.map (pushout.inr (CommRingCat.ofHom P.left.toRingHom)
      (CommRingCat.ofHom P.right.toRingHom)).hom P.rightObject.ideal

/-!
The next comparison is the canonical ring map from the tensor-product
pushout to the chosen divided-power pushout.  Its existence is the ordinary
pushout universal property in `CommRingCat`.
-/
noncomputable def ringPushoutComparison (P : PushoutData) :
    ringPushout P ⟶ P.pushoutObject.toCommRing := by
  exact pushout.desc (CommRingCat.ofHom P.inl.toRingHom) (CommRingCat.ofHom P.inr.toRingHom)
    (by
      change CommRingCat.ofHom (P.inl.toRingHom.comp P.left.toRingHom) =
        CommRingCat.ofHom (P.inr.toRingHom.comp P.right.toRingHom)
      exact congrArg (fun q => CommRingCat.ofHom q) P.condition)

/-- The quotient of a divided-power ring by its divided-power ideal. -/
def quotientRing (A : DividedPowerRing.{u}) : CommRingCat.{u} :=
  CommRingCat.of ((A : Type u) ⧸ A.ideal)

/-! ## The three pushout consequences -/

/-- The quotient map induced by a divided-power-ring homomorphism. -/
noncomputable def quotientMap {A B : DividedPowerRing.{u}} (f : A ⟶ B) :
    quotientRing A ⟶ quotientRing B := by
  apply CommRingCat.ofHom
  apply Ideal.Quotient.lift A.ideal
    ((Ideal.Quotient.mk B.ideal).comp f.toRingHom)
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (f.ideal_map hx)

/-- The tensor product of the two quotient rings over the quotient base,
represented by the corresponding pushout in `CommRingCat`. -/
noncomputable def quotientRingPushout (P : PushoutData) : CommRingCat.{u} :=
  pushout (quotientMap P.left) (quotientMap P.right)

/-- The first assertion of the pushout remark, with tensor products expressed
by the canonical pushout objects in `CommRingCat`. -/
theorem pushout_quotient_iso (P : PushoutData) :
    Nonempty ((P.pushoutObject.toCommRing ⧸ P.pushoutObject.ideal) ≃+*
      (quotientRingPushout P : Type u)) := by
  sorry

/-- The second assertion of the pushout remark. -/
theorem pushout_ring_comparison_surjective (P : PushoutData) :
    Function.Surjective (ringPushoutComparison P).hom := by
  sorry

/-- The third assertion of the pushout remark: the image of the two input
ideals generates the ideal of the divided-power pushout. -/
theorem pushout_ideal_comparison_surjective (P : PushoutData) :
    Ideal.map (ringPushoutComparison P).hom (ringPushoutIdeal P) =
      P.pushoutObject.ideal := by
  sorry

/-! ## The explicit `ZMod 4` counterexample -/

def integerDividedPowerRing : DividedPowerRing :=
  { toCommRing := CommRingCat.of ℤ
    ideal := ⊥
    dividedPowers := dividedPowersBot ℤ }

def zmodFourIdeal : Ideal (ZMod 4) :=
  Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))

def zmodFourRing (δ : DividedPowers zmodFourIdeal) : DividedPowerRing :=
  { toCommRing := CommRingCat.of (ZMod 4)
    ideal := zmodFourIdeal
    dividedPowers := δ }

def zmodFourDpowTwoIsMap (δ : DividedPowers zmodFourIdeal) (v : ZMod 4) : Prop :=
  ∀ x : ZMod 4, x ∈ zmodFourIdeal →
    δ.dpow 2 x = if x = (2 : ZMod 4) then v else 0

def zmodFourDpowTwoData : Prop :=
  ∃ (δ δ' : DividedPowers zmodFourIdeal),
    zmodFourDpowTwoIsMap δ 2 ∧ zmodFourDpowTwoIsMap δ' 0

/-- The concrete values used in the source's two divided-power structures on
`2 ℤ/4ℤ`. -/
theorem zmodFourDpowTwoData_exists : zmodFourDpowTwoData := by
  sorry

theorem zmodFourDpowTwoIsMap_unique
    {v : ZMod 4} {δ δ' : DividedPowers zmodFourIdeal}
    (hδ : zmodFourDpowTwoIsMap δ v)
    (hδ' : zmodFourDpowTwoIsMap δ' v) :
    δ = δ' := by
  sorry

def ForgetPreservesColimits : Prop :=
  PreservesColimits (forget : DividedPowerRing.{u} ⥤ CommRingCat.{u})

theorem forget_does_not_preserve_colimits : ¬ ForgetPreservesColimits := by
  sorry

/-- The source's explicit pushout counterexample is recorded as a property of
the two structures above: its divided-power pushout is `𝔽₂`, whereas the
underlying tensor-product pushout is not identified with it. -/
theorem forgetful_does_not_preserve_colimits_example :
    ∃ (δ δ' : DividedPowers zmodFourIdeal)
      (P : PushoutData),
      zmodFourDpowTwoIsMap δ 2 ∧
      zmodFourDpowTwoIsMap δ' 0 ∧
      P.base = integerDividedPowerRing ∧
      P.leftObject = zmodFourRing δ ∧
      P.rightObject = zmodFourRing δ' ∧
      Nonempty (P.pushoutObject.toCommRing ≅ CommRingCat.of (ZMod 2)) ∧
      P.pushoutObject.ideal = ⊥ ∧
      ¬ Nonempty (ringPushout P ≅ P.pushoutObject.toCommRing) := by
  sorry

end

end Formalization.Books.Dpa.Unit03
