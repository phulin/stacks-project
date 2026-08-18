import Formalization.Books.Homology.Unit06.Extensions
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homological Algebra, Chapter 7: Additive functors

The source uses the usual additive, exact, and adjoint functors.  The
declarations below use Mathlib's canonical comparison morphisms, preservation
classes, short-exact complexes, adjunctions, and the extension classes from
Chapter 6.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit06
open scoped ZeroObject

universe v u v' u'

namespace Formalization.Books.Homology.Unit07

/- `AdditiveCategory` in Chapter 3 records finite products, while the
   comparison morphisms below use Mathlib's binary-biproduct instance. -/
instance additiveCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Additive functors and biproducts -/

/- The two comparison morphisms are Mathlib's canonical versions of the
   maps in the source's items (2) and (3), respectively.  The displayed
   matrix and commutative diagram in the source proof are proof scaffolding
   for this comparison, so no parallel matrix API is introduced here. -/
theorem additive_iff_biprod_comparison_isIso
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    [AdditiveCategory C] [AdditiveCategory D] (F : C ⥤ D) :
    (F.Additive ↔ ∀ X Y : C, IsIso (F.biprodComparison' X Y)) ∧
      ((∀ X Y : C, IsIso (F.biprodComparison' X Y)) ↔
        ∀ X Y : C, IsIso (F.biprodComparison X Y)) := by
  have prime_of_additive :
      F.Additive → (∀ X Y : C, IsIso (F.biprodComparison' X Y)) := by
    intro h
    let : F.Additive := h
    let : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    intro X Y
    change IsIso (biprod.desc (F.map biprod.inl) (F.map biprod.inr))
    rw [← F.mapBiprod_inv X Y]
    infer_instance
  have comparison_of_additive :
      F.Additive → (∀ X Y : C, IsIso (F.biprodComparison X Y)) := by
    intro h
    let : F.Additive := h
    let : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    intro X Y
    change IsIso (biprod.lift (F.map biprod.fst) (F.map biprod.snd))
    rw [← F.mapBiprod_hom X Y]
    infer_instance
  have additive_of_hzero_and_prime :
      IsZero (F.obj (0 : C)) →
        (∀ X Y : C, IsIso (F.biprodComparison' X Y)) → F.Additive := by
    intro hzero h
    let : Functor.PreservesZeroMorphisms F :=
      { map_zero := fun X Y => by
          calc
            F.map (0 : X ⟶ Y) =
                F.map ((0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y)) := by simp
            _ = F.map (0 : X ⟶ (0 : C)) ≫ F.map (0 : (0 : C) ⟶ Y) :=
              F.map_comp _ _
            _ = (0 : F.obj X ⟶ F.obj (0 : C)) ≫
                F.map (0 : (0 : C) ⟶ Y) := by
              rw [hzero.eq_of_tgt (F.map (0 : X ⟶ (0 : C)))]
            _ = 0 := by simp }
    have hPB : PreservesBinaryBiproducts F := by
      constructor
      intro X Y
      let : IsIso (F.biprodComparison' X Y) := h X Y
      exact preservesBinaryBiproduct_of_epi_biprodComparison' F
    let : PreservesBinaryBiproducts F := hPB
    exact Functor.additive_of_preservesBinaryBiproducts F
  have additive_of_prime :
      (∀ X Y : C, IsIso (F.biprodComparison' X Y)) → F.Additive := by
    intro h
    let : IsIso (F.biprodComparison' (0 : C) 0) := h 0 0
    let e₀ : (0 : C) ⊞ 0 ≅ (0 : C) := (isoZeroBiprod (isZero_zero C)).symm
    let e : F.obj (0 : C) ⊞ F.obj (0 : C) ≅ F.obj (0 : C) :=
      (asIso (F.biprodComparison' (0 : C) 0)).trans (F.mapIso e₀)
    have heq :
        (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) ≫ e.hom =
          biprod.inr ≫ e.hom := by
      have hmaps :
          F.map (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ 0) =
            F.map (biprod.inr : (0 : C) ⟶ (0 : C) ⊞ 0) :=
        congrArg F.map ((isZero_zero C).eq_of_src _ _)
      simpa [e, e₀, Category.assoc] using
        congrArg (fun k => k ≫ F.map e₀.hom) hmaps
    have hinl :
        (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) = biprod.inr :=
      (cancel_mono e.hom).1 heq
    have hid := congrArg
      (fun k => k ≫
        (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C))) hinl
    have hzero : IsZero (F.obj (0 : C)) :=
      (IsZero.iff_id_eq_zero _).2 (by simpa using hid)
    exact additive_of_hzero_and_prime hzero h
  have additive_of_hzero_and_comparison :
      IsZero (F.obj (0 : C)) →
        (∀ X Y : C, IsIso (F.biprodComparison X Y)) → F.Additive := by
    intro hzero h
    let : Functor.PreservesZeroMorphisms F :=
      { map_zero := fun X Y => by
          calc
            F.map (0 : X ⟶ Y) =
                F.map ((0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y)) := by simp
            _ = F.map (0 : X ⟶ (0 : C)) ≫ F.map (0 : (0 : C) ⟶ Y) :=
              F.map_comp _ _
            _ = (0 : F.obj X ⟶ F.obj (0 : C)) ≫
                F.map (0 : (0 : C) ⟶ Y) := by
              rw [hzero.eq_of_tgt (F.map (0 : X ⟶ (0 : C)))]
            _ = 0 := by simp }
    have hPB : PreservesBinaryBiproducts F := by
      constructor
      intro X Y
      let : IsIso (F.biprodComparison X Y) := h X Y
      exact preservesBinaryBiproduct_of_mono_biprodComparison F
    let : PreservesBinaryBiproducts F := hPB
    exact Functor.additive_of_preservesBinaryBiproducts F
  have additive_of_comparison :
      (∀ X Y : C, IsIso (F.biprodComparison X Y)) → F.Additive := by
    intro h
    let : IsIso (F.biprodComparison (0 : C) 0) := h 0 0
    have hfst :
        (biprod.fst : F.obj (0 : C) ⊞ F.obj (0 : C) ⟶ F.obj (0 : C)) = biprod.snd := by
      apply (cancel_epi (F.biprodComparison (0 : C) 0)).1
      rw [F.biprodComparison_fst, F.biprodComparison_snd]
      exact congrArg F.map ((isZero_zero C).eq_of_tgt _ _)
    have hid := congrArg
      (fun k =>
        (biprod.inl : F.obj (0 : C) ⟶ F.obj (0 : C) ⊞ F.obj (0 : C)) ≫ k) hfst
    have hzero : IsZero (F.obj (0 : C)) :=
      (IsZero.iff_id_eq_zero _).2 (by simpa using hid)
    exact additive_of_hzero_and_comparison hzero h
  exact ⟨⟨prime_of_additive, additive_of_prime⟩,
    ⟨fun h => comparison_of_additive (additive_of_prime h),
      fun h => prime_of_additive (additive_of_comparison h)⟩⟩

/-! ## Exact functors and short exact sequences -/

/- The source writes exact sequences with zero objects at one or both ends.
   `ComposableArrows` records those endpoint maps explicitly and lets the
   exactness predicate express exactness at all internal objects without
   assuming in advance that `F` preserves zero morphisms. -/

def leftExactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 3 :=
  ComposableArrows.mk₃
    (0 : (0 : D) ⟶ F.obj S.X₁)
    (F.map S.f)
    (F.map S.g)

def rightExactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 3 :=
  ComposableArrows.mk₃
    (F.map S.f)
    (F.map S.g)
    (0 : F.obj S.X₃ ⟶ (0 : D))

def exactImageSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) (S : ShortComplex C) : ComposableArrows D 4 :=
  ComposableArrows.mk₄
    (0 : (0 : D) ⟶ F.obj S.X₁)
    (F.map S.f)
    (F.map S.g)
    (0 : F.obj S.X₃ ⟶ (0 : D))

def mapsShortExactOnLeft
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (leftExactImageSequence F S).Exact

def mapsShortExactOnRight
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (rightExactImageSequence F S).Exact

def mapsShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (exactImageSequence F S).Exact

theorem left_or_right_exact_additive
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    (IsLeftExact F ∨ IsRightExact F) → F.Additive := by
  intro h
  exact h.elim
    (fun h => (leftExactFunctor_le_additiveFunctor C D) F h)
    (fun h => (rightExactFunctor_le_additiveFunctor C D) F h)

theorem left_exact_iff_maps_short_exact_on_left
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsLeftExact F ↔ mapsShortExactOnLeft F := by
  constructor
  case mp =>
    intro hF
    let : PreservesFiniteLimits F := hF
    let : F.Additive := left_or_right_exact_additive F (Or.inl hF)
    intro S hS
    have hmap :=
      (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp hF S hS
    rw [ComposableArrows.exact_iff_δ₀]
    constructor
    case left =>
      change (ComposableArrows.mk₂ (0 : (0 : D) ⟶ F.obj S.X₁) (F.map S.f)).Exact
      refine { toIsComplex := ComposableArrows.isComplex₂_mk _ (by exact zero_comp), exact := ?_ }
      intro i hi
      obtain rfl : i = 0 := by omega
      change (ShortComplex.mk (0 : (0 : D) ⟶ F.obj S.X₁) (F.map S.f) _).Exact
      exact (ShortComplex.exact_iff_mono _ (by simp)).2 hmap.2
    case right =>
      change (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact
      exact hmap.1.exact_toComposableArrows
  case mpr =>
    intro hleft
    have hzero_from_zero : ∀ (Y : C), F.map (0 : (0 : C) ⟶ Y) = 0 := by
      intro Y
      let S : ShortComplex C :=
        ShortComplex.mk (0 : (0 : C) ⟶ Y) (𝟙 Y) (by simp)
      have hS : S.ShortExact := by
        let s : S.Splitting :=
          ShortComplex.Splitting.ofIsZeroOfIsIso S (isZero_zero C) (by
            dsimp [S]
            infer_instance)
        exact s.shortExact
      have h := hleft S hS
      have hz := h.toIsComplex.zero 1
      change F.map (0 : (0 : C) ⟶ Y) ≫ F.map (𝟙 Y) = 0 at hz
      rw [F.map_id, Category.comp_id] at hz
      exact hz
    have hmap_zero : ∀ (X Y : C), F.map (0 : X ⟶ Y) = 0 := by
      intro X Y
      calc
        F.map (0 : X ⟶ Y) =
            F.map ((0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y)) := by simp
        _ = F.map (0 : X ⟶ (0 : C)) ≫ F.map (0 : (0 : C) ⟶ Y) :=
          F.map_comp _ _
        _ = 0 := by rw [hzero_from_zero]; simp
    let : Functor.PreservesZeroMorphisms F := { map_zero := hmap_zero }
    have hprime : ∀ X Y : C, IsIso (F.biprodComparison' X Y) := by
      intro X Y
      let S : ShortComplex C :=
        ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (by simp)
      have hS : S.ShortExact := by
        let s : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct X Y
        exact s.shortExact
      let T : ShortComplex D :=
        ShortComplex.mk (F.map S.f) (F.map S.g) (by
          rw [← F.map_comp]
          simp [S])
      have h := hleft S hS
      have hT : T.Exact := by
        exact h.exact 1
      have hfirst :
          (ShortComplex.mk (0 : (0 : D) ⟶ F.obj S.X₁) (F.map S.f) (by simp)).Exact := by
        exact h.exact 0
      have hf' := (ShortComplex.exact_iff_mono _ (by simp)).1 hfirst
      have hf : Mono T.f := by
        change Mono (F.map S.f)
        exact hf'
      let : Mono T.f := hf
      have hg : Epi T.g := by
        let : IsSplitEpi T.g := ⟨⟨F.map biprod.inr, by
          rw [← F.map_comp]
          simp [T, S]⟩⟩
        infer_instance
      let : Epi T.g := hg
      let sp := ShortComplex.Splitting.ofExactOfRetraction T hT (F.map biprod.fst) (by
        rw [← F.map_comp]
        simp [T, S]) hg
      have hsr : sp.s ≫ F.map biprod.fst = 0 := by
        change sp.s ≫ sp.r = 0
        exact sp.s_r
      have hfr : T.f ≫ F.map biprod.fst = 𝟙 _ := by
        change T.f ≫ sp.r = 𝟙 _
        exact sp.f_r
      have hd : (sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y)) ≫ T.g = 0 := by
        rw [sub_comp, sp.s_g]
        simp [T, S, ← F.map_comp]
      let l := hT.lift (sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y)) (by exact hd)
      have hl_f :
          l ≫ T.f = sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y) := by
        exact hT.lift_f _ _
      have hd_r :
          (sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y)) ≫ F.map biprod.fst = 0 := by
        rw [sub_comp, hsr]
        simp [← F.map_comp]
      have hl0 : l = 0 := by
        calc
          l = l ≫ 𝟙 _ := by simp
          _ = l ≫ (T.f ≫ F.map biprod.fst) := by rw [hfr]
          _ = (l ≫ T.f) ≫ F.map biprod.fst := by simp
          _ = (sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y)) ≫ F.map biprod.fst := by
            rw [hl_f]
          _ = 0 := hd_r
      have hsd : sp.s - F.map (biprod.inr : Y ⟶ X ⊞ Y) = 0 := by
        rw [← hl_f, hl0, zero_comp]
      have hs : sp.s = F.map (biprod.inr : Y ⟶ X ⊞ Y) :=
        sub_eq_zero.mp hsd
      have hq : F.biprodComparison' X Y = sp.isoBinaryBiproduct.inv := by
        apply (biprod.ext_from_iff).2
        constructor
        · rw [Functor.inl_biprodComparison']
          simp [ShortComplex.Splitting.isoBinaryBiproduct, T, S]
        · simp [Functor.biprodComparison', ShortComplex.Splitting.isoBinaryBiproduct, hs]
      rw [hq]
      infer_instance
    let : PreservesBinaryBiproducts F :=
      { preserves := fun {X Y} => by
          let : IsIso (F.biprodComparison' X Y) := hprime X Y
          exact preservesBinaryBiproduct_of_epi_biprodComparison' (F := F) (X := X) (Y := Y) }
    have hadd : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
    let : F.Additive := hadd
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).2
    intro S hS
    have h := hleft S hS
    have hex : (S.map F).Exact := by
      exact h.exact 1
    have hfirst :
        (ShortComplex.mk (0 : (0 : D) ⟶ F.obj S.X₁) (F.map S.f) (by simp)).Exact := by
      exact h.exact 0
    have hf' := (ShortComplex.exact_iff_mono _ (by simp)).1 hfirst
    exact ⟨hex, hf'⟩

theorem right_exact_iff_maps_short_exact_on_right
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsRightExact F ↔ mapsShortExactOnRight F := by
  constructor
  case mp =>
    intro hF
    let : PreservesFiniteColimits F := hF
    let : F.Additive := left_or_right_exact_additive F (Or.inr hF)
    intro S hS
    have hmap :=
      (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mp hF S hS
    rw [ComposableArrows.exact_iff_δ₀]
    constructor
    case left =>
      change (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact
      exact hmap.1.exact_toComposableArrows
    case right =>
      change (ComposableArrows.mk₂ (F.map S.g) (0 : F.obj S.X₃ ⟶ (0 : D))).Exact
      refine { toIsComplex := ComposableArrows.isComplex₂_mk _ (by exact comp_zero), exact := ?_ }
      intro i hi
      obtain rfl : i = 0 := by omega
      change (ShortComplex.mk (F.map S.g) (0 : F.obj S.X₃ ⟶ (0 : D)) _).Exact
      exact (ShortComplex.exact_iff_epi _ (by simp)).2 hmap.2
  case mpr =>
    intro hright
    have hzero_to_zero : ∀ (X : C), F.map (0 : X ⟶ (0 : C)) = 0 := by
      intro X
      let S : ShortComplex C :=
        ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (by simp)
      have hS : S.ShortExact := by
        let s : S.Splitting :=
          ShortComplex.Splitting.ofIsIsoOfIsZero S (by
            dsimp [S]
            infer_instance) (isZero_zero C)
        exact s.shortExact
      have h := hright S hS
      have hz := h.toIsComplex.zero 0
      change F.map (𝟙 X) ≫ F.map (0 : X ⟶ (0 : C)) = 0 at hz
      rw [F.map_id, Category.id_comp] at hz
      exact hz
    have hmap_zero : ∀ (X Y : C), F.map (0 : X ⟶ Y) = 0 := by
      intro X Y
      calc
        F.map (0 : X ⟶ Y) =
            F.map ((0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y)) := by simp
        _ = F.map (0 : X ⟶ (0 : C)) ≫ F.map (0 : (0 : C) ⟶ Y) :=
          F.map_comp _ _
        _ = 0 := by rw [hzero_to_zero]; simp
    let : Functor.PreservesZeroMorphisms F := { map_zero := hmap_zero }
    have hcomparison : ∀ X Y : C, IsIso (F.biprodComparison X Y) := by
      intro X Y
      let S : ShortComplex C :=
        ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (by simp)
      have hS : S.ShortExact := by
        let s : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct X Y
        exact s.shortExact
      let T : ShortComplex D :=
        ShortComplex.mk (F.map S.f) (F.map S.g) (by
          rw [← F.map_comp]
          simp [S])
      have h := hright S hS
      have hT : T.Exact := by
        exact h.exact 0
      let : IsSplitMono T.f := ⟨⟨F.map biprod.fst, by
        rw [← F.map_comp]
        simp [T, S]⟩⟩
      have hf : Mono T.f := by infer_instance
      have hlast :
          (ShortComplex.mk (F.map S.g) (0 : F.obj S.X₃ ⟶ (0 : D)) (by simp)).Exact := by
        exact h.exact 1
      have hg' := (ShortComplex.exact_iff_epi _ (by simp)).1 hlast
      have hg : Epi T.g := by
        change Epi (F.map S.g)
        exact hg'
      let : Epi T.g := hg
      let sp := ShortComplex.Splitting.ofExactOfSection T hT (F.map biprod.inr) (by
        rw [← F.map_comp]
        simp [T, S]) hf
      have hsr : F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ sp.r = 0 := by
        change sp.s ≫ sp.r = 0
        exact sp.s_r
      have hsg : F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ T.g = 𝟙 _ := by
        rw [← F.map_comp]
        simp [T, S]
      have hd : T.f ≫
          (F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r) = 0 := by
        rw [comp_sub, ← F.map_comp, sp.f_r]
        simp [T, S]
      let l := hT.desc (F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r) (by exact hd)
      have hl_g :
          T.g ≫ l = F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r := by
        exact hT.g_desc _ _
      have hd_s :
          F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫
              (F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r) = 0 := by
        rw [comp_sub, ← F.map_comp, hsr]
        simp [T, S]
      have hl0 : l = 0 := by
        calc
          l = 𝟙 _ ≫ l := by simp
          _ = (F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ T.g) ≫ l := by rw [hsg]
          _ = F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ (T.g ≫ l) := by simp
          _ = F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫
              (F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r) := by rw [hl_g]
          _ = 0 := hd_s
      have hsd : F.map (biprod.fst : X ⊞ Y ⟶ X) - sp.r = 0 := by
        rw [← hl_g, hl0, comp_zero]
      have hs : sp.r = F.map (biprod.fst : X ⊞ Y ⟶ X) :=
        (sub_eq_zero.mp hsd).symm
      have hq : F.biprodComparison X Y = sp.isoBinaryBiproduct.hom := by
        apply biprod.hom_ext
        · rw [F.biprodComparison_fst]
          change F.map (biprod.fst : X ⊞ Y ⟶ X) =
            (biprod.lift sp.r T.g) ≫ biprod.fst
          rw [biprod.lift_fst]
          exact hs.symm
        · rw [F.biprodComparison_snd]
          change F.map (biprod.snd : X ⊞ Y ⟶ Y) =
            (biprod.lift sp.r T.g) ≫ biprod.snd
          rw [biprod.lift_snd]
      rw [hq]
      infer_instance
    let : PreservesBinaryBiproducts F :=
      { preserves := fun {X Y} => by
          let : IsIso (F.biprodComparison X Y) := hcomparison X Y
          exact preservesBinaryBiproduct_of_mono_biprodComparison
            (F := F) (X := X) (Y := Y) }
    have hadd : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
    let : F.Additive := hadd
    apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).2
    intro S hS
    have h := hright S hS
    have hex : (S.map F).Exact := by
      exact h.exact 0
    have hlast :
        (ShortComplex.mk (F.map S.g) (0 : F.obj S.X₃ ⟶ (0 : D)) (by simp)).Exact := by
      exact h.exact 1
    have hg' := (ShortComplex.exact_iff_epi _ (by simp)).1 hlast
    exact ⟨hex, hg'⟩

theorem exact_iff_maps_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) :
    IsExact F ↔ mapsShortExact F := by
  sorry

/-! ## Exact functors and extension classes -/

/- Applying an exact functor to the middle term and both structure maps gives
   the extension denoted `F(E)` in the source. -/
noncomputable def mapExtensionOfExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) (E : Extension C A B) :
    Extension D (F.obj A) (F.obj B) := by
  letI : PreservesFiniteLimits F := hF.1
  letI : PreservesFiniteColimits F := hF.2
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF.1)
  exact
    { middle := F.obj E.middle
      inclusion := F.map E.inclusion
      projection := F.map E.projection
      zero := by
        rw [← F.map_comp, E.zero, F.map_zero]
      shortExact := by
        simpa [Extension.toShortComplex, ShortComplex.map] using
          E.shortExact.map_of_exact F }

theorem mapExtensionOfExact_preserves_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F)
    {E E' : Extension C A B} (h : Nonempty (E ≅ E')) :
    Nonempty (mapExtensionOfExact F hF E ≅ mapExtensionOfExact F hF E') := by
  sorry

noncomputable def mapExtensionClassOfExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    Ext B A → Ext (F.obj B) (F.obj A) :=
  Quotient.map (mapExtensionOfExact F hF) (by
    intro E E' h
    exact mapExtensionOfExact_preserves_iso F hF h)

theorem mapExtensionClassOfExact_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    mapExtensionClassOfExact F hF (0 : Ext B A) = 0 := by
  sorry

theorem mapExtensionClassOfExact_add
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F)
    (x y : Ext B A) :
    mapExtensionClassOfExact F hF (x + y) =
      mapExtensionClassOfExact F hF x + mapExtensionClassOfExact F hF y := by
  sorry

/-- The abelian-group homomorphism on extension classes induced by an exact functor. -/
noncomputable def exactFunctorExtMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) :
    Ext B A →+ Ext (F.obj B) (F.obj A) where
  toFun := mapExtensionClassOfExact F hF
  map_zero' := mapExtensionClassOfExact_zero F hF
  map_add' := mapExtensionClassOfExact_add F hF

theorem exactFunctorExtMap_extensionClass
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F) (E : Extension C A B) :
    exactFunctorExtMap F hF (extensionClass E) =
      extensionClass (mapExtensionOfExact F hF E) := by
  rfl

/-! ## The adjoint criterion for abelian categories -/

/- The source's displayed kernel/cokernel identities and the subsequent
   coimage--image calculation are the proof route to this criterion.  Their
   objects are represented here by the canonical kernel, cokernel, coimage,
   and image interfaces already used by the abelian-category chapters. -/
theorem abelian_of_exact_retract_right_adjoint
    {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B]
    [AdditiveCategory A] [Abelian B]
    (hAddB : Nonempty (AdditiveCategory B))
    {a : A ⥤ B} {b : B ⥤ A}
    [a.Additive] [b.Additive]
    (hAdj : Nonempty (b ⊣ a))
    (hLeft : IsLeftExact b)
    (hba : Nonempty (a ⋙ b ≅ 𝟭 A)) :
    Nonempty (Abelian A) := by
  sorry

end Formalization.Books.Homology.Unit07
