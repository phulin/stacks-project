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
  constructor
  · intro hF
    rcases hF with ⟨hL, hR⟩
    let : F.Additive := left_or_right_exact_additive F (Or.inl hL)
    let hleft : mapsShortExactOnLeft F :=
      (left_exact_iff_maps_short_exact_on_left F).1 hL
    let hright : mapsShortExactOnRight F :=
      (right_exact_iff_maps_short_exact_on_right F).1 hR
    intro S hS
    let h := hleft S hS
    let h' := hright S hS
    refine ComposableArrows.Exact.mk
      (ComposableArrows.IsComplex.mk (fun i hi => ?_)) ?_
    · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · change (0 : (0 : D) ⟶ F.obj S.X₁) ≫ F.map S.f = 0
        simp
      · change F.map S.f ≫ F.map S.g = 0
        rw [← F.map_comp, S.zero, F.map_zero]
      · change F.map S.g ≫ (0 : F.obj S.X₃ ⟶ (0 : D)) = 0
        simp
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · have h0 := h.exact 0
        change (ShortComplex.mk (0 : (0 : D) ⟶ F.obj S.X₁)
          (F.map S.f) (by simp)).Exact at h0
        exact h0
      · have h1 := h.exact 1
        change (ShortComplex.mk (F.map S.f) (F.map S.g) _).Exact
        change (ShortComplex.mk (F.map S.f) (F.map S.g)
          (by rw [← F.map_comp, S.zero, F.map_zero])).Exact at h1
        exact h1
      · have h2 := h'.exact 1
        change (ShortComplex.mk (F.map S.g)
          (0 : F.obj S.X₃ ⟶ (0 : D)) (by simp)).Exact at h2
        exact h2
  · intro h
    constructor
    · apply (left_exact_iff_maps_short_exact_on_left F).2
      intro S hS
      have h' := h S hS
      have h0 := h'.exact 0
      change (ShortComplex.mk (0 : (0 : D) ⟶ F.obj S.X₁)
        (F.map S.f) (by simp)).Exact at h0
      have h1 := h'.exact 1
      change (ShortComplex.mk (F.map S.f) (F.map S.g)
        (h'.toIsComplex.zero 1)).Exact at h1
      apply ComposableArrows.exact_of_δ₀
      · change (ComposableArrows.mk₂
          (0 : (0 : D) ⟶ F.obj S.X₁) (F.map S.f)).Exact
        exact h0.exact_toComposableArrows
      · change (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact
        exact h1.exact_toComposableArrows
    · apply (right_exact_iff_maps_short_exact_on_right F).2
      intro S hS
      have h' := h S hS
      have h1 := h'.exact 1
      change (ShortComplex.mk (F.map S.f) (F.map S.g)
        (h'.toIsComplex.zero 1)).Exact at h1
      have h2 := h'.exact 2
      change (ShortComplex.mk (F.map S.g)
        (0 : F.obj S.X₃ ⟶ (0 : D)) (by simp)).Exact at h2
      apply ComposableArrows.exact_of_δ₀
      · change (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact
        exact h1.exact_toComposableArrows
      · change (ComposableArrows.mk₂
          (F.map S.g) (0 : F.obj S.X₃ ⟶ (0 : D))).Exact
        exact h2.exact_toComposableArrows

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
  rcases h with ⟨e⟩
  let eHom : ExtensionHom (mapExtensionOfExact F hF E)
      (mapExtensionOfExact F hF E') :=
    { middle := F.map e.hom.middle
      comm_left := by
        change F.map E.inclusion ≫ F.map e.hom.middle = F.map E'.inclusion
        rw [← F.map_comp, e.hom.comm_left]
      comm_right := by
        change F.map e.hom.middle ≫ F.map E'.projection = F.map E.projection
        rw [← F.map_comp, e.hom.comm_right] }
  let eInv : ExtensionHom (mapExtensionOfExact F hF E')
      (mapExtensionOfExact F hF E) :=
    { middle := F.map e.inv.middle
      comm_left := by
        change F.map E'.inclusion ≫ F.map e.inv.middle = F.map E.inclusion
        rw [← F.map_comp, e.inv.comm_left]
      comm_right := by
        change F.map e.inv.middle ≫ F.map E.projection = F.map E'.projection
        rw [← F.map_comp, e.inv.comm_right] }
  have hhom : e.hom.middle ≫ e.inv.middle = 𝟙 E.middle := by
    exact congrArg (fun q : E ⟶ E => q.middle) e.hom_inv_id
  have hinv : e.inv.middle ≫ e.hom.middle = 𝟙 E'.middle := by
    exact congrArg (fun q : E' ⟶ E' => q.middle) e.inv_hom_id
  have hmap_hom : eHom.middle ≫ eInv.middle = 𝟙 _ := by
    dsimp [eHom, eInv]
    change F.map e.hom.middle ≫ F.map e.inv.middle = 𝟙 (F.obj E.middle)
    rw [← F.map_comp, hhom, F.map_id]
  have hmap_inv : eInv.middle ≫ eHom.middle = 𝟙 _ := by
    dsimp [eHom, eInv]
    change F.map e.inv.middle ≫ F.map e.hom.middle = 𝟙 (F.obj E'.middle)
    rw [← F.map_comp, hinv, F.map_id]
  exact ⟨
    { hom := eHom
      inv := eInv
      hom_inv_id := ExtensionHom.ext _ _ hmap_hom
      inv_hom_id := ExtensionHom.ext _ _ hmap_inv }⟩

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
  let : PreservesFiniteLimits F := hF.1
  let : PreservesFiniteColimits F := hF.2
  let hadd : F.Additive := left_or_right_exact_additive F (Or.inl hF.1)
  let : F.Additive := hadd
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hcomparison : IsIso (F.biprodComparison A B) := by
    change IsIso (biprod.lift (F.map biprod.fst) (F.map biprod.snd))
    rw [← F.mapBiprod_hom A B]
    infer_instance
  let : IsIso (F.biprodComparison A B) := hcomparison
  change extensionClass (mapExtensionOfExact F hF (splitExtension A B)) =
    extensionClass (splitExtension (F.obj A) (F.obj B))
  let e : ExtensionHom (mapExtensionOfExact F hF (splitExtension A B))
      (splitExtension (F.obj A) (F.obj B)) :=
    { middle := F.biprodComparison A B
      comm_left := by
        change F.map (biprod.inl : A ⟶ A ⊞ B) ≫ F.biprodComparison A B = biprod.inl
        apply biprod.hom_ext
        · rw [Category.assoc, F.biprodComparison_fst, ← F.map_comp]
          simp
        · rw [Category.assoc, F.biprodComparison_snd, ← F.map_comp]
          simp
      comm_right := by
        change F.biprodComparison A B ≫ biprod.snd =
          F.map (biprod.snd : A ⊞ B ⟶ B)
        simp }
  let eInv : ExtensionHom (splitExtension (F.obj A) (F.obj B))
      (mapExtensionOfExact F hF (splitExtension A B)) :=
    { middle := inv (I := hcomparison) (F.biprodComparison A B)
      comm_left := by
        change biprod.inl ≫ inv (F.biprodComparison A B) =
          F.map (biprod.inl : A ⟶ A ⊞ B)
        apply (cancel_mono (F.biprodComparison A B)).1
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        apply biprod.hom_ext
        · rw [Category.assoc, F.biprodComparison_fst, ← F.map_comp]
          simp
        · rw [Category.assoc, F.biprodComparison_snd, ← F.map_comp]
          simp
      comm_right := by
        change inv (F.biprodComparison A B) ≫
            F.map (biprod.snd : A ⊞ B ⟶ B) = biprod.snd
        apply (cancel_epi (F.biprodComparison A B)).1
        rw [← Category.assoc, IsIso.hom_inv_id (I := hcomparison), Category.id_comp,
          F.biprodComparison_snd] }
  have hhom : e.middle ≫ eInv.middle = 𝟙 _ := by
    dsimp [e, eInv]
    exact IsIso.hom_inv_id (F.biprodComparison A B)
  have hinv : eInv.middle ≫ e.middle = 𝟙 _ := by
    dsimp [e, eInv]
    exact IsIso.inv_hom_id (F.biprodComparison A B)
  apply Quotient.sound
  exact ⟨
    { hom := e
      inv := eInv
      hom_inv_id := ExtensionHom.ext _ _ hhom
      inv_hom_id := ExtensionHom.ext _ _ hinv }⟩

theorem mapExtensionClassOfExact_add
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {A B : C} (F : C ⥤ D) (hF : IsExact F)
    (x y : Ext B A) :
    mapExtensionClassOfExact F hF (x + y) =
      mapExtensionClassOfExact F hF x + mapExtensionClassOfExact F hF y := by
  sorry
/-
  letI : PreservesFiniteLimits F := hF.1
  letI : PreservesFiniteColimits F := hF.2
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF.1)
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  refine Quotient.inductionOn₂ x y ?_
  intro E₁ E₂
  change extensionClass (mapExtensionOfExact F hF (baerSumExtension E₁ E₂)) =
    extensionClass
      (baerSumExtension (mapExtensionOfExact F hF E₁)
        (mapExtensionOfExact F hF E₂))
  let DS : Extension C (A ⊞ A) (B ⊞ B) := directSumExtension E₁ E₂
  let DS' : Extension D (F.obj A ⊞ F.obj A) (F.obj B ⊞ F.obj B) :=
    directSumExtension (mapExtensionOfExact F hF E₁)
      (mapExtensionOfExact F hF E₂)
  let P : Extension C A (B ⊞ B) :=
    pushoutExtension DS (biprodCodiagonal A)
  let P' : Extension D (F.obj A) (F.obj B ⊞ F.obj B) :=
    pushoutExtension DS' (biprodCodiagonal (F.obj A))
  let eA : F.obj (A ⊞ A) ≅ F.obj A ⊞ F.obj A := F.mapBiprod A A
  let eB : F.obj (B ⊞ B) ≅ F.obj B ⊞ F.obj B := F.mapBiprod B B
  let eM : F.obj DS.middle ≅ DS'.middle := by
    change F.obj (E₁.middle ⊞ E₂.middle) ≅
      F.obj E₁.middle ⊞ F.obj E₂.middle
    exact F.mapBiprod E₁.middle E₂.middle
  let fstM : DS'.middle ⟶ (mapExtensionOfExact F hF E₁).middle := biprod.fst
  let sndM : DS'.middle ⟶ (mapExtensionOfExact F hF E₂).middle := biprod.snd
  let fstDS : DS.middle ⟶ E₁.middle := biprod.fst
  let sndDS : DS.middle ⟶ E₂.middle := biprod.snd
  let fstA : A ⊞ A ⟶ A := biprod.fst
  let sndA : A ⊞ A ⟶ A := biprod.snd
  let fstFA : F.obj A ⊞ F.obj A ⟶ F.obj A := biprod.fst
  let sndFA : F.obj A ⊞ F.obj A ⟶ F.obj A := biprod.snd
  have eM_fst :
      eM.hom ≫ fstM =
        F.map fstDS := by
    dsimp [fstM, fstDS]
    change (F.mapBiprod E₁.middle E₂.middle).hom ≫
        (biprod.fst : F.obj E₁.middle ⊞ F.obj E₂.middle ⟶ F.obj E₁.middle) =
      F.map (biprod.fst : E₁.middle ⊞ E₂.middle ⟶ E₁.middle)
    rw [F.mapBiprod_hom]
    simp
  have hDS_fst : DS.inclusion ≫ fstDS = fstA ≫ E₁.inclusion := by
    dsimp [DS, directSumExtension, fstDS, fstA]
    exact biprod.map_fst E₁.inclusion E₂.inclusion
  have hDS_snd : DS.inclusion ≫ sndDS = sndA ≫ E₂.inclusion := by
    dsimp [DS, directSumExtension, sndDS, sndA]
    exact biprod.map_snd E₁.inclusion E₂.inclusion
  have hDS'_fst :
      DS'.inclusion ≫ fstM = fstFA ≫
        (mapExtensionOfExact F hF E₁).inclusion := by
    dsimp [DS', directSumExtension, fstM, fstFA]
    exact biprod.map_fst (mapExtensionOfExact F hF E₁).inclusion
      (mapExtensionOfExact F hF E₂).inclusion
  have hDS'_snd :
      DS'.inclusion ≫ sndM = sndFA ≫
        (mapExtensionOfExact F hF E₂).inclusion := by
    dsimp [DS', directSumExtension, sndM, sndFA]
    exact biprod.map_snd (mapExtensionOfExact F hF E₁).inclusion
      (mapExtensionOfExact F hF E₂).inclusion
  have hA_fst : eA.hom ≫ fstFA = F.map fstA := by
    dsimp [eA, fstFA, fstA]
    rw [F.mapBiprod_hom]
    simp
  have hA_snd : eA.hom ≫ sndFA = F.map sndA := by
    dsimp [eA, sndFA, sndA]
    rw [F.mapBiprod_hom]
    simp
  have hF_map_biprod :
      F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
          (F.mapBiprod E₁.middle E₂.middle).hom =
        (F.mapBiprod A A).hom ≫
          biprod.map (F.map E₁.inclusion) (F.map E₂.inclusion) := by
    apply biprod.hom_ext
    · calc
        (F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
            (F.mapBiprod E₁.middle E₂.middle).hom) ≫ biprod.fst =
            F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
              F.map biprod.fst := by
                rw [F.mapBiprod_hom]
                simp only [Category.assoc, biprod.lift_fst]
        _ = F.map (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.fst) := by
              rw [F.map_comp]
        _ = F.map (biprod.fst ≫ E₁.inclusion) := by
              rw [biprod.map_fst]
        _ = F.map biprod.fst ≫ F.map E₁.inclusion := by
              rw [F.map_comp]
        _ = ((F.mapBiprod A A).hom ≫
            biprod.map (F.map E₁.inclusion) (F.map E₂.inclusion)) ≫
              biprod.fst := by
                rw [F.mapBiprod_hom]
                rw [Category.assoc, biprod.map_fst]
                rw [← Category.assoc, biprod.lift_fst]
    · calc
        (F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
            (F.mapBiprod E₁.middle E₂.middle).hom) ≫ biprod.snd =
            F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
              F.map biprod.snd := by
                rw [F.mapBiprod_hom]
                simp only [Category.assoc, biprod.lift_snd]
        _ = F.map (biprod.map E₁.inclusion E₂.inclusion ≫ biprod.snd) := by
              rw [F.map_comp]
        _ = F.map (biprod.snd ≫ E₂.inclusion) := by
              rw [biprod.map_snd]
        _ = F.map biprod.snd ≫ F.map E₂.inclusion := by
              rw [F.map_comp]
        _ = ((F.mapBiprod A A).hom ≫
            biprod.map (F.map E₁.inclusion) (F.map E₂.inclusion)) ≫
              biprod.snd := by
                rw [F.mapBiprod_hom]
                rw [Category.assoc, biprod.map_snd]
                rw [← Category.assoc, biprod.lift_snd]
  have eM_snd :
      eM.hom ≫ sndM =
        F.map sndDS := by
    dsimp [sndM, sndDS]
    change (F.mapBiprod E₁.middle E₂.middle).hom ≫
        (biprod.snd : F.obj E₁.middle ⊞ F.obj E₂.middle ⟶ F.obj E₂.middle) =
      F.map (biprod.snd : E₁.middle ⊞ E₂.middle ⟶ E₂.middle)
    rw [F.mapBiprod_hom]
    simp
  have hCodiag :
      F.map (biprod.fst : A ⊞ A ⟶ A) +
          F.map (biprod.snd : A ⊞ A ⟶ A) =
        biprod.lift (F.map (biprod.fst : A ⊞ A ⟶ A))
            (F.map (biprod.snd : A ⊞ A ⟶ A)) ≫
          biprodCodiagonal (F.obj A) := by
    rw [biprodCodiagonal]
    exact biprod.add_eq_lift_desc_id
      (F.map (biprod.fst : A ⊞ A ⟶ A))
      (F.map (biprod.snd : A ⊞ A ⟶ A))
  let pMiddle : F.obj P.middle ⟶ P'.middle :=
    (PreservesPushout.iso F (biprodCodiagonal A) DS.inclusion).inv ≫
      pushout.map (F.map (biprodCodiagonal A)) (F.map DS.inclusion)
        (biprodCodiagonal (F.obj A)) DS'.inclusion
        (𝟙 _) eM.hom eA.hom (by
          rw [biprodCodiagonal, biprod.desc_eq, F.map_add,
            F.map_comp, F.map_comp]
          simp only [F.map_id, Category.comp_id]
          dsimp [eA]
          rw [F.mapBiprod_hom]
          exact hCodiag) (by
          apply biprod.hom_ext
          · change (F.map DS.inclusion ≫ eM.hom) ≫
                fstM =
              (eA.hom ≫ DS'.inclusion) ≫
                fstM
            dsimp [DS, DS', directSumExtension, eA, eM, fstM, fstDS, fstA,
              fstFA, mapExtensionOfExact]
            change
              (F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
                  (F.mapBiprod E₁.middle E₂.middle).hom) ≫ biprod.fst =
                ((F.mapBiprod A A).hom ≫
                  biprod.map (F.map E₁.inclusion) (F.map E₂.inclusion)) ≫
                  biprod.fst
            rw [hF_map_biprod]
          · change (F.map DS.inclusion ≫ eM.hom) ≫
                sndM =
              (eA.hom ≫ DS'.inclusion) ≫
                sndM
            dsimp [DS, DS', directSumExtension, eA, eM, sndM, sndDS, sndA,
              sndFA, mapExtensionOfExact]
            change
              (F.map (biprod.map E₁.inclusion E₂.inclusion) ≫
                  (F.mapBiprod E₁.middle E₂.middle).hom) ≫ biprod.snd =
                ((F.mapBiprod A A).hom ≫
                  biprod.map (F.map E₁.inclusion) (F.map E₂.inclusion)) ≫
                  biprod.snd
            rw [hF_map_biprod])
  let m : ExtensionMorphism (mapExtensionOfExact F hF P) P' :=
    { left := 𝟙 _
      middle := pMiddle
      right := eB.hom
      comm_left := by
        rw [Category.id_comp]
        change F.map P.inclusion ≫ pMiddle = P'.inclusion
        dsimp [P, P', pMiddle, pushoutExtension]
        rw [← Category.assoc, PreservesPushout.inl_iso_inv]
        rw [pushout.inl_desc, Category.id_comp]
      comm_right := by
        change pMiddle ≫ P'.projection = F.map P.projection ≫ eB.hom
        dsimp [P, pushoutExtension, pMiddle]
        rw [← (PreservesPushout.iso F (biprodCodiagonal A) DS.inclusion).inv_hom_id_assoc]
        apply (cancel_epi
          (PreservesPushout.iso F (biprodCodiagonal A) DS.inclusion).inv).1
        simp [P, P', DS, DS', eA, eB, eM, directSumExtension, ← F.map_comp] }
  letI : IsIso pMiddle := by
    dsimp [pMiddle]
    infer_instance
  let δ : B ⟶ B ⊞ B := biprodDiagonal B
  let δ' : F.obj B ⟶ F.obj B ⊞ F.obj B :=
    biprodDiagonal (F.obj B)
  let qMap : pullback (F.map P.projection) (F.map δ) ⟶
      pullback P'.projection δ' :=
    pullback.map (F.map P.projection) (F.map δ) P'.projection δ'
      pMiddle (𝟙 _) eB.hom (by
        exact m.comm_right.symm) (by
        simpa [δ, δ', biprodDiagonal, eB] using
          (biprod.map_lift_mapBiprod F B B (𝟙 B) (𝟙 B)))
  letI : IsIso qMap := by
    dsimp [qMap]
    apply pullback.map_isIso
  letI : IsIso (PreservesPullback.iso F P.projection δ).hom := by
    infer_instance
  letI : IsIso (pullbackComparison F P.projection δ) := by
    change IsIso (PreservesPullback.iso F P.projection δ).hom
    infer_instance
  let qMiddle' : F.obj (pullback P.projection δ) ⟶
      pullback P'.projection δ' :=
    (PreservesPullback.iso F P.projection δ).hom ≫ qMap
  letI : IsIso qMiddle' := by
    dsimp [qMiddle']
    exact IsIso.comp_isIso
  let n : ExtensionHom
      (mapExtensionOfExact F hF (pullbackExtension P δ))
      (pullbackExtension P' δ') :=
    { middle := qMiddle'
      comm_left := by
        change F.map (pullbackExtension P δ).inclusion ≫ qMiddle' =
          (pullbackExtension P' δ').inclusion
        apply pullback.hom_ext
        · have hfst := PreservesPullback.iso_hom_fst F P.projection δ
          have hfst_p :
              (PreservesPullback.iso F P.projection δ).hom ≫
                  pullback.fst (F.map P.projection) (F.map δ) ≫ pMiddle =
                F.map (pullback.fst P.projection δ) ≫ pMiddle := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ pMiddle) hfst
          simp only [qMiddle', qMap, pullback.map, pullbackExtension,
            mapExtensionOfExact, Category.assoc, pullback.lift_fst]
          rw [hfst_p]
          rw [← Category.assoc]
          rw [← F.map_comp]
          rw [pullback.lift_fst]
          have hm : F.map P.inclusion ≫ pMiddle =
              (𝟙 (F.obj A)) ≫ P'.inclusion := by
            exact m.comm_left
          simpa only [Category.id_comp] using hm
        · simp only [qMiddle', qMap, pullback.map, pullbackExtension,
            mapExtensionOfExact, Category.assoc]
          rw [pullback.lift_snd]
          have hsnd := PreservesPullback.iso_hom_snd F P.projection δ
          have hsnd_p :
              (PreservesPullback.iso F P.projection δ).hom ≫
                  pullback.snd (F.map P.projection) (F.map δ) ≫ 𝟙 (F.obj B) =
                F.map (pullback.snd P.projection δ) ≫ 𝟙 (F.obj B) := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ 𝟙 (F.obj B)) hsnd
          rw [hsnd_p]
          rw [← Category.assoc]
          rw [← F.map_comp]
          rw [pullback.lift_snd]
          rw [pullback.lift_snd]
          simp
      comm_right := by
        change qMiddle' ≫ (pullbackExtension P' δ').projection =
          F.map (pullbackExtension P δ).projection
        simp [qMiddle', qMap, pullback.map, pullbackExtension, δ, δ',
          Category.assoc, ← F.map_comp] }
  have hn : Nonempty
      (mapExtensionOfExact F hF (pullbackExtension P δ) ≅
        pullbackExtension P' δ') := by
    let nInv : ExtensionHom
        (pullbackExtension P' δ')
        (mapExtensionOfExact F hF (pullbackExtension P δ)) :=
      { middle := inv qMiddle'
        comm_left := by
          apply (cancel_mono qMiddle').1
          simp [n.comm_left]
        comm_right := by
          apply (cancel_epi qMiddle').1
          simp [n.comm_right] }
    exact ⟨
      { hom := n
        inv := nInv
        hom_inv_id := ExtensionHom.ext _ _ (IsIso.hom_inv_id qMiddle')
        inv_hom_id := ExtensionHom.ext _ _ (IsIso.inv_hom_id qMiddle') }⟩
  exact Quotient.sound hn -/

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
  obtain ⟨_⟩ := hAddB
  obtain ⟨hAdj⟩ := hAdj
  obtain ⟨hba⟩ := hba
  let hPreserves : PreservesFiniteLimits b := hLeft
  exact ⟨@CategoryTheory.abelianOfAdjunction _ _ _ _ _ _ _ a b inferInstance
    hPreserves hba hAdj⟩

end Formalization.Books.Homology.Unit07
