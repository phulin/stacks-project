import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Order.WithBotTop
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Homology.Unit15.TruncationOfComplexes

/-!
# Derived Categories, Chapter 35: operations on full subcategories

The source identifies full subcategories with object properties.  The
canonical Mathlib operations are used throughout: `retractClosure` for
`smd`, `extensionProduct` for `star`, and `ObjectProperty.map` for the
essential image of a functor.  A one-object full subcategory is already
`ObjectProperty.singleton`; no parallel singleton construction is needed.

The warning in the source that this notation is not universal is retained
here as documentation rather than as mathematical data.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w

namespace Formalization.Books.Derived.Unit35

/-! ## The basic operations -/

section BasicOperations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/- The endpoints live in `EInt = WithBotTop ℤ`, so the source's `-∞` and
   `∞` are available while the indexing objects remain integers. -/

/-! The objects `A[-i]` with `i` in the extended integer interval `[a,b]`. -/
def shiftWindow (P : ObjectProperty C) (a b : EInt) : ObjectProperty C :=
  ⨆ i : {i : ℤ // (a : EInt) ≤ (i : EInt) ∧ (i : EInt) ≤ b},
    P.strictMap (shiftFunctor C (-(i : ℤ)))

/-! The full subcategory of objects isomorphic to finite direct sums from `P`. -/
def add (P : ObjectProperty C) : ObjectProperty C :=
  fun X => ∃ (n : ℕ) (A : Fin n → C),
    (∀ i, P (A i)) ∧ Nonempty ((∐ A) ≅ X)

/-! The full subcategory of objects which are isomorphic to direct summands of `P`. -/
abbrev smd (P : ObjectProperty C) : ObjectProperty C :=
  P.retractClosure

/-! The extension product of two full subcategories. -/
abbrev star (P Q : ObjectProperty C) : ObjectProperty C :=
  ObjectProperty.extensionProduct P Q

/- `starPower P n` is used only with `1 ≤ n`; the harmless value at `n = 0`
   is chosen so that it is total and agrees with Mathlib's iteration API. -/
/-! The `n`-fold extension product `P ⋆ ⋯ ⋆ P` for positive `n`. -/
abbrev starPower (P : ObjectProperty C) (n : ℕ) : ObjectProperty C :=
  P.extensionProductIter (n - 1)

/-! The source's `C_n = smd(add(P)^{⋆ n})` for positive `n`. -/
abbrev conePower (P : ObjectProperty C) (n : ℕ) : ObjectProperty C :=
  smd (starPower (add P) n)

/-! The number of integers in the interval `[a,b]`, when `a ≤ b`. -/
def intervalLength (a b : ℤ) : ℕ :=
  Int.toNat (b - a + 1)

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma add_prop_of_finite_biproduct {J : Type*} [Finite J]
    (P : ObjectProperty C) (X : J → C) (hX : ∀ j, add P (X j)) :
    add P (⨁ X) := by
  choose n A hA hX using hX
  let e : ∀ j, (∐ A j) ≅ X j := fun j => Classical.choice (hX j)
  let K := (Σ j, Fin (n j))
  let fK : Fintype K := Fintype.ofFinite K
  let eK : K ≃ Fin (@Fintype.card K fK) := @Fintype.equivFin K fK
  let ASigma : K → C := fun p => A p.1 p.2
  let B : Fin (@Fintype.card K fK) → C := fun k => ASigma (eK.symm k)
  have hB : ∀ k, P (B k) := by
    intro k
    exact hA (eK.symm k).1 (eK.symm k).2
  let e₁ : (⨁ ASigma) ≅ (⨁ B) :=
    biproduct.whiskerEquiv eK (fun p => eqToIso (by
      dsimp [B]
      exact congrArg ASigma (eK.symm_apply_apply p)))
  let e₂ : (⨁ fun j => ⨁ A j) ≅ (⨁ ASigma) :=
    by
      dsimp [ASigma]
      exact biproductBiproductIso (fun j => Fin (n j)) A
  let e₃ : (⨁ fun j => ⨁ A j) ≅ (⨁ X) :=
    biproduct.mapIso (fun j => biproduct.isoCoproduct (A j) ≪≫ e j)
  refine ⟨@Fintype.card K fK, B, hB, ⟨?_⟩⟩
  exact (biproduct.isoCoproduct B).symm ≪≫ e₁.symm ≪≫ e₂.symm ≪≫ e₃

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma add_isClosedUnderFiniteCoproducts (P : ObjectProperty C) :
    (add P).IsClosedUnderFiniteCoproducts := by
  refine ⟨fun J _ => ?_⟩
  refine ⟨fun X ⟨h⟩ => ?_⟩
  let F := h.diag
  let f : J → C := F.obj ∘ Discrete.mk
  let eF : F ≅ Discrete.functor f := Discrete.natIsoFunctor
  let hc : IsColimit ((Cocone.precompose eF.hom).obj (biproduct.bicone f).toCocone) :=
    (IsColimit.precomposeHomEquiv eF _).symm (biproduct.isColimit f)
  have hB : add P (⨁ f) := add_prop_of_finite_biproduct P f (fun j => h.prop_diag_obj ⟨j⟩)
  rcases hB with ⟨n, B, hB, ⟨eB⟩⟩
  exact ⟨n, B, hB, ⟨eB ≪≫ (h.isColimit.coconePointUniqueUpToIso hc).symm⟩⟩

end BasicOperations

/-! ## Associativity and summand operations -/

section OperationsLaws

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

/-! Associativity of the source's `star` operation. -/
theorem star_assoc (P Q R : ObjectProperty C) :
    star (star P Q) R = star P (star Q R) :=
  ObjectProperty.extensionProduct_assoc P Q R

/-! The first inclusion in the source's `smd-star` lemma. -/
omit [CategoryTheory.IsTriangulated C] in
theorem smd_star_subset (P Q : ObjectProperty C) :
    star (smd P) (smd Q) ≤ smd (star P Q) :=
  ObjectProperty.extensionProduct_retractClosure_retractClosure_le P Q

/-! The equality in the source's `smd-star` lemma. -/
omit [CategoryTheory.IsTriangulated C] in
theorem smd_smd_star_eq (P Q : ObjectProperty C) :
    smd (star (smd P) (smd Q)) = smd (star P Q) :=
  ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure P Q

/-! `add(P) ⋆ add(Q)` is closed under finite direct sums. -/
omit [CategoryTheory.IsTriangulated C] in
private lemma extensionProduct_isClosedUnderFiniteCoproducts
    (P Q : ObjectProperty C) [P.IsClosedUnderFiniteCoproducts]
    [Q.IsClosedUnderFiniteCoproducts] :
    (star P Q).IsClosedUnderFiniteCoproducts := by
  refine ⟨fun J _ => ?_⟩
  refine ⟨fun X ⟨h⟩ => ?_⟩
  let F := h.diag
  let X' : J → C := F.obj ∘ Discrete.mk
  let eF : F ≅ Discrete.functor X' := Discrete.natIsoFunctor
  let hc : IsColimit ((Cocone.precompose eF.hom).obj
      (biproduct.bicone X').toCocone) :=
    (IsColimit.precomposeHomEquiv eF _).symm (biproduct.isColimit X')
  choose Y Z f g k hT hP hQ using fun j => h.prop_diag_obj ⟨j⟩
  let T : J → Triangle C := fun j => Triangle.mk (f j) (g j) (k j)
  have hT' : ∀ j, T j ∈ distTriang C := hT
  have hPI : P.IsClosedUnderIsomorphisms :=
    ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have hQI : Q.IsClosedUnderIsomorphisms :=
    ObjectProperty.IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  have hY : P (∏ᶜ Y) :=
    P.prop_of_iso (biproduct.isoProduct Y)
      (P.prop_of_isColimit (biproduct.isColimit Y) (fun j => hP j.as))
  have hZ : Q (∏ᶜ Z) :=
    Q.prop_of_iso (biproduct.isoProduct Z)
      (Q.prop_of_isColimit (biproduct.isColimit Z) (fun j => hQ j.as))
  have hprod : productTriangle T ∈ distTriang C := productTriangle_distinguished T hT'
  have hstarProd : star P Q (∏ᶜ X') :=
    ⟨_, _, _, _, _, hprod, hY, hZ⟩
  have hstar : star P Q (⨁ X') :=
    ObjectProperty.prop_of_iso (star P Q) (biproduct.isoProduct X').symm hstarProd
  exact ObjectProperty.prop_of_iso (star P Q)
    (h.isColimit.coconePointUniqueUpToIso hc).symm hstar

omit [CategoryTheory.IsTriangulated C] in
theorem add_star_closedUnderDirectSums (P Q : ObjectProperty C) :
    (star (add P) (add Q)).IsClosedUnderFiniteCoproducts := by
  have hPfin : (add P).IsClosedUnderFiniteCoproducts := add_isClosedUnderFiniteCoproducts P
  have hQfin : (add Q).IsClosedUnderFiniteCoproducts := add_isClosedUnderFiniteCoproducts Q
  exact extensionProduct_isClosedUnderFiniteCoproducts (add P) (add Q)

/-! `smd(add(P))` is closed under finite direct sums. -/
omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C] in
private lemma retractClosure_isClosedUnderFiniteCoproducts
    (P : ObjectProperty C) [P.IsClosedUnderFiniteCoproducts] :
    (smd P).IsClosedUnderFiniteCoproducts := by
  refine ⟨fun J _ => ?_⟩
  refine ⟨fun X ⟨h⟩ => ?_⟩
  let F := h.diag
  let X' : J → C := F.obj ∘ Discrete.mk
  let eF : F ≅ Discrete.functor X' := Discrete.natIsoFunctor
  let hc : IsColimit ((Cocone.precompose eF.hom).obj
      (biproduct.bicone X').toCocone) :=
    (IsColimit.precomposeHomEquiv eF _).symm (biproduct.isColimit X')
  choose Y hY hr using fun j => h.prop_diag_obj ⟨j⟩
  let r : ∀ j, Retract (X' j) (Y j) := fun j => Classical.choice (hr j)
  have hY' : P (⨁ Y) :=
    P.prop_of_isColimit (biproduct.isColimit Y) (fun j => hY j.as)
  let hret : Retract (⨁ X') (⨁ Y) :=
    { i := biproduct.map (fun j => (r j).i)
      r := biproduct.map (fun j => (r j).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp [Category.assoc, r] }
  have hX' : smd P (⨁ X') := ObjectProperty.prop_retractClosure hY' hret
  exact ObjectProperty.prop_of_iso (smd P)
    (h.isColimit.coconePointUniqueUpToIso hc).symm hX'

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C] in
theorem smd_add_closedUnderDirectSums (P : ObjectProperty C) :
    (smd (add P)).IsClosedUnderFiniteCoproducts := by
  have hPfin : (add P).IsClosedUnderFiniteCoproducts := add_isClosedUnderFiniteCoproducts P
  exact retractClosure_isClosedUnderFiniteCoproducts (add P)

/-! `C_n` is strictly full. -/
omit [CategoryTheory.IsTriangulated C] in
theorem conePower_isStrictlyFull (P : ObjectProperty C) {n : ℕ} :
    (conePower P n).IsClosedUnderIsomorphisms := by
  infer_instance

/-! `C_n` is closed under direct summands. -/
omit [CategoryTheory.IsTriangulated C] in
theorem conePower_isStableUnderRetracts (P : ObjectProperty C) {n : ℕ} :
    (conePower P n).IsStableUnderRetracts := by
  infer_instance

/-! `C_n` is closed under finite direct sums for positive `n`. -/
omit [CategoryTheory.IsTriangulated C] in
theorem conePower_closedUnderDirectSums (P : ObjectProperty C) {n : ℕ}
    (hn : 1 ≤ n) :
    (conePower P n).IsClosedUnderFiniteCoproducts := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hstarPower : ∀ k : ℕ,
      (starPower (add P) (Nat.succ k)).IsClosedUnderFiniteCoproducts := by
    intro k
    induction k with
    | zero =>
        simpa [starPower] using add_isClosedUnderFiniteCoproducts P
    | succ k ih =>
        have hEq : starPower (add P) (Nat.succ (Nat.succ k)) =
            star (add P) (starPower (add P) (Nat.succ k)) := by
          simp [starPower, ObjectProperty.extensionProductIter_succ]
        rw [hEq]
        have hPfin : (add P).IsClosedUnderFiniteCoproducts :=
          add_isClosedUnderFiniteCoproducts P
        have hPrev : (starPower (add P) (Nat.succ k)).IsClosedUnderFiniteCoproducts := ih
        exact extensionProduct_isClosedUnderFiniteCoproducts
          (add P) (starPower (add P) (Nat.succ k))
  have hPower : (starPower (add P) (Nat.succ k)).IsClosedUnderFiniteCoproducts := hstarPower k
  exact retractClosure_isClosedUnderFiniteCoproducts (starPower (add P) (Nat.succ k))

/-! The source's concatenation law for the subcategories `C_n`. -/
theorem conePower_add (P : ObjectProperty C) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    conePower P (n + m) = smd (star (conePower P n) (conePower P m)) := by
  change smd ((add P).extensionProductIter ((n + m) - 1)) =
    smd (star (smd ((add P).extensionProductIter (n - 1)))
      (smd ((add P).extensionProductIter (m - 1))))
  have hnm : (n + m) - 1 = n + (m - 1) := by omega
  rw [hnm]
  rw [ObjectProperty.extensionProductIter_add (P := add P)
    (Nat.sub_add_cancel hn).symm]
  exact (ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure
    ((add P).extensionProductIter (n - 1))
    ((add P).extensionProductIter (m - 1))).symm

end OperationsLaws

/-! ## Images under exact functors -/

section FunctorOperations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-! The source's full-subcategory image `F(P)`, represented by its essential image. -/
def functorImage (F : C ⥤ D) (P : ObjectProperty C) : ObjectProperty D :=
  P.map F

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-! Exact functors commute with the interval-shift operation up to strict fullness. -/
omit [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [AdditiveCategory C] [AdditiveCategory D]
    [F.IsTriangulated] in
theorem functorImage_shiftWindow (P : ObjectProperty C) (a b : EInt) :
    functorImage F (shiftWindow P a b) =
      (shiftWindow (functorImage F P) a b).isoClosure := by
  ext Y
  unfold functorImage ObjectProperty.map ObjectProperty.isoClosure
  constructor
  · rintro ⟨X, hX, ⟨e⟩⟩
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
    obtain ⟨i, ⟨Z, hZ⟩⟩ := hX
    refine ⟨(shiftFunctor D (-(i : ℤ))).obj (F.obj Z), ?_, ⟨?_⟩⟩
    · rw [shiftWindow]
      exact (ObjectProperty.prop_iSup_iff _ _).2
        ⟨i, ⟨F.obj Z, P.prop_map_obj F hZ⟩⟩
    · exact e.symm ≪≫ asIso ((F.commShiftIso (-(i : ℤ))).hom.app Z)
  · rintro ⟨X, hX, ⟨e⟩⟩
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
    obtain ⟨i, ⟨A, hA⟩⟩ := hX
    rcases hA with ⟨Z, hZ, ⟨eZ⟩⟩
    refine ⟨(shiftFunctor C (-(i : ℤ))).obj Z, ?_, ⟨?_⟩⟩
    · rw [shiftWindow]
      exact (ObjectProperty.prop_iSup_iff _ _).2 ⟨i, ⟨Z, hZ⟩⟩
    · exact asIso ((F.commShiftIso (-(i : ℤ))).hom.app Z) ≪≫
        (shiftFunctor D (-(i : ℤ))).mapIso eZ ≪≫ e.symm

/-! Exact functors preserve direct summands up to direct summands. -/
omit [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [AdditiveCategory C] [HasShift C ℤ] [AdditiveCategory D] [HasShift D ℤ]
    [F.CommShift ℤ] [F.IsTriangulated] in
theorem functorImage_smd (P : ObjectProperty C) :
    functorImage F (smd P) ≤ smd (functorImage F P) := by
  rintro Y ⟨X, ⟨Z, hZ, ⟨r⟩⟩, ⟨e⟩⟩
  refine ⟨F.obj Z, ⟨Z, hZ, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  exact (Retract.ofIso e.symm).trans (r.map F)

/-! Exact functors preserve finite direct sums up to finite direct sums. -/
theorem functorImage_add (P : ObjectProperty C) :
    functorImage F (add P) ≤ add (functorImage F P) := by
  rintro Y ⟨X, hX, ⟨e⟩⟩
  rcases hX with ⟨n, A, hA, ⟨eA⟩⟩
  refine ⟨n, F.obj ∘ A, ?_, ⟨?_⟩⟩
  · intro i
    exact P.prop_map_obj F (hA i)
  · exact (biproduct.isoCoproduct (F.obj ∘ A)).symm ≪≫
      (F.mapBiproduct A).symm ≪≫
      F.mapIso (biproduct.isoCoproduct A ≪≫ eA) ≪≫ e

/-! Exact functors preserve extension products. -/
theorem functorImage_star (P Q : ObjectProperty C) :
    functorImage F (star P Q) ≤ star (functorImage F P) (functorImage F Q) := by
  rintro Y ⟨X, hX, ⟨e⟩⟩
  rcases hX with ⟨X₁, X₂, f, g, h, hT, hP, hQ⟩
  have hT' := F.map_distinguished (Triangle.mk f g h) hT
  change Triangle.mk (F.map f) (F.map g)
      (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁) ∈ distTriang D at hT'
  refine ⟨F.obj X₁, F.obj X₂, F.map f ≫ e.hom, e.inv ≫ F.map g,
    F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁, ?_, ?_, ?_⟩
  · exact isomorphic_distinguished _ hT' _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
        (by
          change (F.map f ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map f
          simp)
        (by
          change (e.inv ≫ F.map g) ≫ 𝟙 _ = e.inv ≫ F.map g
          simp)
        (by
          change (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁) ≫
              (shiftFunctor D (1 : ℤ)).map (𝟙 _) =
            𝟙 _ ≫ (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X₁)
          simp))
  · exact P.prop_map_obj F hP
  · exact Q.prop_map_obj F hQ

/-! Exact functors preserve iterated extension products. -/
theorem functorImage_starPower (P : ObjectProperty C) (n : ℕ) :
    functorImage F (starPower P n) ≤ starPower (functorImage F P) n := by
  cases n with
  | zero => simp [starPower]
  | succ n =>
      change functorImage F (P.extensionProductIter n) ≤
        (functorImage F P).extensionProductIter n
      induction n with
      | zero => simp [ObjectProperty.extensionProductIter_zero]
      | succ n ih =>
          rw [ObjectProperty.extensionProductIter_succ,
            ObjectProperty.extensionProductIter_succ]
          exact (functorImage_star F P (P.extensionProductIter n)).trans
            (ObjectProperty.monotone_extensionProduct_right _ ih)

end FunctorOperations

/-! ## Increasing unions -/

section UnionOperations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

variable (A : ℕ → ObjectProperty C) (hA : Monotone A)

/-! Interval shifts commute with an increasing union. -/
omit [AdditiveCategory C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C] in
theorem shiftWindow_iSup (a b : EInt) :
    shiftWindow (⨆ i, A i) a b = ⨆ i, shiftWindow (A i) a b := by
  ext X
  simp only [shiftWindow, ObjectProperty.prop_iSup_iff,
    ObjectProperty.strictMap_iff]
  constructor
  · rintro ⟨j, Z, ⟨i, hZ⟩, rfl⟩
    exact ⟨i, j, Z, hZ, rfl⟩
  · rintro ⟨i, j, Z, hZ, rfl⟩
    exact ⟨j, Z, ⟨i, hZ⟩, rfl⟩

/-! Direct-summand closure commutes with an increasing union. -/
omit [AdditiveCategory C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C] in
theorem smd_iSup :
    smd (⨆ i, A i) = ⨆ i, smd (A i) := by
  apply le_antisymm
  · intro X hX
    rcases hX with ⟨Y, hY, ⟨r⟩⟩
    rw [ObjectProperty.prop_iSup_iff] at hY
    obtain ⟨i, hY⟩ := hY
    exact (ObjectProperty.prop_iSup_iff _ _).2
      ⟨i, ObjectProperty.prop_retractClosure hY r⟩
  · refine iSup_le ?_
    intro i
    exact ObjectProperty.monotone_retractClosure (le_iSup A i)

/-! Finite direct sums commute with an increasing union. -/
include hA in
theorem add_iSup :
    add (⨆ i, A i) = ⨆ i, add (A i) := by
  apply le_antisymm
  · intro X hX
    rcases hX with ⟨n, T, hT, ⟨e⟩⟩
    choose idx hidx using fun j => (ObjectProperty.prop_iSup_iff _ _).1 (hT j)
    let m : ℕ := Finset.univ.sup idx
    have hidx_le : ∀ j : Fin n, idx j ≤ m := by
      intro j
      exact Finset.le_sup (Finset.mem_univ j)
    exact (ObjectProperty.prop_iSup_iff _ _).2
      ⟨m, ⟨n, T, (fun j => hA (hidx_le j) (T j) (hidx j)), ⟨e⟩⟩⟩
  · refine iSup_le ?_
    intro i X hX
    rcases hX with ⟨n, T, hT, ⟨e⟩⟩
    refine ⟨n, T, ?_, ⟨e⟩⟩
    intro j
    exact (ObjectProperty.prop_iSup_iff _ _).2 ⟨i, hT j⟩

/-! Left extension products commute with an increasing union. -/
theorem iSup_star (B : ObjectProperty C) :
    star (⨆ i, A i) B = ⨆ i, star (A i) B := by
  apply le_antisymm
  · intro X hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hA, hB⟩
    obtain ⟨i, hA⟩ := (ObjectProperty.prop_iSup_iff _ _).1 hA
    exact (ObjectProperty.prop_iSup_iff _ _).2
      ⟨i, ⟨Y, Z, f, g, h, hT, hA, hB⟩⟩
  · refine iSup_le ?_
    intro i
    exact ObjectProperty.monotone_extensionProduct_left B (le_iSup A i)

/-! Right extension products commute with an increasing union. -/
theorem star_iSup (B : ObjectProperty C) :
    star B (⨆ i, A i) = ⨆ i, star B (A i) := by
  apply le_antisymm
  · intro X hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hB, hA⟩
    obtain ⟨i, hA⟩ := (ObjectProperty.prop_iSup_iff _ _).1 hA
    exact (ObjectProperty.prop_iSup_iff _ _).2
      ⟨i, ⟨Y, Z, f, g, h, hT, hB, hA⟩⟩
  · refine iSup_le ?_
    intro i
    exact ObjectProperty.monotone_extensionProduct_right B (le_iSup A i)

omit [CategoryTheory.IsTriangulated C] in
private lemma extensionProduct_iSup_iSup_diag
    (P Q : ℕ → ObjectProperty C) (hP : Monotone P) (hQ : Monotone Q) :
    (⨆ i, ⨆ j, star (P i) (Q j)) = ⨆ k, star (P k) (Q k) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    refine iSup_le ?_
    intro j
    let k := max i j
    have hleft : star (P i) (Q j) ≤ star (P k) (Q j) :=
      ObjectProperty.monotone_extensionProduct_left (Q j)
        (hP (Nat.le_max_left i j))
    have hright : star (P k) (Q j) ≤ star (P k) (Q k) :=
      ObjectProperty.monotone_extensionProduct_right (P k)
        (hQ (Nat.le_max_right i j))
    exact hleft.trans (hright.trans (le_iSup (fun k => star (P k) (Q k)) k))
  · refine iSup_le ?_
    intro k
    exact le_iSup_of_le k (le_iSup_of_le k le_rfl)

/-! Iterated extension products commute with an increasing union. -/
include hA in
theorem starPower_iSup (n : ℕ) :
    starPower (⨆ i, A i) n = ⨆ i, starPower (A i) n := by
  have hPowerMono : ∀ n : ℕ, Monotone (fun i => starPower (A i) n) := by
    intro n
    induction n with
    | zero => simpa [starPower] using hA
    | succ n ih =>
        cases n with
        | zero => simpa [starPower] using hA
        | succ n =>
            intro i j hij
            change (A i).extensionProductIter (n + 1) ≤
              (A j).extensionProductIter (n + 1)
            rw [ObjectProperty.extensionProductIter_succ,
              ObjectProperty.extensionProductIter_succ]
            exact (ObjectProperty.monotone_extensionProduct_left
                ((A i).extensionProductIter n) (hA hij)).trans
              (ObjectProperty.monotone_extensionProduct_right (A j)
                (show (A i).extensionProductIter n ≤
                    (A j).extensionProductIter n from ih hij))
  induction n with
  | zero => simp [starPower]
  | succ n ih =>
      cases n with
      | zero => simp [starPower]
      | succ n =>
          change (⨆ i, A i).extensionProductIter (n + 1) =
            ⨆ i, (A i).extensionProductIter (n + 1)
          simp_rw [ObjectProperty.extensionProductIter_succ]
          have ih' : (⨆ i, A i).extensionProductIter n =
              ⨆ i, (A i).extensionProductIter n := by
            simpa [starPower] using ih
          rw [ih']
          have hright := star_iSup (fun i => (A i).extensionProductIter n)
            (⨆ i, A i)
          have hright' :
              (⨆ i, A i).extensionProduct (⨆ i, (A i).extensionProductIter n) =
                ⨆ i, (⨆ i, A i).extensionProduct ((A i).extensionProductIter n) := by
            simpa only [star] using hright
          rw [hright']
          have hleft (j : ℕ) :
              (⨆ i, A i).extensionProduct ((A j).extensionProductIter n) =
                ⨆ i, (A i).extensionProduct ((A j).extensionProductIter n) := by
            simpa only [star] using iSup_star A ((A j).extensionProductIter n)
          simp_rw [hleft]
          have hdiag := extensionProduct_iSup_iSup_diag A
            (fun i => (A i).extensionProductIter n) hA (hPowerMono (n + 1))
          calc
            (⨆ j, ⨆ i, (A i).extensionProduct ((A j).extensionProductIter n)) =
                ⨆ i, ⨆ j, (A i).extensionProduct ((A j).extensionProductIter n) :=
              iSup_comm
            _ = ⨆ k, (A k).extensionProduct ((A k).extensionProductIter n) := by
              simpa only [star] using hdiag

end UnionOperations

/-! ## The derived-category cone bounds -/

section DerivedConeBounds

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C]

/-! The object property on `D(C)` obtained from a property of `C` in degree zero. -/
def derivedProperty (E : ObjectProperty C) : ObjectProperty (DerivedCategory C) :=
  E.map (DerivedCategory.singleFunctor C 0)

/-! The source's `E[a,b]` after viewing `E` as objects of `D(C)`. -/
def derivedWindowProperty (E : ObjectProperty C) (a b : ℤ) :
    ObjectProperty (DerivedCategory C) :=
  shiftWindow (derivedProperty E) (a : EInt) (b : EInt)

/-! A complex is termwise supported in `[a,b]` by `E`. -/
def complexTermwiseInWindow
    (E : ObjectProperty C) (a b : ℤ) (K : BookComplex C) : Prop :=
  (∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
    (∀ i : ℤ, a ≤ i → i ≤ b → E (K.X i))

/-! An object of the derived category is represented by a complex. -/
def representedByComplex (K : DerivedCategory C) (L : BookComplex C) : Prop :=
  Nonempty ((DerivedCategory.Q (C := C)).obj L ≅ K)

private lemma truncLT_homology_map_iso (K : DerivedCategory C) (b i : ℤ)
    (hi : i < b) :
    IsIso ((derivedCohomologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLTι b).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj K
  let S := (derivedCohomologyFunctor C 0).homologySequenceComposableArrows₅ T
    (i - 1) i (by omega)
  have hG0 : IsZero ((derivedCohomologyFunctor C (i - 1)).obj T.obj₃) :=
    (DerivedCategory.isGE_iff _ b).1 (by infer_instance) (i - 1) (by omega)
  have hG1 : IsZero ((derivedCohomologyFunctor C i).obj T.obj₃) :=
    (DerivedCategory.isGE_iff _ b).1 (by infer_instance) i hi
  have hzero0 : S.map' 2 3 = 0 := by
    dsimp [S, Functor.homologySequenceComposableArrows₅]
    exact hG0.eq_of_src _ _
  have hzero1 : S.map' 4 5 = 0 := by
    dsimp [S, Functor.homologySequenceComposableArrows₅]
    exact hG1.eq_of_tgt _ _
  have hS : S.Exact :=
    (derivedCohomologyFunctor C 0).homologySequenceComposableArrows₅_exact T
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished b K)
      (i - 1) i (by omega)
  have hiS : IsIso (S.map' 3 4) :=
    ComposableArrows.Exact.isIso_map' hS 2 (by omega) hzero0 hzero1
  dsimp [T, S, Functor.homologySequenceComposableArrows₅] at hiS ⊢
  exact hiS

private lemma truncGE_homology_map_iso (K : DerivedCategory C) (b i : ℤ)
    (hi : b ≤ i) :
    IsIso ((derivedCohomologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ b).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj K
  let S := (derivedCohomologyFunctor C 0).homologySequenceComposableArrows₅ T
    i (i + 1) (by omega)
  have hL0 : IsZero ((derivedCohomologyFunctor C i).obj T.obj₁) :=
    (DerivedCategory.isLE_iff _ (b - 1)).1 (by infer_instance) i (by omega)
  have hL1 : IsZero ((derivedCohomologyFunctor C (i + 1)).obj T.obj₁) :=
    (DerivedCategory.isLE_iff _ (b - 1)).1 (by infer_instance) (i + 1) (by omega)
  have hzero0 : S.map' 0 1 = 0 := by
    dsimp [S, Functor.homologySequenceComposableArrows₅]
    exact hL0.eq_of_src _ _
  have hzero1 : S.map' 2 3 = 0 := by
    dsimp [S, Functor.homologySequenceComposableArrows₅]
    exact hL1.eq_of_tgt _ _
  have hS : S.Exact :=
    (derivedCohomologyFunctor C 0).homologySequenceComposableArrows₅_exact T
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished b K)
      i (i + 1) (by omega)
  have hiS : IsIso (S.map' 1 2) :=
    ComposableArrows.Exact.isIso_map' hS 0 (by omega) hzero0 hzero1
  dsimp [T, S, Functor.homologySequenceComposableArrows₅] at hiS ⊢
  exact hiS

private lemma shift_singleFunctor_iso (Y : C) (n : ℤ) :
    Nonempty ((shiftFunctor (DerivedCategory C) (-n)).obj
      ((DerivedCategory.singleFunctor C 0).obj Y) ≅
      (DerivedCategory.singleFunctor C n).obj Y) := by
  let X := (DerivedCategory.singleFunctor C 0).obj Y
  let S := (shiftFunctor (DerivedCategory C) (-n)).obj X
  have hXGE : DerivedCategory.IsGE X 0 := by infer_instance
  have hXLE : DerivedCategory.IsLE X 0 := by infer_instance
  have hSge : DerivedCategory.IsGE S n :=
    @CategoryTheory.Triangulated.TStructure.isGE_shift
      (DerivedCategory C) _ _ _ _ _ _ DerivedCategory.TStructure.t
      X 0 (-n) n (by omega) hXGE
  have hSle : DerivedCategory.IsLE S n :=
    @CategoryTheory.Triangulated.TStructure.isLE_shift
      (DerivedCategory C) _ _ _ _ _ _ DerivedCategory.TStructure.t
      X 0 (-n) n (by omega) hXLE
  obtain ⟨Z, ⟨e⟩⟩ :=
    @DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C _ _ _ S n hSge hSle
  have hIso : (derivedCohomologyFunctor C 0).obj (S⟦n⟧) ≅
      (derivedCohomologyFunctor C n).obj S := by
    simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using
      (asIso (((derivedCohomologyFunctor C 0).isoShift n).hom.app S))
  have hu : S⟦n⟧ ≅ X := by
    dsimp [S]
    exact shiftNegShift (C := DerivedCategory C) (X := X) n
  let eShift : (derivedCohomologyFunctor C n).obj S ≅ Y :=
    hIso.symm ≪≫ (derivedCohomologyFunctor C 0).mapIso hu ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y
  let eZY : Z ≅ Y :=
    ((derivedCohomologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app Z).symm ≪≫ eShift
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C n).mapIso eZY⟩

private lemma derivedProperty_of_iso (E : ObjectProperty C) {X Y : C}
    (hX : derivedProperty E ((DerivedCategory.singleFunctor C 0).obj X))
    (e : X ≅ Y) :
    derivedProperty E ((DerivedCategory.singleFunctor C 0).obj Y) := by
  rcases hX with ⟨Z, hZ, ⟨e'⟩⟩
  exact ⟨Z, hZ, ⟨e' ≪≫ (DerivedCategory.singleFunctor C 0).mapIso e⟩⟩

private lemma add_mono {P Q : ObjectProperty (DerivedCategory C)} (hPQ : P ≤ Q) :
    add P ≤ add Q := by
  intro X hX
  rcases hX with ⟨n, A, hA, ⟨e⟩⟩
  exact ⟨n, A, fun i => hPQ (A i) (hA i), ⟨e⟩⟩

private lemma conePower_mono {P Q : ObjectProperty (DerivedCategory C)}
    (hPQ : P ≤ Q) (n : ℕ) : conePower P n ≤ conePower Q n := by
  exact ObjectProperty.monotone_retractClosure
    (ObjectProperty.monotone_extensionProductIter (add_mono hPQ) (n - 1))

private lemma derivedWindowProperty_mono (E : ObjectProperty C) (a b : ℤ)
    (hab : a ≤ b) :
    derivedWindowProperty E a (b - 1) ≤ derivedWindowProperty E a b := by
  intro X hX
  simp only [derivedWindowProperty, shiftWindow, ObjectProperty.prop_iSup_iff] at hX ⊢
  rcases hX with ⟨i, hi⟩
  refine ⟨⟨i, i.property.1, ?_⟩, hi⟩
  exact le_trans i.property.2 (by simp)

private lemma shifted_smd_add_mem (E : ObjectProperty C) (a b i : ℤ)
    (hai : a ≤ i) (hib : i ≤ b) (X : C) (hX : smd (add E) X) :
    conePower (derivedWindowProperty E a b) 1
      ((shiftFunctor (DerivedCategory C) (-i)).obj
        ((DerivedCategory.singleFunctor C 0).obj X)) := by
  let F : C ⥤ DerivedCategory C :=
    DerivedCategory.singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) (-i)
  let P := derivedWindowProperty E a b
  rcases hX with ⟨Y, hY, ⟨r⟩⟩
  rcases hY with ⟨n, A, hA, ⟨eA⟩⟩
  have hsum : add P (F.obj Y) := by
    refine ⟨n, F.obj ∘ A, ?_, ?_⟩
    · intro j
      dsimp [F]
      simp only [P, derivedWindowProperty, shiftWindow,
        ObjectProperty.prop_iSup_iff]
      refine ⟨⟨i, ?_⟩, ?_⟩
      · exact ⟨by simpa using hai, by simpa using hib⟩
      · exact ObjectProperty.strictMap_obj (derivedProperty E)
          (shiftFunctor (DerivedCategory C) (-i))
          (ObjectProperty.prop_map_obj E (DerivedCategory.singleFunctor C 0)
            (hA j))
    · exact ⟨(biproduct.isoCoproduct (F.obj ∘ A)).symm ≪≫
        (F.mapBiproduct A).symm ≪≫
        F.mapIso (biproduct.isoCoproduct A ≪≫ eA)⟩
  change smd (add P) (F.obj X)
  exact ObjectProperty.prop_retractClosure hsum (r.map F)

private lemma add_smd_add_le (P : ObjectProperty (DerivedCategory C)) :
    add (smd (add P)) ≤ smd (add P) := by
  let _ : (smd (add P)).IsClosedUnderFiniteCoproducts :=
    smd_add_closedUnderDirectSums P
  intro X hX
  rcases hX with ⟨n, A, hA, ⟨e⟩⟩
  exact ObjectProperty.prop_of_iso (smd (add P))
    (biproduct.isoCoproduct A ≪≫ e)
    ((smd (add P)).prop_of_isColimit (biproduct.isColimit A)
      (fun j => hA j.as))

private lemma conePower_one_mono (P : ObjectProperty (DerivedCategory C))
    (n : ℕ) : conePower (conePower P 1) n ≤ conePower P n := by
  change smd (starPower (add (smd (add P))) n) ≤
    smd (starPower (add P) n)
  have h := ObjectProperty.monotone_retractClosure
    (ObjectProperty.monotone_extensionProductIter (add_smd_add_le P) (n - 1))
  rw [ObjectProperty.retractClosure_extensionProductIter_retractClosure
    (P := add P)] at h
  simpa [starPower] using h

private lemma derived_mem_conePower_of_bounds
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hGE : DerivedCategory.IsGE K a)
    (hLE : DerivedCategory.IsLE K b)
    (hE : ∀ i : ℤ, a ≤ i → i ≤ b →
      derivedProperty E ((DerivedCategory.singleFunctor C 0).obj
        ((derivedCohomologyFunctor C i).obj K))) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  have hrec : ∀ d : ℕ, ∀ (a b : ℤ), a ≤ b → ∀ (K : DerivedCategory C),
      DerivedCategory.IsGE K a → DerivedCategory.IsLE K b →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        derivedProperty E ((DerivedCategory.singleFunctor C 0).obj
          ((derivedCohomologyFunctor C i).obj K))) →
      intervalLength a b = d + 1 →
      conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
    intro d
    induction d with
    | zero =>
        intro a b hab K hGE hLE hE hlen
        have hab' : a = b := by
          simp [intervalLength] at hlen
          omega
        subst b
        have hpiece := hE a (by omega) (by omega)
        rcases hpiece with ⟨Y, hY, ⟨eY⟩⟩
        let eYH : Y ≅ (derivedCohomologyFunctor C a).obj K :=
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm ≪≫
            (derivedCohomologyFunctor C 0).mapIso eY ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app
              ((derivedCohomologyFunctor C a).obj K)
        obtain ⟨Z, ⟨eK⟩⟩ :=
          @DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C _ _ _ K a
            hGE hLE
        let eKZ : (derivedCohomologyFunctor C a).obj K ≅ Z :=
          (derivedCohomologyFunctor C a).mapIso eK ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C a).app Z
        obtain ⟨eShift⟩ := shift_singleFunctor_iso Y a
        let eSK : (shiftFunctor (DerivedCategory C) (-a)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y) ≅ K :=
          eShift ≪≫
            (eK ≪≫ (DerivedCategory.singleFunctor C a).mapIso
              (eYH ≪≫ eKZ).symm).symm
        let P := derivedWindowProperty E a a
        have hP : P ((shiftFunctor (DerivedCategory C) (-a)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y)) := by
          simp only [P, derivedWindowProperty, shiftWindow,
            ObjectProperty.prop_iSup_iff]
          refine ⟨⟨a, ?_⟩, ?_⟩
          · simp
          · exact ObjectProperty.strictMap_obj (derivedProperty E)
              (shiftFunctor (DerivedCategory C) (-a))
              (ObjectProperty.prop_map_obj E
                (DerivedCategory.singleFunctor C 0) hY)
        have hadd : add P ((shiftFunctor (DerivedCategory C) (-a)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y)) := by
          let f : Fin 1 → DerivedCategory C := fun _ =>
            (shiftFunctor (DerivedCategory C) (-a)).obj
              ((DerivedCategory.singleFunctor C 0).obj Y)
          refine ⟨1, f, fun _ => hP, ?_⟩
          exact ⟨(biproduct.isoCoproduct f).symm ≪≫ biproductUniqueIso f⟩
        rw [hlen]
        change smd (add P) K
        exact ObjectProperty.prop_retractClosure hadd
          (Retract.ofIso eSK.symm)
    | succ d ih =>
        intro a b hab K hGE hLE hE hlen
        have hab' : a ≠ b := by
          intro h
          subst b
          simp [intervalLength] at hlen
        have hab'' : a ≤ b - 1 := by
          omega
        let T := (DerivedCategory.TStructure.t.triangleLTGE b).obj K
        let L := T.obj₁
        let G := T.obj₃
        have hLGE : DerivedCategory.IsGE L a := by
          apply (DerivedCategory.isGE_iff _ a).2
          intro i hi
          have hK0 := (DerivedCategory.isGE_iff _ a).1 hGE i hi
          have hf : IsIso ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncLTι b).app K)) :=
            truncLT_homology_map_iso K b i (by omega)
          exact IsZero.of_iso hK0 (@asIso C _ _ _
            ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncLTι b).app K)) hf)
        have hLLE : DerivedCategory.IsLE L (b - 1) := by infer_instance
        have hGGE : DerivedCategory.IsGE G b := by infer_instance
        have hGLE : DerivedCategory.IsLE G b := by
          apply (DerivedCategory.isLE_iff _ b).2
          intro i hi
          have hK0 := (DerivedCategory.isLE_iff _ b).1 hLE i hi
          have hf : IsIso ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncGEπ b).app K)) :=
            truncGE_homology_map_iso K b i (by omega)
          exact IsZero.of_iso hK0 (@asIso C _ _ _
            ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncGEπ b).app K)) hf).symm
        have hEL : ∀ i : ℤ, a ≤ i → i ≤ b - 1 →
            derivedProperty E ((DerivedCategory.singleFunctor C 0).obj
              ((derivedCohomologyFunctor C i).obj L)) := by
          intro i hai hib
          have hKpiece := hE i hai (by omega)
          have hf : IsIso ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncLTι b).app K)) :=
            truncLT_homology_map_iso K b i (by omega)
          exact derivedProperty_of_iso E hKpiece (@asIso C _ _ _
            ((derivedCohomologyFunctor C i).map
              ((DerivedCategory.TStructure.t.truncLTι b).app K)) hf).symm
        have hlenL : intervalLength a (b - 1) = d + 1 := by
          simp [intervalLength] at hlen ⊢
          omega
        have hL := ih a (b - 1) hab'' L hLGE hLLE hEL hlenL
        have hL' : conePower (derivedWindowProperty E a b) (d + 1) L := by
          rw [← hlenL]
          exact conePower_mono (derivedWindowProperty_mono E a b hab)
            (intervalLength a (b - 1)) L hL
        have hpiece := hE b (by omega) (by omega)
        rcases hpiece with ⟨Y, hY, ⟨eY⟩⟩
        let eYH : Y ≅ (derivedCohomologyFunctor C b).obj K :=
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm ≪≫
            (derivedCohomologyFunctor C 0).mapIso eY ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app
              ((derivedCohomologyFunctor C b).obj K)
        have hf : IsIso ((derivedCohomologyFunctor C b).map
            ((DerivedCategory.TStructure.t.truncGEπ b).app K)) :=
          truncGE_homology_map_iso K b b (by omega)
        let eKG : (derivedCohomologyFunctor C b).obj K ≅
            (derivedCohomologyFunctor C b).obj G :=
          @asIso C _ _ _ ((derivedCohomologyFunctor C b).map
            ((DerivedCategory.TStructure.t.truncGEπ b).app K)) hf
        obtain ⟨Z, ⟨eG⟩⟩ :=
          @DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C _ _ _ G b
            hGGE hGLE
        let eGZ : (derivedCohomologyFunctor C b).obj G ≅ Z :=
          (derivedCohomologyFunctor C b).mapIso eG ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app Z
        obtain ⟨eShift⟩ := shift_singleFunctor_iso Y b
        let eSG : (shiftFunctor (DerivedCategory C) (-b)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y) ≅ G :=
          eShift ≪≫
            (eG ≪≫ (DerivedCategory.singleFunctor C b).mapIso
              (eYH ≪≫ eKG ≪≫ eGZ).symm).symm
        let P := derivedWindowProperty E a b
        have hP : P ((shiftFunctor (DerivedCategory C) (-b)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y)) := by
          simp only [P, derivedWindowProperty, shiftWindow,
            ObjectProperty.prop_iSup_iff]
          refine ⟨⟨b, ?_⟩, ?_⟩
          · exact ⟨by simpa using hab, by simp⟩
          · exact ObjectProperty.strictMap_obj (derivedProperty E)
              (shiftFunctor (DerivedCategory C) (-b))
              (ObjectProperty.prop_map_obj E
                (DerivedCategory.singleFunctor C 0) hY)
        have hadd : add P ((shiftFunctor (DerivedCategory C) (-b)).obj
            ((DerivedCategory.singleFunctor C 0).obj Y)) := by
          let f : Fin 1 → DerivedCategory C := fun _ =>
            (shiftFunctor (DerivedCategory C) (-b)).obj
              ((DerivedCategory.singleFunctor C 0).obj Y)
          refine ⟨1, f, fun _ => hP, ?_⟩
          exact ⟨(biproduct.isoCoproduct f).symm ≪≫ biproductUniqueIso f⟩
        have hGcone : conePower P 1 G := by
          change smd (add P) G
          exact ObjectProperty.prop_retractClosure hadd
            (Retract.ofIso eSG.symm)
        have hstar : star (conePower P (d + 1)) (conePower P 1) K := by
          refine ⟨L, G, T.mor₁, T.mor₂, T.mor₃, ?_, hL', hGcone⟩
          exact DerivedCategory.TStructure.t.triangleLTGE_distinguished b K
        have hd : 1 ≤ d + 1 := by omega
        have hcone : conePower P ((d + 1) + 1) K := by
          rw [conePower_add P hd (by omega)]
          exact ObjectProperty.prop_retractClosure hstar (Retract.refl K)
        rw [hlen]
        exact hcone
  have hlen : intervalLength a b = (b - a).toNat + 1 := by
    simp only [intervalLength]
    apply Int.ofNat_injective
    calc
      Int.ofNat (b - a + 1).toNat = b - a + 1 :=
        Int.toNat_of_nonneg (by omega)
      _ = b - a + 1 := rfl
      _ = Int.ofNat (b - a).toNat + 1 := by
        congr 1
        exact (Int.toNat_of_nonneg (by omega : 0 ≤ b - a)).symm
      _ = Int.ofNat ((b - a).toNat + 1) := by norm_num
  exact hrec (b - a).toNat a b hab K hGE hLE hE hlen

/-! Cohomology supported in `[a,b]` gives the stated cone bound. -/
theorem derived_mem_conePower_of_cohomology
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hvanish : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((derivedCohomologyFunctor C i).obj K))
    (hE : ∀ i : ℤ, a ≤ i → i ≤ b →
      E ((derivedCohomologyFunctor C i).obj K)) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  have hGE : DerivedCategory.IsGE K a :=
    (DerivedCategory.isGE_iff K a).2 (fun i hi => hvanish i (Or.inl hi))
  have hLE : DerivedCategory.IsLE K b :=
    (DerivedCategory.isLE_iff K b).2 (fun i hi => hvanish i (Or.inr hi))
  have hE' : ∀ i : ℤ, a ≤ i → i ≤ b →
      derivedProperty E ((DerivedCategory.singleFunctor C 0).obj
        ((derivedCohomologyFunctor C i).obj K)) := by
    intro i hai hib
    exact ObjectProperty.prop_map_obj E (DerivedCategory.singleFunctor C 0)
      (hE i hai hib)
  exact derived_mem_conePower_of_bounds E a b hab K hGE hLE hE'

/-! Cohomology in `smd(add(E))` gives the same cone bound. -/
theorem derived_mem_conePower_of_cohomology_smd_add
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hvanish : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((derivedCohomologyFunctor C i).obj K))
    (hE : ∀ i : ℤ, a ≤ i → i ≤ b →
      smd (add E) ((derivedCohomologyFunctor C i).obj K)) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  have hK := derived_mem_conePower_of_cohomology (smd (add E)) a b hab K
    hvanish hE
  have hwindow : derivedWindowProperty (smd (add E)) a b ≤
      conePower (derivedWindowProperty E a b) 1 := by
    intro X hX
    simp only [derivedWindowProperty, shiftWindow,
      ObjectProperty.prop_iSup_iff] at hX
    rcases hX with ⟨j, hX⟩
    rcases (ObjectProperty.strictMap_iff _ _ _).1 hX with ⟨Z, hZ, rfl⟩
    rcases hZ with ⟨Y, hY, ⟨e⟩⟩
    have hs := shifted_smd_add_mem E a b (j : ℤ)
      (by simpa using j.property.1) (by simpa using j.property.2) Y hY
    exact ObjectProperty.prop_of_iso (conePower (derivedWindowProperty E a b) 1)
      ((shiftFunctor (DerivedCategory C) (-(j : ℤ))).mapIso e) hs
  have hK' := conePower_mono hwindow (intervalLength a b) K hK
  exact conePower_one_mono (derivedWindowProperty E a b)
    (intervalLength a b) K hK'

private noncomputable def stupidTruncLE_iso_of_termwise_isZero
    (L : BookComplex C) (b : ℤ)
    (hL : ∀ i : ℤ, b < i → IsZero (L.X i)) :
    Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L b ≅ L := by
  classical
  let e := ComplexShape.embeddingUpIntLE b
  change HomologicalComplex.stupidTrunc L e ≅ L
  have hmem : ∀ {i : ℤ}, i ≤ b → ∃ k : ℕ, e.f k = i := by
    intro i hi
    refine ⟨Int.toNat (b - i), ?_⟩
    dsimp [e, ComplexShape.embeddingUpIntLE, ComplexShape.Embedding.mk']
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ b - i)]
    omega
  let f : ∀ i : ℤ,
      (HomologicalComplex.stupidTrunc L e).X i ≅
        L.X i := fun i => by
    by_cases hi : ∃ k, e.f k = i
    · exact L.stupidTruncXIso e hi.choose_spec
    · have hib : b < i := by
        by_contra h
        exact hi (hmem (by omega))
      exact IsZero.iso
        (HomologicalComplex.isZero_stupidTrunc_X L e i (by
          intro k hk
          exact hi ⟨k, hk⟩))
        (hL i hib)
  refine HomologicalComplex.Hom.isoOfComponents f ?_
  · intro i j hij
    by_cases hi : ∃ k, e.f k = i
    · obtain ⟨k, rfl⟩ := hi
      by_cases hj : ∃ l, e.f l = j
      · obtain ⟨l, rfl⟩ := hj
        have hι (t : ℕ) :
            (f (e.f t)).hom =
              (L.stupidTruncXIso e (rfl : e.f t = e.f t)).hom := by
          by_cases h : ∃ q, e.f q = e.f t
          · dsimp [f]
            rw [dif_pos h]
            change (L.stupidTruncXIso e h.choose_spec).hom = _
            have hp : e.f h.choose = e.f t := h.choose_spec
            have hst : h.choose = t := e.injective_f hp
            simp only [hst]
          · simp only [f, dif_neg h]
            exact (h ⟨t, rfl⟩).elim
        have hd (r s : ℕ) :
            (HomologicalComplex.stupidTrunc L e).d (e.f r) (e.f s) =
              (L.stupidTruncXIso e (rfl : e.f r = e.f r)).hom ≫
                L.d (e.f r) (e.f s) ≫
                (L.stupidTruncXIso e (rfl : e.f s = e.f s)).inv := by
          change ((L.restriction e).extend e).d (e.f r) (e.f s) = _
          dsimp [HomologicalComplex.stupidTrunc]
          rw [HomologicalComplex.extend_d_eq (L.restriction e) e rfl rfl,
            HomologicalComplex.restriction_d_eq L e rfl rfl]
          have hstupid (t : ℕ) :
              (L.stupidTruncXIso e (rfl : e.f t = e.f t)).hom =
                ((L.restriction e).extendXIso e
                  (rfl : e.f t = e.f t)).hom ≫
                  (L.restrictionXIso e
                    (rfl : e.f t = e.f t)).hom := by
            dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
              HomologicalComplex.restrictionXIso,
              HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
            rfl
          have hstupid_inv (t : ℕ) :
              (L.stupidTruncXIso e (rfl : e.f t = e.f t)).inv =
                (L.restrictionXIso e
                  (rfl : e.f t = e.f t)).inv ≫
                  ((L.restriction e).extendXIso e
                    (rfl : e.f t = e.f t)).inv := by
            dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
              HomologicalComplex.restrictionXIso,
              HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
            rfl
          rw [hstupid r, hstupid_inv s]
          simp [Category.assoc]
        rw [hι k, hι l, hd k l]
        simp [Category.assoc]
      · have hz : IsZero (L.X j) := by
          apply hL j
          by_contra h
          exact hj (hmem (by omega))
        exact hz.eq_of_tgt _ _
    · have hzi := HomologicalComplex.isZero_stupidTrunc_X L e i (by
        intro k hk
        exact hi ⟨k, hk⟩)
      exact hzi.eq_of_src _ _

private lemma derived_degreeConcentrated_mem_conePower_one
    (E : ObjectProperty C) (a b n : ℤ) (hai : a ≤ n) (hib : n ≤ b)
    (X : C) (hX : smd (add E) X) :
    conePower (derivedWindowProperty E a b) 1
      ((DerivedCategory.Q (C := C)).obj
        (Formalization.Books.Homology.Unit15.CochainComplex.degreeConcentrated X n)) := by
  have hshift := shifted_smd_add_mem E a b n hai hib X hX
  let eQ :
      (DerivedCategory.Q (C := C)).obj
          (Formalization.Books.Homology.Unit15.CochainComplex.degreeConcentrated X n) ≅
        (shiftFunctor (DerivedCategory C) (-n)).obj
          ((DerivedCategory.singleFunctor C 0).obj X) := by
    simpa [Formalization.Books.Homology.Unit15.CochainComplex.degreeConcentrated,
      Formalization.Books.Homology.Unit14.CochainComplex.concentrated,
      Formalization.Books.Homology.Unit13.cochainComplexSingle] using
      (DerivedCategory.Q.commShiftIso (-n)).app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X)
  exact ObjectProperty.prop_of_iso
    (conePower (derivedWindowProperty E a b) 1) eQ.symm hshift

private lemma derived_mem_conePower_of_complex_aux
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (L : BookComplex C)
    (hL : complexTermwiseInWindow (smd (add E)) a b L) :
    conePower (derivedWindowProperty E a b) (intervalLength a b)
      ((DerivedCategory.Q (C := C)).obj L) := by
  have hrec : ∀ d : ℕ, ∀ (a b : ℤ), a ≤ b → ∀ (L : BookComplex C),
      complexTermwiseInWindow (smd (add E)) a b L →
      intervalLength a b = d + 1 →
      conePower (derivedWindowProperty E a b) (intervalLength a b)
        ((DerivedCategory.Q (C := C)).obj
          (Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L b)) := by
    intro d
    induction d with
    | zero =>
        intro a b hab L hL hlen
        have hab' : a = b := by
          simp [intervalLength] at hlen
          omega
        subst b
        let T :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L a
        let hcomp :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE_components L a
        have hGE : T.IsStrictlyGE a :=
          (CochainComplex.isStrictlyGE_iff T a).2 (by
            intro i hi
            exact (hL.1 i (Or.inl hi)).of_iso
              (Classical.choice (hcomp.1 i (by omega))))
        have hLE : T.IsStrictlyLE a :=
          (CochainComplex.isStrictlyLE_iff T a).2 (by
            intro i hi
            exact hcomp.2 i hi)
        have hpiece : smd (add E) (T.X a) := by
          obtain ⟨e⟩ := hcomp.1 a (by omega)
          exact ObjectProperty.prop_of_iso (smd (add E)) e.symm
            (hL.2 a (by omega) (by omega))
        obtain ⟨M, ⟨eT⟩⟩ :=
          @CochainComplex.exists_iso_single C _ _ T _ a hGE hLE
        have eM : T.X a ≅ M := by
          simpa using HomologicalComplex.Hom.isoApp eT a
        have hM : smd (add E) M :=
          ObjectProperty.prop_of_iso (smd (add E)) eM hpiece
        have hs := shifted_smd_add_mem E a a a (by omega) (by omega)
          M hM
        obtain ⟨eShift⟩ := shift_singleFunctor_iso M a
        have hsingle : conePower (derivedWindowProperty E a a) 1
            ((DerivedCategory.singleFunctor C a).obj M) :=
          ObjectProperty.prop_of_iso (conePower (derivedWindowProperty E a a) 1)
            eShift hs
        have hQT : conePower (derivedWindowProperty E a a) 1
            ((DerivedCategory.Q (C := C)).obj T) := by
          apply ObjectProperty.prop_of_iso (conePower (derivedWindowProperty E a a) 1)
            ((DerivedCategory.Q (C := C)).mapIso eT).symm
          simpa only [DerivedCategory.Q_obj_single_obj] using hsingle
        simpa [T, intervalLength] using hQT
    | succ d ih =>
        intro a b hab L hL hlen
        have habne : a ≠ b := by
          intro heq
          subst b
          simp [intervalLength] at hlen
        have hab' : a ≤ b - 1 := by omega
        let T :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L b
        let Tprev :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L (b - 1)
        let hcomp :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE_components L (b - 1)
        have hT : complexTermwiseInWindow (smd (add E)) a (b - 1) Tprev := by
          constructor
          · intro i hi
            rcases hi with hi | hi
            · by_cases hil : i ≤ b - 1
              · exact (hL.1 i (Or.inl hi)).of_iso
                  (Classical.choice (hcomp.1 i hil))
              · exact hcomp.2 i (by omega)
            · by_cases hil : i ≤ b - 1
              · omega
              · exact hcomp.2 i (by omega)
          · intro i hai hil
            obtain ⟨e⟩ := hcomp.1 i hil
            exact ObjectProperty.prop_of_iso (smd (add E)) e.symm
              (hL.2 i hai (by omega))
        have hlenprev : intervalLength a (b - 1) = d + 1 := by
          simp [intervalLength] at hlen ⊢
          omega
        have hprev0 := ih a (b - 1) hab' Tprev hT hlenprev
        have hprev : conePower (derivedWindowProperty E a (b - 1))
            (intervalLength a (b - 1))
            ((DerivedCategory.Q (C := C)).obj Tprev) := by
          exact ObjectProperty.prop_of_iso
            (conePower (derivedWindowProperty E a (b - 1))
              (intervalLength a (b - 1)))
            ((DerivedCategory.Q (C := C)).mapIso
              (stupidTruncLE_iso_of_termwise_isZero Tprev (b - 1)
                (fun i hi => hT.1 i (Or.inr hi)))) hprev0
        have hprev' : conePower (derivedWindowProperty E a b) (d + 1)
            ((DerivedCategory.Q (C := C)).obj Tprev) := by
          rw [← hlenprev]
          exact conePower_mono (derivedWindowProperty_mono E a b hab)
            (intervalLength a (b - 1)) _ hprev
        obtain ⟨f, hf, ⟨eK⟩⟩ :=
          Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE_transition L b
        let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
        have hS : S.ShortExact :=
          ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel f) inferInstance hf
        let Ttri := DerivedCategory.triangleOfSES hS
        have hkernel : conePower (derivedWindowProperty E a b) 1
            ((DerivedCategory.Q (C := C)).obj (kernel f)) := by
          have hdeg := derived_degreeConcentrated_mem_conePower_one E a b b
            (by omega) (by omega) (L.X b)
            (hL.2 b (by omega) (by omega))
          exact ObjectProperty.prop_of_iso
            (conePower (derivedWindowProperty E a b) 1)
            ((DerivedCategory.Q (C := C)).mapIso eK).symm hdeg
        have hstar : star (conePower (derivedWindowProperty E a b) 1)
            (conePower (derivedWindowProperty E a b) (d + 1))
            ((DerivedCategory.Q (C := C)).obj T) := by
          refine ⟨(DerivedCategory.Q (C := C)).obj (kernel f),
            (DerivedCategory.Q (C := C)).obj Tprev, Ttri.mor₁, Ttri.mor₂,
            Ttri.mor₃, ?_, hkernel, hprev'⟩
          exact DerivedCategory.triangleOfSES_distinguished hS
        have hd : 1 ≤ d + 1 := by omega
        have hcone : conePower (derivedWindowProperty E a b) ((d + 1) + 1)
            ((DerivedCategory.Q (C := C)).obj T) := by
          rw [show (d + 1) + 1 = 1 + (d + 1) by omega]
          rw [conePower_add (derivedWindowProperty E a b) (by omega) hd]
          exact ObjectProperty.prop_retractClosure hstar (Retract.refl _)
        rw [hlen]
        exact hcone
  have htop := hrec (intervalLength a b - 1) a b hab L hL (by
    simp [intervalLength]
    omega)
  have htop' : conePower (derivedWindowProperty E a b) (intervalLength a b)
      ((DerivedCategory.Q (C := C)).obj
        (Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncLE L b)) :=
    htop
  exact ObjectProperty.prop_of_iso
    (conePower (derivedWindowProperty E a b) (intervalLength a b))
    ((DerivedCategory.Q (C := C)).mapIso
      (stupidTruncLE_iso_of_termwise_isZero L b
        (fun i hi => hL.1 i (Or.inr hi)))) htop'

/-! A bounded complex with terms in `E` gives the stated cone bound. -/
theorem derived_mem_conePower_of_complex
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hK : ∃ L : BookComplex C,
      representedByComplex K L ∧ complexTermwiseInWindow E a b L) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  rcases hK with ⟨L, ⟨eK⟩, hL⟩
  have hL' : complexTermwiseInWindow (smd (add E)) a b L := by
    refine ⟨hL.1, ?_⟩
    intro i hai hib
    let f : Fin 1 → C := fun _ => L.X i
    have hadd : add E (L.X i) := by
      refine ⟨1, f, fun _ => hL.2 i hai hib, ?_⟩
      exact ⟨(biproduct.isoCoproduct f).symm ≪≫ biproductUniqueIso f⟩
    exact ObjectProperty.prop_retractClosure hadd (Retract.refl _)
  exact ObjectProperty.prop_of_iso
    (conePower (derivedWindowProperty E a b) (intervalLength a b)) eK
    (derived_mem_conePower_of_complex_aux E a b hab L hL')

/-! A bounded complex with terms in `smd(add(E))` gives the same bound. -/
theorem derived_mem_conePower_of_complex_smd_add
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hK : ∃ L : BookComplex C,
      representedByComplex K L ∧ complexTermwiseInWindow (smd (add E)) a b L) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  rcases hK with ⟨L, ⟨eK⟩, hL⟩
  exact ObjectProperty.prop_of_iso
    (conePower (derivedWindowProperty E a b) (intervalLength a b)) eK
    (derived_mem_conePower_of_complex_aux E a b hab L hL)

end DerivedConeBounds

/-! ## The forward cone bound for a homological functor -/

section ForwardConeBound

variable {T : Type u} [Category.{v} T] [AdditiveCategory T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [CategoryTheory.IsTriangulated T]
  {A : Type u'} [Category.{v'} A] [Abelian A]

omit [CategoryTheory.IsTriangulated T] in
private lemma homological_forward_shiftWindow
    (H : T ⥤ A) [H.IsHomological]
    (a b : ℤ) (m : ℕ) (E : ObjectProperty T)
    (hE : ∀ ⦃X : T⦄, E X → ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologicalDegree H i).obj X))
    {i : ℤ} {Y : T}
    (hY : shiftWindow E (((-(m : ℤ)) : ℤ) : EInt)
      (((m : ℤ) : ℤ) : EInt) Y)
    (hi : i < -(m : ℤ) + a ∨ (m : ℤ) + b < i) :
    IsZero ((homologicalDegree H i).obj Y) := by
  simp only [shiftWindow, ObjectProperty.prop_iSup_iff] at hY
  rcases hY with ⟨j, hY⟩
  rcases (ObjectProperty.strictMap_iff _ _ _).1 hY with ⟨Z, hZ, rfl⟩
  have hjlo : -(m : ℤ) ≤ (j : ℤ) := by
    simpa using j.property.1
  have hjhi : (j : ℤ) ≤ (m : ℤ) := by
    simpa using j.property.2
  have hbase : i - (j : ℤ) < a ∨ b < i - (j : ℤ) := by
    rcases hi with hi | hi
    · left
      omega
    · right
      omega
  change IsZero (H.obj ((shiftFunctor T i).obj
    ((shiftFunctor T (-(j : ℤ))).obj Z)))
  simpa [homologicalDegree] using
    IsZero.of_iso (hE hZ (i - (j : ℤ)) hbase)
      (H.mapIso ((shiftFunctorAdd' T (-(j : ℤ)) i (i - (j : ℤ))
        (by omega)).app Z)).symm

omit [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [CategoryTheory.IsTriangulated T] in
private lemma homological_isZero_of_additive_coproduct
    (F : T ⥤ A) [F.Additive] {r : ℕ} (A' : Fin r → T)
    (hA : ∀ j, IsZero (F.obj (A' j))) :
    IsZero (F.obj (∐ A')) := by
  have hB : IsZero (⨁ fun j => F.obj (A' j)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro j
    exact (hA j).eq_of_tgt _ _
  have hsum : IsZero (F.obj (⨁ A')) :=
    hB.of_iso (F.mapBiproduct A')
  exact hsum.of_iso (F.mapIso (biproduct.isoCoproduct A').symm)

omit [CategoryTheory.IsTriangulated T] in
private lemma homological_forward_conePower_aux
    (H : T ⥤ A) [H.IsHomological]
    (a b : ℤ) (E : ObjectProperty T)
    (hE : ∀ ⦃X : T⦄, E X → ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologicalDegree H i).obj X))
    {m n : ℕ} (X : T)
    (hX : conePower (shiftWindow E (((-(m : ℤ)) : ℤ) : EInt)
      (((m : ℤ) : ℤ) : EInt)) n X) :
    ∀ i : ℤ, i < -(m : ℤ) + a ∨ (m : ℤ) + b < i →
      IsZero ((homologicalDegree H i).obj X) := by
  let P : ObjectProperty T := shiftWindow E (((-(m : ℤ)) : ℤ) : EInt)
    (((m : ℤ) : ℤ) : EInt)
  let ZP : ObjectProperty T := fun Y =>
    ∀ i : ℤ, i < -(m : ℤ) + a ∨ (m : ℤ) + b < i →
      IsZero ((homologicalDegree H i).obj Y)
  have hP : P ≤ ZP := by
    intro Y hY i hi
    exact homological_forward_shiftWindow H a b m E hE hY hi
  have hadd : add P ≤ ZP := by
    intro Y hY i hi
    rcases hY with ⟨r, A', hA, ⟨e⟩⟩
    have hF : (homologicalDegree H i).Additive := by
      dsimp [homologicalDegree]
      infer_instance
    have hcoprod : IsZero ((homologicalDegree H i).obj (∐ A')) := by
      exact @homological_isZero_of_additive_coproduct T _ _ A _ _
        (homologicalDegree H i) hF r A'
          (fun j => (hP _ (hA j) i hi))
    exact hcoprod.of_iso ((homologicalDegree H i).mapIso e).symm
  have hstar : star ZP ZP ≤ ZP := by
    intro Y hY i hi
    rcases hY with ⟨Y₁, Y₃, f, g, h, hT, h₁, h₃⟩
    let T' := Triangle.mk f g h
    let Tshift := (Triangle.shiftFunctor T i).obj T'
    have hex := H.map_distinguished_exact Tshift
      (Triangle.shift_distinguished T' hT i)
    change IsZero (H.obj ((shiftFunctor T i).obj Y))
    simpa [T', Tshift] using
      hex.isZero_of_both_isZero (h₁ i hi) (h₃ i hi)
  have hret : ZP.retractClosure ≤ ZP := by
    intro Y hY i hi
    rcases hY with ⟨Y', hY', ⟨r⟩⟩
    let F := homologicalDegree H i
    change IsZero (F.obj Y)
    have hr : F.map r.i ≫ F.map r.r = 𝟙 _ := by
      rw [← F.map_comp, r.retract, F.map_id]
    have hri : F.map r.i = 0 := by
      simpa [F, homologicalDegree] using (hY' i hi).eq_of_tgt _ _
    apply (IsZero.iff_id_eq_zero _).2
    rw [← hr]
    rw [hri]
    simp
  have hiter : ∀ k : ℕ, (add P).extensionProductIter k ≤ ZP := by
    intro k
    induction k with
    | zero => simpa only [ObjectProperty.extensionProductIter_zero] using hadd
    | succ k ih =>
        rw [ObjectProperty.extensionProductIter_succ]
        exact (ObjectProperty.monotone_extensionProduct_left _ hadd).trans
          ((ObjectProperty.monotone_extensionProduct_right _ ih).trans hstar)
  have hcone : conePower P n ≤ ZP := by
    change smd ((add P).extensionProductIter (n - 1)) ≤ ZP
    exact (ObjectProperty.monotone_retractClosure (hiter (n - 1))).trans hret
  intro i hi
  exact hcone X (by simpa [P] using hX) i hi

/-!
The printed source bound incorrectly multiplies the support endpoints by the
number of extension factors.  Homological exactness preserves a common
support interval under extensions, so the correct interval is `[-m + a, m + b]`.
-/
omit [CategoryTheory.IsTriangulated T] in
theorem homological_forward_conePower
    (H : T ⥤ A) [H.IsHomological]
    (a b : ℤ) (hab : a ≤ b) (E : ObjectProperty T)
    (hE : ∀ ⦃X : T⦄, E X → ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologicalDegree H i).obj X))
    {m n : ℕ} (hn : 1 ≤ n) (X : T)
    (hX : conePower (shiftWindow E (((-(m : ℤ)) : ℤ) : EInt)
    (((m : ℤ) : ℤ) : EInt)) n X) :
    ∀ i : ℤ,
      i < -(m : ℤ) + a ∨
      (m : ℤ) + b < i →
      IsZero ((homologicalDegree H i).obj X) := by
  have _hn : 1 ≤ n := hn
  have _hab : a ≤ b := hab
  exact homological_forward_conePower_aux H a b E hE X hX

end ForwardConeBound

end Formalization.Books.Derived.Unit35
