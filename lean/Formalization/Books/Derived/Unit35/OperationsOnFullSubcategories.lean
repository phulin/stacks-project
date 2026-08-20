import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Order.WithBotTop
import Formalization.Books.Derived.Unit11.DerivedCategories

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
  sorry

/-! Exact functors preserve extension products. -/
theorem functorImage_star (P Q : ObjectProperty C) :
    functorImage F (star P Q) ≤ star (functorImage F P) (functorImage F Q) := by
  sorry

/-! Exact functors preserve iterated extension products. -/
theorem functorImage_starPower (P : ObjectProperty C) (n : ℕ) :
    functorImage F (starPower P n) ≤ starPower (functorImage F P) n := by
  sorry

end FunctorOperations

/-! ## Increasing unions -/

section UnionOperations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

variable (A : ℕ → ObjectProperty C) (hA : Monotone A)

/-! Interval shifts commute with an increasing union. -/
theorem shiftWindow_iSup (a b : EInt) :
    shiftWindow (⨆ i, A i) a b = ⨆ i, shiftWindow (A i) a b := by
  sorry

/-! Direct-summand closure commutes with an increasing union. -/
theorem smd_iSup :
    smd (⨆ i, A i) = ⨆ i, smd (A i) := by
  sorry

/-! Finite direct sums commute with an increasing union. -/
theorem add_iSup :
    add (⨆ i, A i) = ⨆ i, add (A i) := by
  sorry

/-! Left extension products commute with an increasing union. -/
theorem iSup_star (B : ObjectProperty C) :
    star (⨆ i, A i) B = ⨆ i, star (A i) B := by
  sorry

/-! Right extension products commute with an increasing union. -/
theorem star_iSup (B : ObjectProperty C) :
    star B (⨆ i, A i) = ⨆ i, star B (A i) := by
  sorry

/-! Iterated extension products commute with an increasing union. -/
theorem starPower_iSup (n : ℕ) :
    starPower (⨆ i, A i) n = ⨆ i, starPower (A i) n := by
  sorry

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

/-! Cohomology supported in `[a,b]` gives the stated cone bound. -/
theorem derived_mem_conePower_of_cohomology
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hvanish : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((derivedCohomologyFunctor C i).obj K))
    (hE : ∀ i : ℤ, a ≤ i → i ≤ b →
      E ((derivedCohomologyFunctor C i).obj K)) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  sorry

/-! Cohomology in `smd(add(E))` gives the same cone bound. -/
theorem derived_mem_conePower_of_cohomology_smd_add
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hvanish : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((derivedCohomologyFunctor C i).obj K))
    (hE : ∀ i : ℤ, a ≤ i → i ≤ b →
      smd (add E) ((derivedCohomologyFunctor C i).obj K)) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  sorry

/-! A bounded complex with terms in `E` gives the stated cone bound. -/
theorem derived_mem_conePower_of_complex
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hK : ∃ L : BookComplex C,
      representedByComplex K L ∧ complexTermwiseInWindow E a b L) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  sorry

/-! A bounded complex with terms in `smd(add(E))` gives the same bound. -/
theorem derived_mem_conePower_of_complex_smd_add
    (E : ObjectProperty C) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory C)
    (hK : ∃ L : BookComplex C,
      representedByComplex K L ∧ complexTermwiseInWindow (smd (add E)) a b L) :
    conePower (derivedWindowProperty E a b) (intervalLength a b) K := by
  sorry

end DerivedConeBounds

/-! ## The forward cone bound for a homological functor -/

section ForwardConeBound

variable {T : Type u} [Category.{v} T] [AdditiveCategory T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [CategoryTheory.IsTriangulated T]
  {A : Type u'} [Category.{v'} A] [Abelian A]

/-!
The printed source bound incorrectly multiplies the support endpoints by the
number of extension factors.  Homological exactness preserves a common
support interval under extensions, so the correct interval is `[-m + a, m + b]`.
-/
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
  sorry

end ForwardConeBound

end Formalization.Books.Derived.Unit35
