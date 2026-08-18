import Formalization.Books.Homology.Unit13.Complexes
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Homological Algebra, Chapter 14: Homotopy and the shift functor

The source uses the same shift convention for chain and cochain complexes.
Mathlib already provides the cochain-complex shift and its homology shift
sequence.  The chain-complex shift is recorded here with explicit
shift-identity isomorphisms and the same componentwise normalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

universe v u

namespace Formalization.Books.Homology.Unit14

/-! ## A source-facing formulation of principal homogeneous spaces -/

/-- A principal homogeneous space records a simply transitive additive action.
This is the set-theoretic content of the source's “principal homogeneous
space under a group” wording. -/
structure PrincipalHomogeneousSpace (G P : Type*) [AddGroup G] where
  nonempty : Nonempty P
  translate : G → P → P
  translate_zero : ∀ p, translate 0 p = p
  translate_add : ∀ (g h : G) (p : P), translate (g + h) p = translate g (translate h p)
  existsUnique : ∀ p q, ∃! g, translate g p = q

/-! ## Chain-complex shifts -/

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

set_option backward.defeqAttrib.useBackward true in
/-- The shift of a chain complex by `n`, with the sign convention of the
source. -/
@[simps]
def shiftFunctor (n : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ where
  obj K :=
    { X := fun i => K.X (i + n)
      d := fun _ _ => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        rw [K.shape, smul_zero]
        intro hij'
        apply hij
        dsimp at hij' ⊢
        lia }
  map φ :=
    { f := fun _ => φ.f _
      comm' := by
        intros
        dsimp
        simp only [Linear.comp_units_smul, Hom.comm, Linear.units_smul_comp] }
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance (n : ℤ) : (shiftFunctor C n).Additive where

variable {C}

@[simp]
def shiftFunctorObjXIso (K : ChainComplex C ℤ) (n i m : ℤ) (hm : m = i + n) :
    ((shiftFunctor C n).obj K).X i ≅ K.X m :=
  K.XIsoOfEq hm.symm

variable (C)

attribute [local simp] XIsoOfEq_hom_naturality

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
def shiftFunctorZero' (n : ℤ) (h : n = 0) :
  shiftFunctor C n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => shiftFunctorObjXIso K _ _ _ (by lia))
    (fun _ _ _ => by simp [shiftFunctorObjXIso, h])) (fun _ ↦ by ext; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
  shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => shiftFunctorObjXIso K _ _ _ (by lia))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul,
        XIsoOfEq_hom_comp_d]))
    (by intros; ext; simp)

end ChainComplex

/-! ## Shift identities and degree-concentrated complexes -/

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

noncomputable def shift_zero :
    shiftFunctor C (0 : ℤ) ≅ 𝟭 (ChainComplex C ℤ) :=
  shiftFunctorZero' C 0 rfl

noncomputable def shift_add (k l : ℤ) :
    shiftFunctor C (k + l) ≅ shiftFunctor C k ⋙ shiftFunctor C l :=
  shiftFunctorAdd' C k l (k + l) rfl

noncomputable def shift_comm (k l : ℤ) :
    shiftFunctor C k ⋙ shiftFunctor C l ≅ shiftFunctor C l ⋙ shiftFunctor C k :=
  (shiftFunctorAdd' C k l (k + l) rfl).symm ≪≫
    eqToIso (congrArg (shiftFunctor C) (add_comm k l)) ≪≫
      shiftFunctorAdd' C l k (l + k) rfl

variable (C)

noncomputable def concentrated (A : C) (k : ℤ) [HasZeroObject C] : ChainComplex C ℤ :=
  (shiftFunctor C k).obj
    ((Formalization.Books.Homology.Unit13.chainComplexSingle C).obj A)

variable {C}

theorem concentrated_at (A : C) (k : ℤ) [HasZeroObject C] :
    (concentrated C A k).X (-k) = A := by
  sorry

theorem concentrated_isZero (A : C) (k n : ℤ) (hn : n ≠ -k) [HasZeroObject C] :
    IsZero ((concentrated C A k).X n) := by
  sorry

end ChainComplex

/-! ## Homology shifts and homotopies for chain complexes -/

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A chain homology-shift comparison is a natural isomorphism, so its
componentwise functoriality is part of the interface rather than a separate
choice for each morphism. -/
abbrev ChainHomologyShiftComparison (k i : ℤ) :=
  HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) (i + k) ≅
    (shiftFunctor C k) ⋙
      HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) i

/-- The source's functorial homology-shift comparison exists. -/
theorem chain_homology_shift_comparison_exists (k i : ℤ) :
    Nonempty (ChainHomologyShiftComparison (C := C) k i) := by
  sorry

/-- The source-facing homology-shift identification for chain complexes.
The shift functor is the explicit one above; the existence statement keeps
the canonical homology comparison abstract while retaining its exact source
type. -/
theorem chain_homology_shift_identification
    (K : ChainComplex C ℤ) (k i : ℤ) :
    Nonempty (K.homology (i + k) ≅
      ((shiftFunctor C k).obj K).homology i) := by
  sorry

/-- The homology-shift identification is functorial in the complex. -/
theorem chain_homology_shift_functorial
    {A B : ChainComplex C ℤ} (f : A ⟶ B) (k i : ℤ) :
    ∃ eA : A.homology (i + k) ≅ ((shiftFunctor C k).obj A).homology i,
      ∃ eB : B.homology (i + k) ≅ ((shiftFunctor C k).obj B).homology i,
        eA.hom ≫ HomologicalComplex.homologyMap ((shiftFunctor C k).map f) i =
          HomologicalComplex.homologyMap f (i + k) ≫ eB.hom := by
  sorry

/-- The shift comparisons can be chosen compatibly with two successive
shifts and the comparison `shiftFunctor (k + l) ≅ shiftFunctor k ⋙
shiftFunctor l`. -/
theorem chain_homology_shift_coherent
    (K : ChainComplex C ℤ) (k l i : ℤ) :
    ∃ e : K.homology (i + (k + l)) ≅
        ((shiftFunctor C (k + l)).obj K).homology i,
      ∃ e' : K.homology (i + (k + l)) ≅
          (((shiftFunctor C k) ⋙ (shiftFunctor C l)).obj K).homology i,
        e.hom ≫
            HomologicalComplex.homologyMap
              ((shift_add (C := C) k l).hom.app K) i = e'.hom := by
  sorry

variable {A B : ChainComplex C ℤ}

/-- A self-homotopy is parametrized by a map into the shifted target. -/
theorem chain_homotopy_shift_self (a : A ⟶ B) :
    Nonempty (Homotopy a a ≃ (A ⟶ (shiftFunctor C 1).obj B)) := by
  sorry

/-- For two maps, the homotopy set is empty or a principal homogeneous space
under the additive group of maps into the shifted target. -/
theorem chain_homotopy_shift_principal (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (PrincipalHomogeneousSpace (A ⟶ (shiftFunctor C 1).obj B)
        (Homotopy a b)) := by
  sorry

/-! ## Termwise split short exact sequences of chain complexes -/

/-- A family of splittings of the degreewise short complexes underlying a
short complex of chain complexes.  The splittings are deliberately indexed
degreewise: they are not required to form a morphism of complexes. -/
def TermwiseSplitting (S : ShortComplex (ChainComplex C ℤ)) :=
  ∀ n : ℤ,
    (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).Splitting

/-- The degree `n` map `π_{n-1} d_B s_n` from the source. -/
def termwiseSplitConnectingFamily
    {S : ShortComplex (ChainComplex C ℤ)}
    (s : TermwiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ S.X₁.X (n + (-1 : ℤ)) :=
  (s n).s ≫ S.X₂.d n (n + (-1 : ℤ)) ≫ (s (n + (-1 : ℤ))).r

/-- The source's connecting family assembled into a map to the negative
shift. -/
structure TermwiseSplitConnectingMap
    {S : ShortComplex (ChainComplex C ℤ)} (s : TermwiseSplitting S) where
  hom : S.X₃ ⟶ (shiftFunctor C (-1 : ℤ)).obj S.X₁
  hom_f : ∀ n : ℤ, hom.f n = termwiseSplitConnectingFamily s n

theorem termwiseSplitConnectingMap_exists
    {S : ShortComplex (ChainComplex C ℤ)} (s : TermwiseSplitting S) :
    Nonempty (TermwiseSplitConnectingMap s) := by
  sorry

/-- The unique degreewise difference between two choices of section. -/
def termwiseSplittingDifference
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₃ ⟶
      (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₁ :=
  (s' n).s ≫ (s n).r

/-- The same difference, viewed as a component of a homotopy into the
negative shift. -/
def termwiseSplittingDifferenceShift
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ ((shiftFunctor C (-1 : ℤ)).obj S.X₁).X (n + 1) :=
  termwiseSplittingDifference s s' n ≫
    eqToHom (by
      change S.X₁.X n = S.X₁.X ((n + 1) + (-1 : ℤ))
      congr 1
      lia)

theorem termwiseSplitting_section_eq
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    (s' n).s = (s n).s +
      termwiseSplittingDifference s s' n ≫
        (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).f := by
  sorry

theorem termwiseSplitting_difference_unique
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ)
    {h : (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₃ ⟶
      (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₁}
    (hh : (s' n).s = (s n).s + h ≫
      (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).f) :
    h = termwiseSplittingDifference s s' n := by
  sorry

/-- The map obtained from a termwise splitting induces the canonical
connecting morphism after the homology-shift identification. -/
theorem termwiseSplitConnectingMap_induces_connecting
    {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact)
    (s : TermwiseSplitting S) (δ : TermwiseSplitConnectingMap s) (i : ℤ) :
    ∃ e : ((shiftFunctor C (-1 : ℤ)).obj S.X₁).homology i ≅
        S.X₁.homology (i - 1),
      HomologicalComplex.homologyMap δ.hom i ≫ e.hom =
        Formalization.Books.Homology.Unit13.chainConnectingMap hS i := by
  sorry

/-- Changing a termwise splitting changes the resulting connecting maps by a
homotopy. -/
theorem termwiseSplitConnectingMap_homotopic
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S)
    (δ : TermwiseSplitConnectingMap s)
    (δ' : TermwiseSplitConnectingMap s') :
    ∃ h : ∀ n : ℤ,
        (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₃ ⟶
          (S.map (HomologicalComplex.eval C (ComplexShape.down ℤ) n)).X₁,
      (∀ n, h n = termwiseSplittingDifference s s' n) ∧
        Nonempty (Homotopy δ.hom δ'.hom) := by
  sorry

theorem termwiseSplitConnectingMap_homotopy_components
    {S : ShortComplex (ChainComplex C ℤ)}
    (s s' : TermwiseSplitting S)
    (δ : TermwiseSplitConnectingMap s)
    (δ' : TermwiseSplitConnectingMap s') :
    ∃ h : Homotopy δ.hom δ'.hom,
      ∀ n : ℤ, h.hom n (n + 1) = termwiseSplittingDifferenceShift s s' n := by
  sorry

end ChainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

noncomputable def shift_zero :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (0 : ℤ) ≅ 𝟭 (CochainComplex C ℤ) :=
  CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ

noncomputable def shift_add (k l : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (k + l) ≅
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) k ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) l :=
  CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) k l

noncomputable def shift_comm (k l : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) k ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) l ≅
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) l ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) k :=
  CategoryTheory.shiftFunctorComm (CochainComplex C ℤ) k l

variable (C)

noncomputable def concentrated (A : C) (k : ℤ) [HasZeroObject C] : CochainComplex C ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj
    ((Formalization.Books.Homology.Unit13.cochainComplexSingle C).obj A)

variable {C}

theorem concentrated_at [HasZeroObject C] (A : C) (k : ℤ) :
    (concentrated C A k).X (-k) = A := by
  sorry

theorem concentrated_isZero [HasZeroObject C] (A : C) (k n : ℤ) (hn : n ≠ -k) :
    IsZero ((concentrated C A k).X n) := by
  sorry

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Cohomology shifts and homotopies for cochain complexes -/

/-- The canonical cohomology-shift comparison supplied by Mathlib's
`ShiftSequence` API, oriented as in the source. -/
noncomputable def cochainCohomologyShiftIso
    (K : CochainComplex C ℤ) (k i : ℤ) :
    K.homology (i + k) ≅
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).obj K |>.homology i :=
  (asIso (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
      k i (i + k) (by lia)).hom.app K)).symm

/-- Naturality of the canonical cohomology-shift comparison. -/
theorem cochainCohomologyShiftIso_natural
    {A B : CochainComplex C ℤ} (f : A ⟶ B) (k i : ℤ) :
    (cochainCohomologyShiftIso A k i).hom ≫
          HomologicalComplex.homologyMap
            ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) k).map f) i =
      HomologicalComplex.homologyMap f (i + k) ≫
        (cochainCohomologyShiftIso B k i).hom := by
  sorry

/-- The cohomology-shift comparisons are compatible with two successive
shifts and the canonical addition comparison of shift functors. -/
theorem cochainCohomologyShiftIso_coherent
    (K : CochainComplex C ℤ) (k l i : ℤ) :
    ∃ e' : K.homology (i + (k + l)) ≅
        (((CategoryTheory.shiftFunctor (CochainComplex C ℤ) k) ⋙
          CategoryTheory.shiftFunctor (CochainComplex C ℤ) l).obj K).homology i,
      (cochainCohomologyShiftIso K (k + l) i).hom ≫
          HomologicalComplex.homologyMap
            ((shift_add (C := C) k l).hom.app K) i = e'.hom := by
  sorry

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : CochainComplex C ℤ}

/-- A self-homotopy is parametrized by a map into the negative shifted target. -/
theorem cochain_homotopy_shift_self (a : A ⟶ B) :
    Nonempty (Homotopy a a ≃
      (A ⟶ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj B)) := by
  sorry

/-- For two cochain maps, the homotopy set is empty or a principal homogeneous
space under maps into the negative shifted target. -/
theorem cochain_homotopy_shift_principal (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (PrincipalHomogeneousSpace
        (A ⟶ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).obj B)
        (Homotopy a b)) := by
  sorry

/-! ## Termwise split short exact sequences of cochain complexes -/

/-- A degreewise family of splittings for a short complex of cochain
complexes. -/
def TermwiseSplitting (S : ShortComplex (CochainComplex C ℤ)) :=
  ∀ n : ℤ,
    (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting

/-- The degree `n` map `π^{n+1} d_B^n s^n` from the source. -/
def termwiseSplitConnectingFamily
    {S : ShortComplex (CochainComplex C ℤ)}
    (s : TermwiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ S.X₁.X (n + 1) :=
  (s n).s ≫ S.X₂.d n (n + 1) ≫ (s (n + 1)).r

/-- The cochain connecting family assembled into a map to the positive
shift. -/
structure TermwiseSplitConnectingMap
    {S : ShortComplex (CochainComplex C ℤ)} (s : TermwiseSplitting S) where
  hom : S.X₃ ⟶
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj S.X₁
  hom_f : ∀ n : ℤ, hom.f n = termwiseSplitConnectingFamily s n

theorem termwiseSplitConnectingMap_exists
    {S : ShortComplex (CochainComplex C ℤ)} (s : TermwiseSplitting S) :
    Nonempty (TermwiseSplitConnectingMap s) := by
  sorry

/-- The unique degreewise difference between two choices of section. -/
def termwiseSplittingDifference
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₃ ⟶
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₁ :=
  (s' n).s ≫ (s n).r

/-- A degreewise splitting difference, viewed in the component
`A[1]^{n-1}` used by a cochain homotopy. -/
def termwiseSplittingDifferenceShift
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶
      ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj S.X₁).X
        (n + (-1 : ℤ)) :=
  termwiseSplittingDifference s s' n ≫
    eqToHom (by
      change S.X₁.X n = S.X₁.X ((n + (-1 : ℤ)) + 1)
      congr 1
      lia)

theorem termwiseSplitting_section_eq
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    (s' n).s = (s n).s +
      termwiseSplittingDifference s s' n ≫
        (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).f := by
  sorry

theorem termwiseSplitting_projection_eq
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ) :
    (s' n).r = (s n).r +
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).g ≫
        (-(termwiseSplittingDifference s s' n)) := by
  sorry

theorem termwiseSplitting_difference_unique
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S) (n : ℤ)
    {h : (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₃ ⟶
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₁}
    (hh : (s' n).s = (s n).s + h ≫
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).f) :
    h = termwiseSplittingDifference s s' n := by
  sorry

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cochain connecting map obtained from a termwise splitting induces
the canonical long-exact-sequence connecting morphism. -/
theorem termwiseSplitConnectingMap_induces_connecting
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (s : TermwiseSplitting S) (δ : TermwiseSplitConnectingMap s) (i : ℤ) :
    ∃ e :
        ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj S.X₁).homology i ≅
          S.X₁.homology (i + 1),
      HomologicalComplex.homologyMap δ.hom i ≫ e.hom =
        Formalization.Books.Homology.Unit13.cochainConnectingMap hS i := by
  sorry

end CochainComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The change-of-splitting formula, including the induced homotopy between
the two assembled cochain connecting maps. -/
theorem termwiseSplitConnectingMap_homotopic
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S)
    (δ : TermwiseSplitConnectingMap s)
    (δ' : TermwiseSplitConnectingMap s') :
    ∃ h : ∀ n : ℤ,
        (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₃ ⟶
          (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).X₁,
      (∀ n, h n = termwiseSplittingDifference s s' n) ∧
        (∀ n,
          (s' n).r = (s n).r +
            (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).g ≫
              (-(h n))) ∧
        Nonempty (Homotopy δ'.hom δ.hom) := by
  sorry

/-- In the orientation matching the displayed formula in the source, the
change-of-splitting homotopy has the Mathlib component equation
`δ' = d h + h d + δ`. -/
theorem termwiseSplitConnectingMap_change_formula
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S)
    (δ : TermwiseSplitConnectingMap s)
    (δ' : TermwiseSplitConnectingMap s') :
    ∃ h : Homotopy δ'.hom δ.hom,
      ∀ n : ℤ,
        δ'.hom.f n =
          _root_.dNext n h.hom +
            _root_.prevD n h.hom + δ.hom.f n := by
  sorry

theorem termwiseSplitConnectingMap_homotopy_components
    {S : ShortComplex (CochainComplex C ℤ)}
    (s s' : TermwiseSplitting S)
    (δ : TermwiseSplitConnectingMap s)
    (δ' : TermwiseSplitConnectingMap s') :
    ∃ h : Homotopy δ'.hom δ.hom,
      ∀ n : ℤ,
        h.hom n (n + (-1 : ℤ)) =
          -(termwiseSplittingDifferenceShift s s' n) := by
  sorry

end CochainComplex

end Formalization.Books.Homology.Unit14
