import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Derived.Unit30.DerivingAdjoints
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.Derived.Unit34.DerivedLimits

/-!
# More on Algebra, Chapter 87: Rlim of abelian groups

This file records the definitions and theorem interfaces in the chapter.
The substantive proofs are intentionally deferred; definitions reuse the
canonical inverse-system, derived-limit, product, and pro-category APIs from
the preceding chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Algebra.Unit86
open Formalization.Books.Categories.Unit22
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit34
open Formalization.Books.Derived.Unit30
open Formalization.Books.Homology.Unit03
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit87

/-! ## 87.1. Computing `Rlim` -/

/-- Inverse systems of abelian groups indexed by the opposite of `ℕ`. -/
abbrev AbelianGroupInverseSystem := ℕᵒᵖ ⥤ AddCommGrpCat.{u}

/-- Set-valued inverse systems, for the set-valued part of the chaotic-site
identification in the source remark. -/
abbrev SetInverseSystem := ℕᵒᵖ ⥤ Type u

/-- Inverse systems of complexes of abelian groups. -/
abbrev ComplexInverseSystem := ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ

/-- Complexes whose terms are inverse systems of abelian groups. -/
abbrev ComplexOfInverseSystems := CochainComplex AbelianGroupInverseSystem ℤ

/-- The adjacent transition map in an inverse system of abelian groups. -/
def abelianGroupTransition (A : AbelianGroupInverseSystem.{u}) (n : ℕ) :
    A.obj (Opposite.op (n + 1)) ⟶ A.obj (Opposite.op n) :=
  A.map (opHomOfLE (Nat.le_succ n))

@[simp]
theorem abelianGroupTransition_zero (A : AbelianGroupInverseSystem.{u}) (n : ℕ) :
    abelianGroupTransition A n = A.map (opHomOfLE (Nat.le_succ n)) := rfl

/-- The source's Mittag--Leffler condition, on the underlying inverse system
of types. -/
abbrev IsMittagLefflerSystem (A : AbelianGroupInverseSystem.{u}) : Prop :=
  (A ⋙ CategoryTheory.forget (AddCommGrpCat.{u})).IsMittagLeffler

/-- The constant countable direct-sum system used in Emmanouil's criterion. -/
noncomputable def countableDirectSumSystem (A : AbelianGroupInverseSystem.{u}) :
    AbelianGroupInverseSystem.{u} :=
  ∐ fun _ : ℕ => A

/-- The inverse-limit functor on inverse systems of abelian groups. -/
noncomputable abbrev inverseLimitFunctor :
    AbelianGroupInverseSystem.{u} ⥤ AddCommGrpCat.{u} :=
  (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})

/-- The `p`-th right-derived functor of inverse limit. -/
noncomputable abbrev derivedLimitFunctor (p : ℕ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    AbelianGroupInverseSystem.{u} ⥤ AddCommGrpCat.{u} :=
  (inverseLimitFunctor.{u}).rightDerived p

/-- The `p`-th derived limit of an inverse system. -/
noncomputable abbrev derivedLimitGroup (A : AbelianGroupInverseSystem.{u}) (p : ℕ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : AddCommGrpCat.{u} :=
  (derivedLimitFunctor p).obj A

/-- The first derived limit. -/
noncomputable abbrev firstDerivedLimitGroup (A : AbelianGroupInverseSystem.{u})
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : AddCommGrpCat.{u} :=
  derivedLimitGroup A 1

/-- Right acyclicity for inverse limit means vanishing of all positive derived
limits. -/
def IsRightAcyclicForLimit (A : AbelianGroupInverseSystem.{u})
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (derivedLimitGroup A p)

/-- A source-facing name for first-derived-limit vanishing. -/
abbrev FirstDerivedLimitVanishing (A : AbelianGroupInverseSystem.{u})
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : Prop :=
  IsZero (firstDerivedLimitGroup A)

/-- Functoriality of derived limits. -/
noncomputable def derivedLimitMap {A B : AbelianGroupInverseSystem.{u}} (p : ℕ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (f : A ⟶ B) : derivedLimitGroup A p ⟶ derivedLimitGroup B p :=
  (derivedLimitFunctor p).map f

/-- Functoriality of ordinary inverse limits. -/
noncomputable def inverseLimitMap {A B : AbelianGroupInverseSystem.{u}}
    [HasLimit A] [HasLimit B] (f : A ⟶ B) : limit A ⟶ limit B :=
  limMap f

/-- The map `1 - f` on the product of an inverse system. -/
noncomputable def inverseLimitDifferenceMap (A : AbelianGroupInverseSystem.{u})
    [HasProduct (fun n : ℕ => A.obj (Opposite.op n))] :
    (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) ⟶
      (∏ᶜ fun n : ℕ => A.obj (Opposite.op n)) :=
  Pi.lift (fun n =>
    Pi.π (fun n : ℕ => A.obj (Opposite.op n)) n -
      Pi.π (fun n : ℕ => A.obj (Opposite.op n)) (n + 1) ≫
        abelianGroupTransition A n)

/-- The derived limit object attached to a derived inverse system. -/
noncomputable def Rlim
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    DerivedCategory (AddCommGrpCat.{u}) :=
  derivedLimit F (exists_isDerivedLimit F)

theorem exists_Rlim
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    ∃ K : DerivedCategory (AddCommGrpCat.{u}), IsDerivedLimit F K := by
  exact exists_isDerivedLimit F

theorem Rlim_isDerivedLimit
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    IsDerivedLimit F (Rlim F) := by
  exact derivedLimit_isDerivedLimit F (exists_isDerivedLimit F)

/-- The inverse system obtained by viewing abelian groups as complexes in
degree zero. -/
abbrev derivedAbelianGroupSystem (A : AbelianGroupInverseSystem.{u})
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})] :
    DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})) :=
  A ⋙ DerivedCategory.singleFunctor (AddCommGrpCat.{u}) 0

/-- The unbounded right-derived functor of inverse limit on the derived
category of inverse systems. -/
theorem exists_Rlim_rightDerivedFunctor
    [HasDerivedCategory.{w} (AbelianGroupInverseSystem.{u})]
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})] :
    ∃ RF : DerivedCategory (AbelianGroupInverseSystem.{u}) ⥤
        DerivedCategory (AddCommGrpCat.{u}),
      IsUnboundedRightDerivedFunctor (inverseLimitFunctor.{u}) RF := by
  sorry

/-- The notation `R^p lim K` is the `p`-th derived-category cohomology of
the chosen derived inverse-limit functor. -/
noncomputable abbrev RlimCohomology
    [HasDerivedCategory.{w} (AbelianGroupInverseSystem.{u})]
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (RF : DerivedCategory (AbelianGroupInverseSystem.{u}) ⥤
      DerivedCategory (AddCommGrpCat.{u}))
    (K : DerivedCategory (AbelianGroupInverseSystem.{u})) (p : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat p).obj (RF.obj K)

/-- A complex is a two-term presentation of the standard `Rlim` complex when
it is supported in degrees zero and one and its differential is `1 - f`. -/
def IsTwoTermRlimRepresentation (A : AbelianGroupInverseSystem.{u})
    (K : CochainComplex AddCommGrpCat.{u} ℤ)
    [HasProduct (fun n : ℕ => A.obj (Opposite.op n))] : Prop :=
  (∀ p : ℤ, p ≠ 0 → p ≠ 1 → IsZero (K.X p)) ∧
    ∃ (e₀ : K.X 0 ≅ ∏ᶜ fun n : ℕ => A.obj (Opposite.op n))
      (e₁ : K.X 1 ≅ ∏ᶜ fun n : ℕ => A.obj (Opposite.op n)),
      K.d 0 1 ≫ e₁.hom = e₀.hom ≫ inverseLimitDifferenceMap A

/-- Higher derived limits of a sequential inverse system vanish. -/
theorem Rlim_higher_vanishes (A : AbelianGroupInverseSystem.{u}) (p : ℕ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (hp : 1 < p) : IsZero (derivedLimitGroup A p) := by
  sorry

/-- A Mittag--Leffler system is right acyclic for inverse limit. -/
theorem Rlim_MittagLeffler_is_rightAcyclic (A : AbelianGroupInverseSystem.{u})
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (hA : IsMittagLefflerSystem A) : IsRightAcyclicForLimit A := by
  sorry

/-- The standard two-term complex represents the derived inverse limit. -/
theorem Rlim_two_term_representation (A : AbelianGroupInverseSystem.{u})
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    [HasProduct (fun n : ℕ => A.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ => (derivedAbelianGroupSystem A).obj (Opposite.op n))] :
    ∃ K : CochainComplex AddCommGrpCat.{u} ℤ,
      IsTwoTermRlimRepresentation A K ∧
        Nonempty
          ((DerivedCategory.Q : CochainComplex AddCommGrpCat.{u} ℤ ⥤
              DerivedCategory (AddCommGrpCat.{u})).obj K ≅
            Rlim (derivedAbelianGroupSystem A)) := by
  sorry

/-- Every derived object of the inverse-system category has a representative
whose terms are right acyclic for inverse limit. -/
theorem exists_rightAcyclic_representative
    [HasDerivedCategory.{w} (AbelianGroupInverseSystem.{u})]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (K : DerivedCategory (AbelianGroupInverseSystem.{u})) :
    ∃ L : ComplexOfInverseSystems.{u},
      Nonempty
        (K ≅
          (DerivedCategory.Q : ComplexOfInverseSystems.{u} ⥤
            DerivedCategory (AbelianGroupInverseSystem.{u})).obj L) ∧
        ∀ p : ℤ, IsRightAcyclicForLimit (L.X p) := by
  sorry

/-- The inverse system of terms in a fixed degree. -/
noncomputable def complexSystemDegree (K : ComplexInverseSystem.{u}) (p : ℤ) :
    AbelianGroupInverseSystem.{u} :=
  K ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) p

/-- The inverse system of cohomology groups in a fixed degree. -/
noncomputable def cohomologySystem (K : ComplexInverseSystem.{u}) (p : ℤ) :
    AbelianGroupInverseSystem.{u} :=
  K ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) p

/-- If all terms are right acyclic, the termwise inverse-limit complex computes
the derived limit. -/
theorem Rlim_of_rightAcyclic_terms
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (K : ComplexInverseSystem.{u}) [HasLimit K]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (_hK : ∀ p : ℤ, IsRightAcyclicForLimit (complexSystemDegree K p)) :
    IsDerivedLimit (derivedComplexInverseSystem K)
      ((DerivedCategory.Q : CochainComplex AddCommGrpCat.{u} ℤ ⥤
          DerivedCategory (AddCommGrpCat.{u})).obj
        (termwiseInverseLimitComplex K)) := by
  exact termwiseInverseLimit_isDerivedLimit K

/-! ## 87.2. Exact sequences and pro-isomorphisms -/

/-- A seven-arrow composable sequence, used for the seven terms in the
long exact sequence of inverse limits. -/
def sevenTermSequence
    {C : Type u} [Category.{v} C]
    (G₀ G₁ G₂ G₃ G₄ G₅ G₆ G₇ : C)
    (d₀ : G₀ ⟶ G₁) (d₁ : G₁ ⟶ G₂) (d₂ : G₂ ⟶ G₃)
    (d₃ : G₃ ⟶ G₄) (d₄ : G₄ ⟶ G₅) (d₅ : G₅ ⟶ G₆)
    (d₆ : G₆ ⟶ G₇) : ComposableArrows C 7 :=
  ((ComposableArrows.mk₅ d₂ d₃ d₄ d₅ d₆).precomp d₁).precomp d₀

/-- The seven-term sequence in the source's six-term exact sequence. -/
noncomputable def RlimSixTermSequence (S : ShortComplex (AbelianGroupInverseSystem.{u}))
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (δ₁ : limit S.X₃ ⟶ firstDerivedLimitGroup S.X₁)
    (δ₂ : firstDerivedLimitGroup S.X₁ ⟶ firstDerivedLimitGroup S.X₂)
    (δ₃ : firstDerivedLimitGroup S.X₂ ⟶ firstDerivedLimitGroup S.X₃) :
    ComposableArrows AddCommGrpCat.{u} 7 :=
  sevenTermSequence
    (0 : AddCommGrpCat.{u}) (limit S.X₁) (limit S.X₂) (limit S.X₃)
    (firstDerivedLimitGroup S.X₁) (firstDerivedLimitGroup S.X₂)
    (firstDerivedLimitGroup S.X₃) (0 : AddCommGrpCat.{u})
    (0 : (0 : AddCommGrpCat.{u}) ⟶ limit S.X₁)
    (limMap S.f) (limMap S.g) δ₁ δ₂ δ₃
    (0 : firstDerivedLimitGroup S.X₃ ⟶ (0 : AddCommGrpCat.{u}))

/-- A pointwise short exact inverse system gives the six-term exact sequence
for `lim` and `R¹lim`. -/
theorem six_term_Rlim_exact
    (S : ShortComplex (AbelianGroupInverseSystem.{u}))
    (hS : IsPointwiseShortExact S)
    [HasLimit S.X₁] [HasLimit S.X₂] [HasLimit S.X₃]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    ∃ (δ₁ : limit S.X₃ ⟶ firstDerivedLimitGroup S.X₁)
      (δ₂ : firstDerivedLimitGroup S.X₁ ⟶ firstDerivedLimitGroup S.X₂)
      (δ₃ : firstDerivedLimitGroup S.X₂ ⟶ firstDerivedLimitGroup S.X₃),
      (RlimSixTermSequence S δ₁ δ₂ δ₃).Exact := by
  sorry

/-- The finite-window comparison used to compute cohomology of a termwise
inverse-limit complex. -/
theorem apply_MittagLeffler_again
    (K : ComplexInverseSystem.{u}) [HasLimit K]
    (hwindow : ∀ (n : ℕ) (p : ℤ), (p < -2 ∨ 1 < p) →
      IsZero ((K.obj (Opposite.op n)).X p))
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (hA_neg2 : FirstDerivedLimitVanishing (complexSystemDegree K (-2)))
    (hA_neg1 : FirstDerivedLimitVanishing (complexSystemDegree K (-1)))
    (hH_neg1 : FirstDerivedLimitVanishing (cohomologySystem K (-1))) :
    Nonempty
      ((termwiseInverseLimitComplex K).homology 0 ≅
        limit (cohomologySystem K 0)) := by
  sorry

/-- Isomorphism of the pro-objects represented by two inverse systems. -/
noncomputable abbrev natProObject
    {C : Type u} [Category.{v} C] (F : ℕᵒᵖ ⥤ C) : ProCategory C :=
  (proLim (AsSmall.{v} (ℕᵒᵖ))).obj
    (CategoryTheory.AsSmall.down ⋙ F)

def IsProIsomorphism
    {C : Type u} [Category.{v} C]
    (F G : ℕᵒᵖ ⥤ C) : Prop :=
  Nonempty (natProObject F ≅ natProObject G)

/-- A pro-isomorphism induces isomorphisms on ordinary and first derived
inverse limits. -/
theorem pro_isomorphism_derived_limit_maps
    (A B : AbelianGroupInverseSystem.{u})
    [HasLimit A] [HasLimit B]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})]
    (hAB : IsProIsomorphism A B) :
    Nonempty (limit A ≅ limit B) ∧
      Nonempty (firstDerivedLimitGroup A ≅ firstDerivedLimitGroup B) := by
  sorry

/-! ## 87.3. Hom sequences and the derived-limit triangle -/

/-- The exact sequence for maps into a derived limit, re-exported with the
chapter's terminology. -/
theorem map_into_Rlim_exact
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {F : DerivedInverseSystem C} {K L : C}
    (p : DerivedLimitPresentation F K)
    [HasInjectiveResolutions (DerivedInverseSystem (AddCommGrpCat.{v}))] :
    ∃ α : firstDerivedLimitInto (shiftedInverseSystem F (-1 : ℤ)) L ⟶
        (preadditiveCoyoneda.obj (Opposite.op L)).obj K,
      ∃ β : (preadditiveCoyoneda.obj (Opposite.op L)).obj K ⟶
        (lim : DerivedInverseSystem (AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).obj
          (homInverseSystemInto F L),
      (ComposableArrows.mk₄
          (0 : (0 : AddCommGrpCat.{v}) ⟶
            firstDerivedLimitInto (shiftedInverseSystem F (-1 : ℤ)) L)
          α β
          (0 : (lim : DerivedInverseSystem (AddCommGrpCat.{v}) ⥤
            AddCommGrpCat.{v}).obj (homInverseSystemInto F L) ⟶
            (0 : AddCommGrpCat.{v}))).Exact := by
  exact hom_into_derivedLimit_exact p

/-- A pro-isomorphism of inverse systems in a triangulated category induces a
noncanonical isomorphism between any two chosen derived limits. -/
theorem pro_isomorphism_Rlim
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {F G : DerivedInverseSystem C} {K L : C}
    (hK : IsDerivedLimit F K) (hL : IsDerivedLimit G L)
    (hFG : IsProIsomorphism F G) : Nonempty (K ≅ L) := by
  sorry

/-- The dual exact sequence for maps out of a homotopy colimit. -/
theorem map_from_hocolim_exact
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {F : SequentialSystem C} {K L : C}
    [HasCoproduct (fun n : ℕ => F.obj n)]
    (p : DerivedColimitPresentation F K)
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] :
    ∃ α : firstDerivedLimit
      (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
        (inferInstance : Preadditive C) F (L⟦(-1 : ℤ)⟧)) ⟶
        (preadditiveCoyoneda.obj (Opposite.op K)).obj L,
      ∃ β : (preadditiveCoyoneda.obj (Opposite.op K)).obj L ⟶
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).obj
          (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
            (inferInstance : Preadditive C) F L),
      (ComposableArrows.mk₄
          (0 : (0 : AddCommGrpCat.{v}) ⟶
            firstDerivedLimit
              (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
                (inferInstance : Preadditive C) F (L⟦(-1 : ℤ)⟧)))
          α β
          (0 : (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤
            AddCommGrpCat.{v}).obj
              (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
                (inferInstance : Preadditive C) F L) ⟶
            (0 : AddCommGrpCat.{v}))).Exact := by
  exact hom_from_homotopyColimit_exact p

/-- A presentation of `Rlim` is precisely the canonical distinguished
triangle `Rlim → ∏ Kₙ → ∏ Kₙ → Rlim[1]`. -/
noncomputable def RlimPresentation
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    DerivedLimitPresentation F (Rlim F) :=
  Classical.choice (Rlim_isDerivedLimit F)

theorem Rlim_distinguished_triangle
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    Triangle.mk (RlimPresentation F).inclusion
        (inverseSystemDifferenceMap F (RlimPresentation F).product)
        (RlimPresentation F).connecting ∈
      distTriang (DerivedCategory (AddCommGrpCat.{u})) := by
  exact (RlimPresentation F).distinguished

/-- The natural-number inverse-system category is the category of sheaves on
the natural numbers with the chaotic topology, in the source's
identification. -/
abbrev naturalNumberChaoticSheafCategory := AbelianGroupInverseSystem.{u}

/-- Global sections in the preceding sheaf identification are inverse limit. -/
noncomputable abbrev naturalNumberChaoticSetGlobalSections :
    SetInverseSystem.{u} ⥤ Type u :=
  (lim : (ℕᵒᵖ ⥤ Type u) ⥤ Type u)

/-- The abelian-group global-sections functor in that identification is
inverse limit. -/
noncomputable abbrev naturalNumberChaoticGlobalSections :
    naturalNumberChaoticSheafCategory.{u} ⥤ AddCommGrpCat.{u} :=
  inverseLimitFunctor.{u}

/-- Its higher cohomology is the right-derived inverse-limit functor. -/
noncomputable abbrev naturalNumberChaoticCohomology (p : ℕ)
    [HasInjectiveResolutions (naturalNumberChaoticSheafCategory.{u})] :
    naturalNumberChaoticSheafCategory.{u} ⥤ AddCommGrpCat.{u} :=
  derivedLimitFunctor p

theorem naturalNumberChaotic_globalSections_eq_limit :
    naturalNumberChaoticGlobalSections.{u} = inverseLimitFunctor.{u} := rfl

theorem naturalNumberChaotic_cohomology_eq_derivedLimit (p : ℕ)
    [HasInjectiveResolutions (naturalNumberChaoticSheafCategory.{u})] :
    naturalNumberChaoticCohomology p = derivedLimitFunctor p := rfl

/-! ## 87.4. Cohomology of derived limits -/

/-- The short exact cohomology window attached to a derived limit. -/
def RlimCohomologyExactSequence
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (K : ComplexInverseSystem.{u}) (L : DerivedCategory (AddCommGrpCat.{u}))
    (p : ℤ) (_hL : IsDerivedLimit (derivedComplexInverseSystem K) L)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : Prop :=
  ∃ α : firstDerivedLimitGroup (cohomologySystem K (p - 1)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat p).obj L,
    ∃ β : (DerivedCategory.homologyFunctor AddCommGrpCat p).obj L ⟶
      limit (cohomologySystem K p),
    (ComposableArrows.mk₄
        (0 : (0 : AddCommGrpCat.{u}) ⟶
          firstDerivedLimitGroup (cohomologySystem K (p - 1)))
        α β
        (0 : limit (cohomologySystem K p) ⟶ (0 : AddCommGrpCat.{u}))).Exact

/-- The cohomology short exact sequence for the derived limit of a system of
complexes. -/
theorem break_long_exact_sequence
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (K : ComplexInverseSystem.{u}) [HasLimit K]
    (L : DerivedCategory (AddCommGrpCat.{u}))
    (hL : IsDerivedLimit (derivedComplexInverseSystem K) L)
    (p : ℤ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    RlimCohomologyExactSequence K L p hL := by
  sorry

/-! ## 87.5. Lifting inverse systems of derived objects -/

/-- A compatible lift of an inverse system of derived objects to complexes. -/
structure DerivedSystemComplexLift
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))) where
  M : ComplexInverseSystem.{u}
  stageIso : ∀ n : ℕ,
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u} ℤ ⥤
      DerivedCategory (AddCommGrpCat.{u})).obj (M.obj (Opposite.op n)) ≅
      F.obj (Opposite.op n)
  compatible : ∀ n : ℕ,
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u} ℤ ⥤
      DerivedCategory (AddCommGrpCat.{u})).map
        (M.map (opHomOfLE (Nat.le_succ n))) ≫ (stageIso n).hom =
      (stageIso (n + 1)).hom ≫ F.map (opHomOfLE (Nat.le_succ n))

/-- Every inverse system of derived abelian groups admits a compatible lift to
an inverse system of complexes. -/
theorem exists_derivedSystemComplexLift
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))) :
    Nonempty (DerivedSystemComplexLift F) := by
  sorry

/-- The derived limit is independent of the chosen compatible lift. -/
theorem derived_limit_of_system_complex_lift
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    {F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))}
    {L : DerivedCategory (AddCommGrpCat.{u})}
    (hL : IsDerivedLimit F L) (M : DerivedSystemComplexLift F)
    [HasProduct (fun n : ℕ =>
      (derivedComplexInverseSystem M.M).obj (Opposite.op n))] :
    Nonempty (L ≅ Rlim (derivedComplexInverseSystem M.M)) := by
  sorry

/-- The cohomology inverse system of a system of derived objects. -/
noncomputable def derivedObjectCohomologySystem
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))) (p : ℤ) :
    AbelianGroupInverseSystem.{u} :=
  F ⋙ DerivedCategory.homologyFunctor AddCommGrpCat p

/-- The canonical cohomology short exact sequence for any derived inverse
system, after choosing a compatible complex lift. -/
def DerivedObjectRlimCohomologyExactSequence
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    (L : DerivedCategory (AddCommGrpCat.{u}))
    (_hL : IsDerivedLimit F L) (p : ℤ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] : Prop :=
  ∃ α : firstDerivedLimitGroup (derivedObjectCohomologySystem F (p - 1)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat p).obj L,
    ∃ β : (DerivedCategory.homologyFunctor AddCommGrpCat p).obj L ⟶
      limit (derivedObjectCohomologySystem F p),
    (ComposableArrows.mk₄
        (0 : (0 : AddCommGrpCat.{u}) ⟶
          firstDerivedLimitGroup (derivedObjectCohomologySystem F (p - 1)))
        α β
        (0 : limit (derivedObjectCohomologySystem F p) ⟶
          (0 : AddCommGrpCat.{u}))).Exact

theorem derived_limit_cohomology_exact_sequence
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    (F : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u})))
    (L : DerivedCategory (AddCommGrpCat.{u}))
    (_hL : IsDerivedLimit F L) (M : DerivedSystemComplexLift F) (p : ℤ)
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    DerivedObjectRlimCohomologyExactSequence F L _hL p := by
  sorry

/-! ## 87.6. Mittag--Leffler criteria -/

/-- A pro-isomorphic derived inverse system has isomorphic derived limits. -/
theorem Rlim_pro_equal
    [HasDerivedCategory.{w} (AddCommGrpCat.{u})]
    {E D : DerivedInverseSystem (DerivedCategory (AddCommGrpCat.{u}))}
    [HasProduct (fun n : ℕ => E.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ => D.obj (Opposite.op n))]
    (hED : IsProIsomorphism E D) :
    Nonempty (Rlim E ≅ Rlim D) := by
  sorry

/-- Emmanouil's characterization of the Mittag--Leffler condition. -/
theorem emmanouil (A : AbelianGroupInverseSystem.{u})
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    IsMittagLefflerSystem A ↔
      IsZero (firstDerivedLimitGroup A) ∧
        IsZero (firstDerivedLimitGroup (countableDirectSumSystem A)) := by
  sorry

/-- In a pointwise short exact inverse system, Mittag--Leffler ends imply a
Mittag--Leffler middle term. -/
theorem mittagLeffler_of_shortExact
    (S : ShortComplex (AbelianGroupInverseSystem.{u}))
    (hS : IsPointwiseShortExact S)
    (h₁ : IsMittagLefflerSystem S.X₁)
    (h₃ : IsMittagLefflerSystem S.X₃) :
    IsMittagLefflerSystem S.X₂ := by
  sorry

/-- The zero pro-object condition for an inverse system. -/
def IsZeroProSystem (A : AbelianGroupInverseSystem.{u}) : Prop :=
  IsZero (natProObject A)

/-- A countable inverse system is zero as a pro-object exactly when the
ordinary and first derived limits of it and its countable direct sum vanish. -/
theorem pro_zero_iff_Rlim_zero (A : AbelianGroupInverseSystem.{u})
    [HasLimit A] [HasLimit (countableDirectSumSystem A)]
    [HasInjectiveResolutions (AbelianGroupInverseSystem.{u})] :
    IsZeroProSystem A ↔
      IsZero (limit A) ∧ IsZero (firstDerivedLimitGroup A) ∧
        IsZero (limit (countableDirectSumSystem A)) ∧
          IsZero (firstDerivedLimitGroup (countableDirectSumSystem A)) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit87
