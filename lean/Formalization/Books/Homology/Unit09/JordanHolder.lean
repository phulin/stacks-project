import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Noetherian
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
