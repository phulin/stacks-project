import Formalization.Books.Duality.Unit06.BaseChangeII

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u v

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def TraceBaseChangeStatement {C : Type u}
    [Category C] {A B : C} (α β : A ⟶ B) : Prop :=
  α = β

theorem lemma_trace_map_and_base_change {C : Type u}
    [Category C] {A B : C} (α β : A ⟶ B)
    (hCartesian : Prop) (hTorIndependent : Prop) :
    TraceBaseChangeStatement α β := by
  sorry

theorem lemma_unit_and_base_change {C : Type u}
    [Category C] {A B : C} (α β : A ⟶ B)
    (hCartesian : Prop) (hTorIndependent : Prop) :
    TraceBaseChangeStatement α β := by
  sorry

def example_trace_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) :
    (RPushforward f).obj (a.rightAdjoint.obj K) ⟶ K :=
  Trace a K

end

end Formalization.Books.Duality.Unit01
