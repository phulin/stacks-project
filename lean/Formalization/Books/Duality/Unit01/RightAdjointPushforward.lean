import Formalization.Books.Duality.Unit01.DualizingComplexesOnSchemes

/-!
# Right adjoint of pushforward

The source's `Rf_*`, its right adjoint, the sheafy trace map, and the global
derived-Hom comparison are represented by the categorical data in `Core`.
The examples are retained as precise preservation and non-preservation
interfaces rather than as prose-only counterexamples.
-/

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def PreservesCoherent {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, IsCoherent K → IsCoherent (a.rightAdjoint.obj K)

def PreservesBoundedAbove {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, IsBoundedAbove K → IsBoundedAbove (a.rightAdjoint.obj K)

def PreservesBoundedBelow {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, IsBoundedBelow K → IsBoundedBelow (a.rightAdjoint.obj K)

def SheafyTraceMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) (L : DerivedObject X) (K : DerivedObject Y) :=
  a.sheafyTrace L K

def equation_sheafy_trace {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) (L : DerivedObject X) (K : DerivedObject Y) :=
  SheafyTraceMap a L K

theorem lemma_twisted_inverse_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hqc : IsQuasiCompactMorphism f) (hqs : IsQuasiSeparatedMorphism f) :
    Nonempty (RightAdjointData f) := by
  sorry

theorem example_affine_twisted_inverse_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hqc : IsQuasiCompactMorphism f) (hqs : IsQuasiSeparatedMorphism f) :
    Nonempty (RightAdjointData f) := by
  exact lemma_twisted_inverse_image f hqc hqs

theorem example_does_not_preserve_coherent :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (a : RightAdjointData f),
      ¬ PreservesCoherent a := by
  sorry

theorem example_does_not_preserve_bounded_above :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (a : RightAdjointData f),
      ¬ PreservesBoundedAbove a := by
  sorry

theorem lemma_twisted_inverse_image_bounded_below {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (hqc : IsQuasiCompactMorphism f) (hqs : IsQuasiSeparatedMorphism f) :
    PreservesBoundedBelow a := by
  sorry

def SheafyTrace {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) (L : DerivedObject X) (K : DerivedObject Y) :=
  SheafyTraceMap a L K

structure Coherator (Y : Scheme.{u}) where
  functor : DerivedObject Y ⥤ DerivedObject Y

def CoherentifiedSheafyTrace {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) (Q : Coherator Y)
    (L : DerivedObject X) (K : DerivedObject Y) :=
  Q.functor.map (SheafyTraceMap a L K)

theorem lemma_iso_on_RSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (Q : Coherator Y) :
    ∀ (L : DerivedObject X) (K : DerivedObject Y),
      IsIso (CoherentifiedSheafyTrace a Q L K) := by
  sorry

theorem example_iso_on_RSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) :
    ∃ Q : Coherator Y, ∀ L K, IsIso (CoherentifiedSheafyTrace a Q L K) := by
  sorry

theorem remark_iso_on_RSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (L : DerivedObject X) (K : DerivedObject Y)
    (hL : IsQuasiCoherent (a.rightAdjoint.obj K)) :
    IsIso (SheafyTraceMap a L K) := by
  sorry

theorem example_iso_on_RSheafHom_noetherian {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (hf : IsProperMorphism f) (hX : IsNoetherianScheme X)
    (hY : IsNoetherianScheme Y) :
    ∀ L K, IsIso (SheafyTraceMap a L K) := by
  sorry

def GlobalHomAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) (L : DerivedObject X) (K : DerivedObject Y) : Prop :=
  Nonempty (((RPushforward f).obj L ⟶ K) ≃ (L ⟶ a.rightAdjoint.obj K))

theorem lemma_iso_global_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) :
    ∀ L K, GlobalHomAdjunction a L K := by
  sorry

end

end Formalization.Books.Duality.Unit01
