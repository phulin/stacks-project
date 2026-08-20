import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Torsor.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Deformation Theory, Chapter 8: Deformations of schemes

This file formalizes `books/defos.tex:2383-2450`.  The scheme-specific
interfaces retain Mathlib's scheme morphisms, closed immersions, module
pullback/pushforward functors, and short exact sequences.  The classification
and automorphism statements are theorem interfaces at this stage.
-/

namespace Formalization.Books.Defos.Unit08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/-! ## First-order thickenings of schemes -/

/-- A closed immersion of schemes whose defining ideal is square-zero. -/
structure FirstOrderThickening {S S' : Scheme.{u}} (i : S ⟶ S') : Prop where
  closedImmersion : IsClosedImmersion i
  square_zero : i.ker ^ 2 = ⊥

/-- The kernel module of the structure-sheaf map of a scheme morphism. -/
noncomputable abbrev thickeningKernelModule {S S' : Scheme.{u}} (i : S ⟶ S') : S'.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-- The conormal module `𝒞_{S/S'}` in the first-order case, obtained by
pulling the kernel module back to the closed subscheme. -/
noncomputable abbrev conormalModule {S S' : Scheme.{u}} (i : S ⟶ S') : S.Modules :=
  (Scheme.Modules.pullback i).obj (thickeningKernelModule i)

/-- A scheme-level presentation of the naive cotangent complex.  The two
terms are the conormal and differential modules in degrees `-1` and `0`.
The earlier sheaf-level construction is not definitionally an object of
`X.Modules`, so the conversion is retained as named chapter-facing data. -/
structure SchemeNaiveCotangentComplex {X S : Scheme.{u}} (f : X ⟶ S) where
  degreeNegOne : X.Modules
  degreeZero : X.Modules
  differential : degreeNegOne ⟶ degreeZero

/-- The chapter-facing data selecting the naive cotangent complex of `f`. -/
class SchemeNaiveCotangentComplexData {X S : Scheme.{u}} (f : X ⟶ S) where
  complex : SchemeNaiveCotangentComplex f

/-- The selected scheme-level naive cotangent complex. -/
noncomputable abbrev schemeNaiveCotangentComplex
    {X S : Scheme.{u}} (f : X ⟶ S)
    [h : SchemeNaiveCotangentComplexData f] : SchemeNaiveCotangentComplex f :=
  h.complex

/-- Ext groups from the naive cotangent complex to a coefficient module.
This is the scheme analogue of the project’s sheaf Ext theory interface. -/
class SchemeNaiveCotangentExtTheory (X : Scheme.{u}) where
  ext : ∀ {S : Scheme.{u}} (f : X ⟶ S),
    SchemeNaiveCotangentComplex f → X.Modules → ℕ → Type (u + 1)
  group : ∀ {S : Scheme.{u}} (f : X ⟶ S)
    (L : SchemeNaiveCotangentComplex f) (K : X.Modules) (n : ℕ),
    AddCommGroup (ext f L K n)

/-- The source notation `Extⁿ_{𝒪_X}(NL_{X/S}, K)`. -/
abbrev NaiveCotangentExtGroup {X S : Scheme.{u}}
    [SchemeNaiveCotangentExtTheory X] (f : X ⟶ S)
    (L : SchemeNaiveCotangentComplex f) (K : X.Modules) (n : ℕ) : Type (u + 1) :=
  SchemeNaiveCotangentExtTheory.ext f L K n

instance naiveCotangentExtGroup_addCommGroup
    {X S : Scheme.{u}} [h : SchemeNaiveCotangentExtTheory X]
    (f : X ⟶ S) (L : SchemeNaiveCotangentComplex f) (K : X.Modules) (n : ℕ) :
    AddCommGroup (NaiveCotangentExtGroup f L K n) :=
  h.group f L K n

/-! ## A flat deformation and its isomorphisms -/

/-- A flat deformation of `f : X ⟶ S` across `i : S ⟶ S'`, together with the
chosen identification of its special fibre with `X`. -/
structure SchemeDeformation {X S S' : Scheme.{u}}
    (i : S ⟶ S') (f : X ⟶ S) where
  total : Scheme
  lift : total ⟶ S'
  flat : Flat lift
  identification : X ≅ pullback lift i
  identification_over_base : identification.hom ≫ pullback.snd lift i = f

/-- The closed immersion of the special fibre into the total space supplied
by a deformation. -/
noncomputable abbrev SchemeDeformation.specialFiberInclusion
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (D : SchemeDeformation i f) : X ⟶ D.total :=
  D.identification.hom ≫ pullback.fst D.lift i

/-- An isomorphism of flat deformations preserving the base and the chosen
identification of the special fibre. -/
structure SchemeDeformationIso
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (D E : SchemeDeformation i f) where
  total : D.total ≅ E.total
  over_base : D.lift = total.hom ≫ E.lift
  special_fibre :
    D.identification.hom ≫ pullback.fst D.lift i ≫ total.hom =
      E.identification.hom ≫ pullback.fst E.lift i

/-- Isomorphism classes of pairs `(f' : X' ⟶ S', a)` from the source. -/
def schemeDeformationSetoid {X S S' : Scheme.{u}} (i : S ⟶ S') (f : X ⟶ S) :
    Setoid (SchemeDeformation i f) where
  r D E := Nonempty (SchemeDeformationIso D E)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro D
      exact ⟨{
        total := Iso.refl _
        over_base := by simp
        special_fibre := by simp
      }⟩
    · intro D E h
      rcases h with ⟨e⟩
      refine ⟨{
        total := e.total.symm
        over_base := ?_
        special_fibre := ?_
      }⟩
      · rw [e.over_base]
        simp
      · apply (cancel_mono e.total.hom).mp
        simp only [Iso.symm_hom, Category.assoc, e.total.inv_hom_id, Category.comp_id]
        exact (e.special_fibre).symm
    · intro D E F hDE hEF
      rcases hDE with ⟨e₁⟩
      rcases hEF with ⟨e₂⟩
      refine ⟨{
        total := e₁.total.trans e₂.total
        over_base := ?_
        special_fibre := ?_
      }⟩
      · rw [e₁.over_base, e₂.over_base]
        simp only [Iso.trans_hom, Category.assoc]
      · calc
          D.identification.hom ≫ pullback.fst D.lift i ≫
              (e₁.total.trans e₂.total).hom =
            (D.identification.hom ≫ pullback.fst D.lift i ≫ e₁.total.hom) ≫
              e₂.total.hom := by simp [Iso.trans_hom, Category.assoc]
          _ = (E.identification.hom ≫ pullback.fst E.lift i) ≫ e₂.total.hom := by
            rw [e₁.special_fibre]
          _ = F.identification.hom ≫ pullback.fst F.lift i := e₂.special_fibre

/-- The set of isomorphism classes of flat deformations. -/
abbrev SchemeDeformationClass {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S} :=
  Quotient (schemeDeformationSetoid i f)

/-- Automorphisms of a deformation over `S'` which restrict to the identity
on its special fibre. -/
structure SchemeDeformationAutomorphism
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (D : SchemeDeformation i f) where
  total : D.total ≅ D.total
  over_base : D.lift = total.hom ≫ D.lift
  special_fibre :
    D.identification.hom ≫ pullback.fst D.lift i ≫ total.hom =
      D.identification.hom ≫ pullback.fst D.lift i

/-! ## The exact diagram in the proof -/

/-- A short exact sequence with its three source-facing module objects fixed. -/
structure SchemeShortExact {Y : Scheme.{u}}
    (A B C : Y.Modules) where
  inclusion : A ⟶ B
  projection : B ⟶ C
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact

/-- The commutative diagram of short exact module sequences used in the
proof of the deformation lemma.  The vertical maps are expressed after
pushforward along the lifted morphism, so every displayed equality lives in
the single category `S'.Modules`. -/
structure SchemeDeformationExactDiagram
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (D : SchemeDeformation i f) where
  bottom : SchemeShortExact
    ((Scheme.Modules.pushforward i).obj (conormalModule i))
    (SheafOfModules.unit S'.ringCatSheaf)
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf))
  top : SchemeShortExact
    ((Scheme.Modules.pushforward D.specialFiberInclusion).obj
      ((Scheme.Modules.pullback f).obj (conormalModule i)))
    (SheafOfModules.unit D.total.ringCatSheaf)
    ((Scheme.Modules.pushforward D.specialFiberInclusion).obj
      (SheafOfModules.unit X.ringCatSheaf))
  left_map :
    ((Scheme.Modules.pushforward i).obj (conormalModule i)) ⟶
      (Scheme.Modules.pushforward D.lift).obj
        ((Scheme.Modules.pushforward D.specialFiberInclusion).obj
          ((Scheme.Modules.pullback f).obj (conormalModule i)))
  middle_map :
    (SheafOfModules.unit S'.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward D.lift).obj
        (SheafOfModules.unit D.total.ringCatSheaf)
  right_map :
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶
      (Scheme.Modules.pushforward D.lift).obj
        ((Scheme.Modules.pushforward D.specialFiberInclusion).obj
          (SheafOfModules.unit X.ringCatSheaf))
  left_commutes :
    bottom.inclusion ≫ middle_map =
      left_map ≫ (Scheme.Modules.pushforward D.lift).map top.inclusion
  right_commutes :
    bottom.projection ≫ right_map =
      middle_map ≫ (Scheme.Modules.pushforward D.lift).map top.projection

/-- The kernel of a first-order thickening is the ideal of the closed
subscheme, so the special fibre inclusion is a closed immersion. -/
theorem specialFiberInclusion_isClosedImmersion
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (hi : FirstOrderThickening i) (D : SchemeDeformation i f) :
    IsClosedImmersion D.specialFiberInclusion := by
  letI : IsClosedImmersion i := hi.closedImmersion
  infer_instance

/-- The exact diagram displayed in the source proof exists for every flat
deformation across a first-order thickening. -/
theorem exists_schemeDeformationExactDiagram
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    (hi : FirstOrderThickening i) (hf : Flat f)
    (D : SchemeDeformation i f) :
    Nonempty (SchemeDeformationExactDiagram D) := by
  sorry

/-! ## The deformation classification lemma -/

/-- Flat deformations of a flat morphism across a first-order thickening,
when one exists, form a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`. -/
theorem deformation_classes_is_principal_homogeneous
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    [SchemeNaiveCotangentComplexData f]
    [SchemeNaiveCotangentExtTheory X]
    (hi : FirstOrderThickening i) (hf : Flat f)
    (D : SchemeDeformation i f) :
    Nonempty (AddTorsor
      (NaiveCotangentExtGroup f (schemeNaiveCotangentComplex f)
        ((Scheme.Modules.pullback f).obj (conormalModule i)) 1)
      (SchemeDeformationClass (i := i) (f := f))) := by
  sorry

/-- Automorphisms of a chosen flat deformation over `S'` which reduce to the
identity on the special fibre form a principal homogeneous space under
`Ext⁰_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`. -/
theorem deformation_automorphisms_is_principal_homogeneous
    {X S S' : Scheme.{u}} {i : S ⟶ S'} {f : X ⟶ S}
    [SchemeNaiveCotangentComplexData f]
    [SchemeNaiveCotangentExtTheory X]
    (hi : FirstOrderThickening i) (hf : Flat f)
    (D : SchemeDeformation i f) :
    Nonempty (AddTorsor
      (NaiveCotangentExtGroup f (schemeNaiveCotangentComplex f)
        ((Scheme.Modules.pullback f).obj (conormalModule i)) 0)
      (SchemeDeformationAutomorphism D)) := by
  sorry

end

end Formalization.Books.Defos.Unit08
