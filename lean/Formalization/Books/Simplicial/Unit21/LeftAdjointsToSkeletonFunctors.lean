import Formalization.Books.Simplicial.Unit14.HomFromSimplicialSetsIntoCosimplicialObjects
import Formalization.Books.Simplicial.Unit18.SplittingSimplicialObjects
import Formalization.Books.Simplicial.Unit19.CoskeletonFunctors
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Simplicial Methods, Chapter 21: Left adjoints to the skeleton functors

The source's `iₙ!` is Mathlib's left Kan extension along the inclusion of the
truncated simplex category.  The declarations below retain the source's
pointwise colimit indexing, while using `CostructuredArrow`, `SSet.boundary`,
and the earlier skeleton and degreewise-coproduct interfaces.
-/

namespace Formalization.Books.Simplicial.Unit21

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u w

/-! ## The left Kan extension and its indexing category -/

/-- The inclusion used for the left Kan extension defining `iₘ!`. -/
abbrev leftSkeletonInclusion (m : ℕ) :
    (SimplexCategory.Truncated m)ᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  (SimplexCategory.Truncated.inclusion m).op

/-- Existence of the left Kan extension for every `m`-truncated object. -/
abbrev HasLeftSkeletonFunctor
    (C : Type u) [Category.{v} C] (m : ℕ) : Prop :=
  ∀ U : SimplicialObject.Truncated C m,
    (leftSkeletonInclusion m).HasLeftKanExtension U

private noncomputable instance leftSkeletonIndexFinCategory (m : ℕ) (X : SimplexCategoryᵒᵖ) :
    FinCategory (CostructuredArrow (leftSkeletonInclusion m) X) := by
  letI : Finite (SimplexCategory.Truncated m) := by
    let f : SimplexCategory.Truncated m → Fin (m + 1) :=
      fun X => ⟨X.obj.len, Nat.lt_succ_of_le X.property⟩
    apply Finite.of_injective f
    intro X Y h
    cases X with
    | mk X hX =>
      cases Y with
      | mk Y hY =>
        apply ObjectProperty.FullSubcategory.ext
        exact SimplexCategory.ext (congrArg Fin.val h)
  letI : Finite ((SimplexCategory.Truncated m)ᵒᵖ) := by
    apply Finite.of_injective (fun X => X.unop)
    intro X Y h
    exact congrArg op h
  letI : ∀ a b : (SimplexCategory.Truncated m)ᵒᵖ, Finite (a ⟶ b) := fun a b => by
    apply Finite.of_injective (fun f => f.unop.hom)
    intro f g h
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact h
  letI : ∀ a : (SimplexCategory.Truncated m)ᵒᵖ,
      Finite ((leftSkeletonInclusion m).obj a ⟶ X) := fun a => by
    apply Finite.of_injective (fun f => f.unop)
    intro f g h
    exact Quiver.Hom.unop_inj h
  letI : Finite (CostructuredArrow (leftSkeletonInclusion m) X) := by
    let f : CostructuredArrow (leftSkeletonInclusion m) X →
        Σ a : (SimplexCategory.Truncated m)ᵒᵖ,
          (leftSkeletonInclusion m).obj a ⟶ X :=
      fun A => ⟨A.left, A.hom⟩
    apply Finite.of_injective f
    intro X Y h
    apply Comma.ext
    · exact congrArg Sigma.fst h
    · exact Subsingleton.elim _ _
    · cases X
      cases Y
      cases h
      rfl
  letI : ∀ a b : CostructuredArrow (leftSkeletonInclusion m) X, Finite (a ⟶ b) := fun a b => by
    apply Finite.of_injective (fun f => f.left)
    intro f g h
    apply CommaMorphism.ext
    · exact h
    · exact Subsingleton.elim _ _
  exact { fintypeObj := Fintype.ofFinite _, fintypeHom := fun a b => Fintype.ofFinite _ }

private noncomputable instance hasPointwiseLeftSkeleton
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) :
    Functor.HasPointwiseLeftKanExtension (leftSkeletonInclusion m) U := fun X => by
  infer_instance

/-- Finite colimits provide the left adjoint required in this chapter. -/
theorem has_left_skeleton_functor_of_has_finite_colimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    HasLeftSkeletonFunctor C m := by
  intro U
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (leftSkeletonInclusion m) U)

/-- The source's left adjoint `iₘ!`, implemented by Mathlib's `lan`. -/
noncomputable def leftAdjoint
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    SimplicialObject.Truncated C m ⥤ SimplicialObject C :=
  let hsk : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  letI : HasLeftSkeletonFunctor C m := hsk
  SimplicialObject.Truncated.sk m

/-- The adjunction `iₘ! ⊣ skₘ`, using the canonical Kan-extension adjunction. -/
noncomputable def leftAdjunction
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    leftAdjoint (C := C) m ⊣ SimplicialObject.truncation m :=
  letI : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  Functor.lanAdjunction (leftSkeletonInclusion m) C

/-- The source's mapping-property equivalence for `iₘ!`. -/
noncomputable def leftAdjointHomEquiv
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) (V : SimplicialObject C) :
    ((leftAdjoint m).obj U ⟶ V) ≃
      (U ⟶ (SimplicialObject.truncation m).obj V) :=
  (leftAdjunction m).homEquiv U V

/-- The unit map `U → skₘ(iₘ!U)`. -/
noncomputable def leftAdjointUnit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (U : SimplicialObject.Truncated C m) :
    U ⟶ (SimplicialObject.truncation m).obj ((leftAdjoint m).obj U) :=
  (leftAdjunction m).unit.app U

/-- The counit map `iₘ!(skₘV) → V`. -/
noncomputable def leftAdjointCounit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (V : SimplicialObject C) :
    (leftAdjoint m).obj ((SimplicialObject.truncation m).obj V) ⟶ V :=
  (leftAdjunction m).counit.app V

/-- The source's indexing category for the degree-`n` colimit. -/
abbrev leftSkeletonIndex (m n : ℕ) :=
  CostructuredArrow (leftSkeletonInclusion m)
    (op (SimplexCategory.mk n))

/-- The diagram `U(n)` whose colimit gives the degree-`n` value of `iₘ!U`. -/
def leftSkeletonDiagram
    {C : Type u} [Category.{v} C] (m n : ℕ)
    (U : SimplicialObject.Truncated C m) : leftSkeletonIndex m n ⥤ C :=
  CostructuredArrow.proj (leftSkeletonInclusion m)
    (op (SimplexCategory.mk n)) ⋙ U

/-- The functorial map of indexing categories induced by a simplex map. -/
def leftSkeletonIndexMap
    {m n n' : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    leftSkeletonIndex m n' ⥤ leftSkeletonIndex m n :=
  CostructuredArrow.map φ.op

/-- Precomposition by `φ̲` gives the source's equality of diagrams. -/
theorem leftSkeletonDiagram_map
    {C : Type u} [Category.{v} C]
    {m n n' : ℕ} (U : SimplicialObject.Truncated C m)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    leftSkeletonIndexMap φ ⋙ leftSkeletonDiagram m n U =
      leftSkeletonDiagram m n' U := by
  rfl

/-- The colimit in the source's pointwise formula. -/
noncomputable def leftSkeletonColimit
    {C : Type u} [Category.{v} C] (m n : ℕ)
    (U : SimplicialObject.Truncated C m)
    (h : HasColimit (leftSkeletonDiagram m n U)) : C :=
  letI := h
  colimit (leftSkeletonDiagram m n U)

/-- Finite colimits supply each pointwise colimit in the displayed formula. -/
theorem has_left_skeleton_colimit_of_has_finite_colimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) :
    HasColimit (leftSkeletonDiagram m n U) := by
  infer_instance

/-- The left Kan extension has the source's pointwise colimit description. -/
theorem leftAdjoint_obj_iso_colimit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m)
    (h : HasColimit (leftSkeletonDiagram m n U)) :
    Nonempty (((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n)) ≅ leftSkeletonColimit m n U h) := by
  exact ⟨Functor.leftKanExtensionObjIsoColimit (leftSkeletonInclusion m) U
    (op (SimplexCategory.mk n))⟩

/-- The simplicial map of `iₘ!U` is the map transported from the functorial
colimit construction along the degreewise colimit isomorphisms. -/
theorem leftAdjoint_map_is_functorial_colimit
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m n n' : ℕ) (U : SimplicialObject.Truncated C m)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n')
    (h_n : HasColimit (leftSkeletonDiagram m n U))
    (h_n' : HasColimit (leftSkeletonDiagram m n' U)) :
    ∃ (f : leftSkeletonColimit m n' U h_n' ⟶
        leftSkeletonColimit m n U h_n)
      (e_n : ((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n)) ≅ leftSkeletonColimit m n U h_n)
      (e_n' : ((leftAdjoint m).obj U).obj
        (op (SimplexCategory.mk n')) ≅ leftSkeletonColimit m n' U h_n'),
      e_n'.hom ≫ f =
        ((leftAdjoint m).obj U).map φ.op ≫ e_n.hom := by
  let e_n : ((leftAdjoint m).obj U).obj (op (SimplexCategory.mk n)) ≅
      leftSkeletonColimit m n U h_n :=
    Classical.choice (leftAdjoint_obj_iso_colimit m n U h_n)
  let e_n' : ((leftAdjoint m).obj U).obj (op (SimplexCategory.mk n')) ≅
      leftSkeletonColimit m n' U h_n' :=
    Classical.choice (leftAdjoint_obj_iso_colimit m n' U h_n')
  refine ⟨e_n'.inv ≫ ((leftAdjoint m).obj U).map φ.op ≫ e_n.hom, e_n, e_n', ?_⟩
  simp only [Iso.hom_inv_id_assoc]

/-- In the truncation range the unit of the adjunction is an isomorphism. -/
theorem leftAdjoint_unit_is_iso
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (m : ℕ) (U : SimplicialObject.Truncated C m) :
    IsIso (leftAdjointUnit m U) := by
  let : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  let : (leftSkeletonInclusion m).Full :=
    (SimplexCategory.Truncated.inclusion.fullyFaithful m).full
  let : (leftSkeletonInclusion m).Faithful :=
    (SimplexCategory.Truncated.inclusion.fullyFaithful m).faithful
  dsimp [leftAdjointUnit, leftAdjunction, leftAdjoint]
  rw [Functor.lanAdjunction_unit]
  let : ∀ X, IsIso (((leftSkeletonInclusion m).lanUnit.app U).app X) := fun X =>
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (leftSkeletonInclusion m) U ((leftSkeletonInclusion m).obj X)).isIso_hom_app
  exact NatIso.isIso_of_isIso_app ((leftSkeletonInclusion m).lanUnit.app U)

/-- The degree-`n` colimit exists from the initial object when `n ≤ m`. -/
theorem has_left_skeleton_colimit_of_degree_le
    {C : Type u} [Category.{v} C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    HasColimit (leftSkeletonDiagram m n U) := by
  let hff : (leftSkeletonInclusion m).FullyFaithful :=
    SimplexCategory.Truncated.inclusion.fullyFaithful m
  let : (leftSkeletonInclusion m).Full := hff.full
  let : (leftSkeletonInclusion m).Faithful := hff.faithful
  let Y : (SimplexCategory.Truncated m)ᵒᵖ := op ⟨SimplexCategory.mk n, hn⟩
  let e : op (SimplexCategory.mk n) = (leftSkeletonInclusion m).obj Y := by rfl
  let j0 : leftSkeletonIndex m n :=
    CostructuredArrow.mk (Y := Y) (eqToHom e.symm)
  let hterm : IsTerminal j0 := by
    refine IsTerminal.ofUniqueHom (Y := j0) ?_ ?_
    · intro A
      let g := hff.preimage (A.hom ≫ eqToHom e)
      exact CostructuredArrow.homMk (f := A) (f' := j0) g (by
        change (leftSkeletonInclusion m).map g ≫ eqToHom e.symm = A.hom
        rw [hff.map_preimage]
        simp)
    · intro A f
      apply CostructuredArrow.hom_ext
      apply (leftSkeletonInclusion m).map_injective
      change (leftSkeletonInclusion m).map f.left =
        (leftSkeletonInclusion m).map (hff.preimage (A.hom ≫ eqToHom e))
      calc
        (leftSkeletonInclusion m).map f.left = A.hom ≫ eqToHom e := by
          simpa [j0, e] using congrArg (fun q => q ≫ eqToHom e) f.w
        _ = (leftSkeletonInclusion m).map (hff.preimage (A.hom ≫ eqToHom e)) :=
          (hff.map_preimage (A.hom ≫ eqToHom e)).symm
  exact HasColimit.mk ⟨coconeOfDiagramTerminal hterm (leftSkeletonDiagram m n U),
    colimitOfDiagramTerminal hterm (leftSkeletonDiagram m n U)⟩

/-- The source's recovery statement at an individual degree. -/
theorem leftSkeleton_recovering_degree
    {C : Type u} [Category.{v} C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    Nonempty (leftSkeletonColimit m n U
      (has_left_skeleton_colimit_of_degree_le m n U hn) ≅
      U.obj (op ⟨SimplexCategory.mk n, hn⟩)) := by
  let hcol := has_left_skeleton_colimit_of_degree_le m n U hn
  let : HasColimit (leftSkeletonDiagram m n U) := hcol
  let hff : (leftSkeletonInclusion m).FullyFaithful :=
    SimplexCategory.Truncated.inclusion.fullyFaithful m
  let : (leftSkeletonInclusion m).Full := hff.full
  let : (leftSkeletonInclusion m).Faithful := hff.faithful
  let Y : (SimplexCategory.Truncated m)ᵒᵖ := op ⟨SimplexCategory.mk n, hn⟩
  let e : op (SimplexCategory.mk n) = (leftSkeletonInclusion m).obj Y := by rfl
  let j0 : leftSkeletonIndex m n :=
    CostructuredArrow.mk (Y := Y) (eqToHom e.symm)
  let hterm : IsTerminal j0 := by
    refine IsTerminal.ofUniqueHom (Y := j0) ?_ ?_
    · intro A
      let g := hff.preimage (A.hom ≫ eqToHom e)
      exact CostructuredArrow.homMk (f := A) (f' := j0) g (by
        change (leftSkeletonInclusion m).map g ≫ eqToHom e.symm = A.hom
        rw [hff.map_preimage]
        simp)
    · intro A f
      apply CostructuredArrow.hom_ext
      apply (leftSkeletonInclusion m).map_injective
      change (leftSkeletonInclusion m).map f.left =
        (leftSkeletonInclusion m).map (hff.preimage (A.hom ≫ eqToHom e))
      calc
        (leftSkeletonInclusion m).map f.left = A.hom ≫ eqToHom e := by
          simpa [j0, e] using congrArg (fun q => q ≫ eqToHom e) f.w
        _ = (leftSkeletonInclusion m).map (hff.preimage (A.hom ≫ eqToHom e)) :=
          (hff.map_preimage (A.hom ≫ eqToHom e)).symm
  exact ⟨(colimit.isColimit (leftSkeletonDiagram m n U)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal hterm (leftSkeletonDiagram m n U))⟩

/-- Some authors call truncation followed by `iₘ!` the `m`-skeleton. -/
noncomputable def sourceSkeletonEndofunctor
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ) :
    SimplicialObject C ⥤ SimplicialObject C :=
  SimplicialObject.truncation m ⋙ leftAdjoint m

/-- The analogous source notation for truncation followed by the coskeleton. -/
noncomputable def sourceCoskeletonEndofunctor
    {C : Type u} [Category.{v} C] [HasFiniteLimits C] (m : ℕ) :
    SimplicialObject C ⥤ SimplicialObject C :=
  letI : Unit19.HasCoskeletonFunctor (C := C) m :=
    Unit19.has_coskeleton_functor_of_has_finite_limits m
  SimplicialObject.truncation m ⋙ SimplicialObject.Truncated.cosk m

/-! ## Simplicial sets and the boundary of a simplex -/

/-- The left adjoint on simplicial sets. -/
noncomputable def simplicialSetLeftAdjoint (m : ℕ) :
    SimplicialObject.Truncated (Type u) m ⥤ SSet.{u} :=
  leftAdjoint (C := Type u) m

/-- The counit map from the `m`-skeleton of a simplicial set. -/
noncomputable def simplicialSetLeftAdjointCounit
    (U : SSet.{u}) (m : ℕ) :
    (simplicialSetLeftAdjoint m).obj
        ((SimplicialObject.truncation (C := Type u) m).obj U) ⟶ U :=
  leftAdjointCounit (C := Type u) m U

/-- Every simplex of `iₘ!U` above degree `m` is degenerate. -/
theorem simplicialSetLeftAdjoint_high_degenerate
    (m n : ℕ) (U : SimplicialObject.Truncated (Type u) m) (h : m < n) :
    ∀ x : ((simplicialSetLeftAdjoint m).obj U) _⦋n⦌,
      x ∈ ((simplicialSetLeftAdjoint m).obj U).degenerate n := by
  intro x
  rw [SSet.mem_degenerate_iff]
  let hcol : HasColimit (leftSkeletonDiagram m n U) :=
    has_left_skeleton_colimit_of_has_finite_colimits m n U
  let _ : HasColimit (leftSkeletonDiagram m n U) := hcol
  let e : ((simplicialSetLeftAdjoint m).obj U).obj
      (op (SimplexCategory.mk n)) ≅ leftSkeletonColimit m n U hcol :=
    Functor.leftKanExtensionObjIsoColimit (leftSkeletonInclusion m) U
      (op (SimplexCategory.mk n))
  obtain ⟨A, y, hy⟩ := Types.jointly_surjective' (e.hom x)
  let f : SimplexCategory.mk n ⟶ A.left.unop.obj := A.hom.unop
  let f' := factorThruImage f
  let r := (image f).len
  have hr : r < n := by
    have hle : r ≤ A.left.unop.obj.len := SimplexCategory.len_le_of_mono (image.ι f)
    exact lt_of_le_of_lt (le_trans hle A.left.unop.property) h
  have hxe : e.hom x =
      e.hom (((simplicialSetLeftAdjoint m).obj U).map A.hom
        (((leftAdjointUnit m U).app A.left) y)) := by
    rw [← hy]
    have hι :=
      Functor.leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom
        (leftSkeletonInclusion m) U (op (SimplexCategory.mk n)) A
    exact (congrArg (fun q => q y) (congrArg ConcreteCategory.hom hι)).symm
  have hx : x = ((simplicialSetLeftAdjoint m).obj U).map A.hom
      (((leftAdjointUnit m U).app A.left) y) := by
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 hxe
  have hI : image f = SimplexCategory.mk r := by
    apply SimplexCategory.ext
    rfl
  let eI : image f ≅ SimplexCategory.mk r := eqToIso hI
  let g : SimplexCategory.mk n ⟶ SimplexCategory.mk r := f' ≫ eI.hom
  refine ⟨r, hr, g, inferInstance, ?_⟩
  let y' : ((simplicialSetLeftAdjoint m).obj U).obj (op (image f)) := by
    exact ((simplicialSetLeftAdjoint m).obj U).map (image.ι f).op
      (((leftAdjointUnit m U).app A.left) y)
  refine ⟨((simplicialSetLeftAdjoint m).obj U).map eI.inv.op y', ?_⟩
  rw [hx]
  calc
    ((simplicialSetLeftAdjoint m).obj U).map g.op
          (((simplicialSetLeftAdjoint m).obj U).map eI.inv.op y') =
        ((simplicialSetLeftAdjoint m).obj U).map (g ≫ eI.inv).op y' := by
      simp only [op_comp, Functor.map_comp, comp_apply]
    _ = ((simplicialSetLeftAdjoint m).obj U).map f'.op y' := by
      simp [g, Category.assoc]
    _ = ((simplicialSetLeftAdjoint m).obj U).map (f' ≫ image.ι f).op
          (((leftAdjointUnit m U).app A.left) y) := by
      simp only [y', op_comp, Functor.map_comp]
      rfl
    _ = ((simplicialSetLeftAdjoint m).obj U).map f.op
          (((leftAdjointUnit m U).app A.left) y) := by
      rw [image.fac]
    _ = ((simplicialSetLeftAdjoint m).obj U).map A.hom
          (((leftAdjointUnit m U).app A.left) y) := by
      simp [f]

/-- The simplicial-set counit identifies `iₙ!skₙU` with the earlier skeleton. -/
theorem simplicialSetLeftAdjoint_identifies_skeleton
    (U : SSet.{u}) (n : ℕ) :
    ∃ e : (simplicialSetLeftAdjoint n).obj
          ((SimplicialObject.truncation (C := Type u) n).obj U) ≅
        (Unit18.simplicialSetNSkeleton U n : SSet),
      e.hom ≫ Unit18.simplicialSetNSkeletonInclusion U n =
        simplicialSetLeftAdjointCounit U n := by
  let c := simplicialSetLeftAdjointCounit U n
  let B := Unit18.simplicialSetNSkeleton U n
  have hciso : IsIso ((SimplicialObject.truncation (C := Type u) n).map c) := by
    apply @isIso_of_hom_comp_eq_id _ _ _ _ (leftAdjointUnit n
      ((SimplicialObject.truncation (C := Type u) n).obj U))
      (leftAdjoint_unit_is_iso n _)
    change (leftAdjunction (C := Type u) n).unit.app _ ≫
      (SimplicialObject.truncation (C := Type u) n).map
        ((leftAdjunction (C := Type u) n).counit.app U) = _
    exact (leftAdjunction (C := Type u) n).right_triangle_components U
  have hc_bij : ∀ {d : ℕ}, d ≤ n →
      Function.Bijective (c.app (op ⦋d⦌)) := by
    intro d hd
    change Function.Bijective
      (((SimplicialObject.truncation (C := Type u) n).map c).app
        (op ⟨SimplexCategory.mk d, hd⟩))
    rw [← isIso_iff_bijective]
    infer_instance
  have h_range : SSet.Subcomplex.range c ≤ B := by
    rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    obtain ⟨z, hz⟩ := hx
    have hzn : z ∈ ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type u) n).obj U)).nonDegenerate d := by
      by_contra hzd
      have hdeg := SSet.degenerate_app_apply
        ((SSet.mem_degenerate_iff_notMem_nonDegenerate _ z).mpr hzd) c
      rw [hz] at hdeg
      exact x.property hdeg
    have hd : d ≤ n := by
      by_contra! hdn
      exact hzn (simplicialSetLeftAdjoint_high_degenerate n d
        ((SimplicialObject.truncation (C := Type u) n).obj U) hdn z)
    rw [Unit18.simplicial_set_n_skeleton_agrees_below U n d hd]
    trivial
  let p : (simplicialSetLeftAdjoint n).obj
      ((SimplicialObject.truncation (C := Type u) n).obj U) ⟶ (B : SSet) :=
    SSet.Subcomplex.lift c h_range
  have hp_bij_low : ∀ {d : ℕ}, d ≤ n →
      Function.Bijective (p.app (op ⦋d⦌)) := by
    intro d hd
    have hc := hc_bij hd
    constructor
    · intro x y hxy
      apply hc.1
      simpa [p] using congrArg Subtype.val hxy
    · intro y
      obtain ⟨x, hx⟩ := hc.2 y.1
      refine ⟨x, Subtype.ext ?_⟩
      simpa [p] using hx
  have hp_nd : Unit18.MapsNondegenerate p := by
    intro d x hx
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
    intro hpx
    rw [SSet.mem_degenerate_iff] at hpx
    obtain ⟨k, hk, g, hg, z, hz⟩ := hpx
    have hd : d ≤ n := by
      by_contra! hdn
      exact hx (simplicialSetLeftAdjoint_high_degenerate n d
        ((SimplicialObject.truncation (C := Type u) n).obj U) hdn x)
    have hkd : k ≤ n := le_trans (Nat.le_of_lt hk) hd
    obtain ⟨w, hw⟩ := hp_bij_low hkd |>.2 z
    have h_eq : p.app (op ⦋d⦌) (((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type u) n).obj U)).map g.op w) =
        p.app (op ⦋d⦌) x := by
      rw [NatTrans.naturality_apply, hw, hz]
    have : ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type u) n).obj U)).map g.op w = x := by
      exact (hp_bij_low hd).1 h_eq
    exact hx ⟨k, hk, g, w, this⟩
  have hp_bij : ∀ d, Function.Bijective (p.app (op ⦋d⦌)) := by
    apply Unit18.simplicial_set_map_bijective_of_nonDegenerate p hp_nd
    intro d
    constructor
    · intro x y hxy
      exact Subtype.ext ((hp_bij_low (by
        by_contra! hd
        exact x.property (simplicialSetLeftAdjoint_high_degenerate n d _ hd x.1))).1
        (congrArg Subtype.val hxy))
    · intro y
      have hndU : (y.1 : U _⦋d⦌) ∈ U.nonDegenerate d :=
        (SSet.Subcomplex.mem_nonDegenerate_iff B y.1).mp y.property
      let hndU' : U.nonDegenerate d := ⟨y.1, hndU⟩
      have hskel : (y.1 : U _⦋d⦌) ∈ B.obj (op ⦋d⦌) := y.1.property
      have hdlt : d < n + 1 := by
        apply (SSet.mem_skeleton_obj_iff_of_nonDegenerate
          (X := U) hndU' (n + 1)).mp
        simpa [B, Unit18.simplicialSetNSkeleton] using hskel
      have hd : d ≤ n := by omega
      obtain ⟨x, hx⟩ := (hp_bij_low hd).2 y.1
      have hxnd : x ∈ ((simplicialSetLeftAdjoint n).obj
          ((SimplicialObject.truncation (C := Type u) n).obj U)).nonDegenerate d := by
        by_contra hxn
        have hdeg := SSet.degenerate_app_apply
          ((SSet.mem_degenerate_iff_notMem_nonDegenerate _ x).mpr hxn) p
        rw [hx] at hdeg
        exact y.property hdeg
      refine ⟨⟨x, hxnd⟩, ?_⟩
      apply Subtype.ext
      exact hx
  have hp_iso : IsIso p := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    induction d using Opposite.rec with
    | _ d =>
      induction d using SimplexCategory.rec with
      | _ d =>
        rw [isIso_iff_bijective]
        exact hp_bij d
  refine ⟨@asIso _ _ _ _ p hp_iso, ?_⟩
  simpa [p, c, simplicialSetLeftAdjointCounit, leftAdjointCounit,
    Unit18.simplicialSetNSkeletonInclusion, B] using
    SSet.Subcomplex.lift_ι c h_range

/-- The source's `iₙ!skₙ` notation as an endofunctor on simplicial sets. -/
noncomputable def sourceSimplicialSetSkeleton (n : ℕ) :
    SSet.{u} ⥤ SSet.{u} :=
  sourceSkeletonEndofunctor (C := Type u) n

/-- The source's boundary construction written using the left adjoint. -/
noncomputable def boundaryViaLeftAdjoint (n : ℕ) (_hn : 0 < n) : SSet.{u} :=
  (simplicialSetLeftAdjoint (n - 1)).obj
    ((SimplicialObject.truncation (C := Type u) (n - 1)).obj
      (Δ[n] : SSet.{u}))

/-- For positive `n`, the source's left-adjoint boundary is `∂Δ[n]`. -/
theorem boundaryViaLeftAdjoint_iso_boundary
    (n : ℕ) (hn : 0 < n) :
    Nonempty (boundaryViaLeftAdjoint n hn ≅ (∂Δ[n] : SSet.{u})) := by
  obtain ⟨e, he⟩ := simplicialSetLeftAdjoint_identifies_skeleton
    (Δ[n] : SSet.{u}) (n - 1)
  have hB : Unit18.simplicialSetNSkeleton (Δ[n] : SSet.{u}) (n - 1) =
      (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) := by
    have hsub : Unit18.simplicialSetNSkeleton (Δ[n] : SSet.{u}) (n - 1) ≤
        (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) := by
      rw [SSet.stdSimplex.le_boundary_iff]
      intro htop
      have hx : SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n)) ∈
          (Unit18.simplicialSetNSkeleton (Δ[n] : SSet.{u}) (n - 1)).obj
            (op ⦋n⦌) := by
        rw [htop]
        trivial
      have hnd0 : SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n)) ∈
          (Δ[n] : SSet.{u}).nonDegenerate n := by
        rw [SSet.stdSimplex.nonDegenerate_top_dim]
        simp
      let hnd : (Δ[n] : SSet.{u}).nonDegenerate n :=
        ⟨SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n)), hnd0⟩
      have hn' : 1 ≤ n := by omega
      have hs : hnd.1 ∈
          ((Δ[n] : SSet.{u}).skeleton n).obj (op ⦋n⦌) := by
        simpa [hnd, Unit18.simplicialSetNSkeleton,
          Nat.sub_add_cancel hn'] using hx
      have hdim := (SSet.mem_skeleton_obj_iff_of_nonDegenerate
        (X := (Δ[n] : SSet.{u})) hnd n).mp hs
      omega
    apply le_antisymm hsub
    rw [SSet.boundary_eq_iSup]
    apply iSup_le
    intro i
    let e₀ : {x : Fin (n + 1) // x ≠ i} ≃
        {x : Fin (n + 1) // x ∈ ({i}ᶜ : Finset (Fin (n + 1)))} :=
      { toFun := fun x => ⟨x.1, by
            simpa only [Finset.mem_compl, Finset.mem_singleton] using x.2⟩
        invFun := fun x => ⟨x.1, by
            simpa only [Finset.mem_compl, Finset.mem_singleton] using x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    let e₁ : {x : Fin (n + 1) // x ≠ i} ≃o
        {x : Fin (n + 1) // x ∈ ({i}ᶜ : Finset (Fin (n + 1)))} :=
      e₀.toOrderIso (by intro a b h; exact h) (by intro a b h; exact h)
    let ei : Fin ((n - 1) + 1) ≃o ({i}ᶜ : Finset (Fin (n + 1))) :=
      (Fin.castOrderIso (by omega)).trans ((finSuccAboveOrderIso i).trans e₁)
    rw [SSet.stdSimplex.face_eq_ofSimplex ({i}ᶜ) (n - 1) ei]
    change SSet.Subcomplex.ofSimplex _ ≤
      (Δ[n] : SSet.{u}).skeleton ((n - 1) + 1)
    apply SSet.ofSimplex_le_skeleton
    omega
  let e' : boundaryViaLeftAdjoint n hn ≅ (∂Δ[n] : SSet.{u}) := by
    simpa only [boundaryViaLeftAdjoint] using e ≪≫ SSet.Subcomplex.eqToIso hB
  exact ⟨e'⟩

/-! ## Attaching one simplex -/

/-- The exact hypotheses in the source's simplex-gluing lemma.

The source's displayed boundary is represented by the canonical `SSet.boundary`;
in degree zero Mathlib identifies it with the empty sub-simplicial set.
-/
structure SimplexAttachment
    {U V : SSet.{u}} (i : U ⟶ V) (n : ℕ) (x : V _⦋n⦌) : Prop where
  mono_i : Mono i
  agrees_below : ∀ {j : ℕ}, j < n →
    Function.Surjective (i.app (op ⦋j⦌))
  exactly_one_new : ∀ y : V _⦋n⦌,
    y ∈ Set.range (i.app (op ⦋n⦌)) ∨ y = x
  new_not_in_range : x ∉ Set.range (i.app (op ⦋n⦌))
  outside_degenerate : ∀ {j : ℕ}, n < j →
    ∀ y : V _⦋j⦌, y ∉ Set.range (i.app (op ⦋j⦌)) →
      y ∈ V.degenerate j

/-- The unique map from a standard simplex represented by its top simplex. -/
def simplexMapOfSimplex (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    (Δ[n] : SSet.{u}) ⟶ V :=
  SSet.yonedaEquiv.symm x

/-- The defining property of `simplexMapOfSimplex`. -/
theorem simplexMapOfSimplex_apply (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    SSet.yonedaEquiv (simplexMapOfSimplex V n x) = x := by
  exact SSet.yonedaEquiv.apply_symm_apply x

/-- The simplex map represented by `x` is unique. -/
theorem simplexMapOfSimplex_unique (V : SSet.{u}) (n : ℕ) (x : V _⦋n⦌) :
    ∃! f : (Δ[n] : SSet.{u}) ⟶ V,
      SSet.yonedaEquiv f = x := by
  refine ⟨simplexMapOfSimplex V n x, simplexMapOfSimplex_apply V n x, ?_⟩
  intro f hf
  exact SSet.yonedaEquiv.injective
    (hf.trans (simplexMapOfSimplex_apply V n x).symm)

/-- The degree-zero boundary is the initial (empty) simplicial set. -/
theorem boundary_zero_is_empty :
    Nonempty ((∂Δ[0] : SSet.{u}) ≅ initial SSet.{u}) := by
  rw [SSet.boundary_zero]
  exact ⟨(SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).uniqueUpToIso
    (initialIsInitial)⟩

/-- A new simplex gives the source's pushout square. -/
theorem glue_simplex
    {U V : SSet.{u}} (i : U ⟶ V) (n : ℕ) (x : V _⦋n⦌)
    (h : SimplexAttachment i n x) :
    ∃ f : (∂Δ[n] : SSet.{u}) ⟶ U,
      f ≫ i = (SSet.boundary n).ι ≫ simplexMapOfSimplex V n x ∧
      IsPushout (SSet.boundary n).ι f
        (simplexMapOfSimplex V n x) i := by
  let _ : Mono i := h.mono_i
  have hx_nd : x ∈ V.nonDegenerate n := by
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
    intro hxdeg
    obtain ⟨m, hm, g, hg, z, hz⟩ := (SSet.mem_degenerate_iff (X := V) x).mp hxdeg
    obtain ⟨w, hw⟩ := h.agrees_below hm z
    apply h.new_not_in_range
    refine ⟨U.map g.op w, ?_⟩
    rw [NatTrans.naturality_apply, hw, hz]
  have simplexMap_app (d : ℕ) (g : ⦋d⦌ ⟶ ⦋n⦌) :
      (simplexMapOfSimplex V n x).app (op ⦋d⦌)
          (SSet.stdSimplex.objEquiv.symm g) = V.map g.op x := by
    change dsimp% (SSet.yonedaEquiv.symm x).app (op ⦋d⦌)
      (SSet.stdSimplex.objEquiv.symm g) = V.map g.op x
    exact SSet.yonedaEquiv_symm_app_objEquiv_symm x g
  let p : (∂Δ[n] : SSet.{u}) ⟶ V :=
    (SSet.boundary n).ι ≫ simplexMapOfSimplex V n x
  have hp_range : SSet.Subcomplex.range p ≤ SSet.Subcomplex.range i := by
    rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.image_le_iff]
    rw [show SSet.Subcomplex.range (SSet.boundary n).ι = SSet.boundary n from
      CategoryTheory.Subfunctor.range_ι _]
    rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
    intro d y hy
    let y' : (SSet.boundary n : SSet.{u}).nonDegenerate d :=
      ⟨⟨y, hy⟩, by
        exact (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary n)
          (⟨y, hy⟩ : (SSet.boundary n).obj (op ⦋d⦌))).mpr y.property⟩
    have hd : d < n := SSet.dim_lt_of_nonDegenerate
      (X := (SSet.boundary n : SSet.{u})) y' n
    obtain ⟨z, hz⟩ := h.agrees_below hd
      ((simplexMapOfSimplex V n x).app (op ⦋d⦌) y)
    change (simplexMapOfSimplex V n x).app (op ⦋d⦌) y ∈
      Set.range (i.app (op ⦋d⦌))
    exact ⟨z, hz⟩
  let q : (∂Δ[n] : SSet.{u}) ⟶ SSet.Subcomplex.range i :=
    SSet.Subcomplex.lift p hp_range
  let f : (∂Δ[n] : SSet.{u}) ⟶ U :=
    q ≫ inv (SSet.Subcomplex.toRange i)
  have hf : f ≫ i = p := by
    dsimp [f]
    change q ≫ inv (SSet.Subcomplex.toRange i) ≫ i = p
    have ht : inv (SSet.Subcomplex.toRange i) ≫ i =
        (SSet.Subcomplex.range i).ι := by
      apply (cancel_epi (SSet.Subcomplex.toRange i)).1
      simp
    calc
      q ≫ inv (SSet.Subcomplex.toRange i) ≫ i = q ≫
          (inv (SSet.Subcomplex.toRange i) ≫ i) := by rfl
      _ = p := by rw [ht, SSet.Subcomplex.lift_ι]
  refine ⟨f, hf, ?_⟩
  refine { w := by simpa [p] using hf.symm, isColimit' := ⟨evaluationJointlyReflectsColimits _
    (fun ⟨⟨d⟩⟩ ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    refine (Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_).flip
    · rw [Types.isPullback_iff]
      refine ⟨congr($(hf).app (op ⦋d⦌)), ?_, ?_⟩
      · intro a b hab
        apply Subtype.ext
        simpa using hab.2
      · intro a b hab
        by_cases ha : b ∈ (SSet.boundary n).obj (op ⦋d⦌)
        · refine ⟨⟨b, ha⟩, ?_, rfl⟩
          apply injective_of_mono (i.app (op ⦋d⦌))
          have hfac := congrArg (fun k : (∂Δ[n] : SSet.{u}) ⟶ V =>
            k.app (op ⦋d⦌) ⟨b, ha⟩) hf
          change i.app (op ⦋d⦌) (f.app (op ⦋d⦌) ⟨b, ha⟩) =
              (simplexMapOfSimplex V n x).app (op ⦋d⦌) b at hfac
          exact hfac.trans hab.symm
        · obtain ⟨r, rfl⟩ :=
            (SSet.stdSimplex.objEquiv (n := ⦋n⦌) (m := op ⦋d⦌)).symm.surjective b
          have hr_epi : Epi r := by
            simpa [SimplexCategory.epi_iff_surjective, SSet.boundary] using! ha
          have hdim : n ≤ d := by simpa using (SimplexCategory.len_le_of_epi r)
          have htop : n = d := by
            by_contra hlt
            have hsection := isSplitEpi_of_epi r
            have hxrange : x ∈ Set.range (i.app (op ⦋n⦌)) := by
              refine ⟨(U.map (section_ r).op) a, ?_⟩
              calc
                (i.app (op ⦋n⦌)) ((U.map (section_ r).op) a) =
                    V.map (section_ r).op (i.app (op ⦋d⦌) a) := by
                  rw [NatTrans.naturality_apply]
                _ = V.map (section_ r).op
                    ((simplexMapOfSimplex V n x).app _
                      (SSet.stdSimplex.objEquiv.symm r)) := by
                  simpa using congrArg (V.map (section_ r).op) hab
                _ = V.map (section_ r).op (V.map r.op x) := by
                  rw [simplexMap_app]
                _ = x := by
                  rw [← Functor.map_comp_apply, ← op_comp]
                  simp
            exact h.new_not_in_range hxrange
          subst d
          have hr_id : r = 𝟙 _ := SimplexCategory.eq_id_of_epi r
          subst r
          exact (h.new_not_in_range ⟨a, by
            simpa [simplexMap_app] using hab⟩).elim
    · ext y
      simp only [Set.mem_univ, iff_true]
      by_cases hy : y ∈ Set.range (i.app (op ⦋d⦌))
      · exact Or.inl hy
      · obtain ⟨m, g, hg, z, hz⟩ := V.exists_nonDegenerate y
        have hz_not : z.1 ∉ Set.range (i.app (op ⦋m⦌)) := by
          intro hz'
          obtain ⟨w, hw⟩ := hz'
          apply hy
          refine ⟨U.map g.op w, ?_⟩
          rw [NatTrans.naturality_apply, hw, hz]
        have hm : m = n := by
          rcases Nat.lt_trichotomy m n with hmn | rfl | hnm
          · obtain ⟨w, hw⟩ := h.agrees_below hmn z.1
            exact (hz_not ⟨w, hw⟩).elim
          · rfl
          · exact (z.property (h.outside_degenerate hnm z.1 hz_not)).elim
        subst hm
        have hzx : z.1 = x := (h.exactly_one_new z.1).resolve_left hz_not
        refine Or.inr ⟨SSet.stdSimplex.objEquiv.symm g, ?_⟩
        calc
          (simplexMapOfSimplex V m x).app (op ⦋d⦌)
              (SSet.stdSimplex.objEquiv.symm g) = V.map g.op x :=
            simplexMap_app d g
          _ = y := hzx ▸ hz.symm
    · intro a b ha hb hab
      obtain ⟨r₁, rfl⟩ :=
        (SSet.stdSimplex.objEquiv (n := ⦋n⦌) (m := op ⦋d⦌)).symm.surjective a
      obtain ⟨r₂, rfl⟩ :=
        (SSet.stdSimplex.objEquiv (n := ⦋n⦌) (m := op ⦋d⦌)).symm.surjective b
      have ha' : SSet.stdSimplex.objEquiv.symm r₁ ∉
          (SSet.boundary n).obj (op ⦋d⦌) := by
        intro ha_mem
        apply ha
        exact ⟨⟨SSet.stdSimplex.objEquiv.symm r₁, ha_mem⟩, rfl⟩
      have hb' : SSet.stdSimplex.objEquiv.symm r₂ ∉
          (SSet.boundary n).obj (op ⦋d⦌) := by
        intro hb_mem
        apply hb
        exact ⟨⟨SSet.stdSimplex.objEquiv.symm r₂, hb_mem⟩, rfl⟩
      have hr₁ : Epi r₁ := by
        simpa [SimplexCategory.epi_iff_surjective, SSet.boundary] using! ha'
      have hr₂ : Epi r₂ := by
        simpa [SimplexCategory.epi_iff_surjective, SSet.boundary] using! hb'
      have hr : r₁ = r₂ := V.unique_nonDegenerate_map
          ((simplexMapOfSimplex V n x).app (op ⦋d⦌)
            (SSet.stdSimplex.objEquiv.symm r₁)) r₁ ⟨x, hx_nd⟩ (by
              exact simplexMap_app d r₁) r₂ ⟨x, hx_nd⟩ (by
              calc
                (simplexMapOfSimplex V n x).app (op ⦋d⦌)
                    (SSet.stdSimplex.objEquiv.symm r₁) =
                    (simplexMapOfSimplex V n x).app (op ⦋d⦌)
                      (SSet.stdSimplex.objEquiv.symm r₂) := hab
                _ = V.map r₂.op x := simplexMap_app d r₂)
      simp [hr]
    )⟩ }

/-- A finite inclusion is obtained by adjoining finitely many simplices.

For an arbitrary categorical monomorphism the filtration has endpoint
isomorphisms rather than literal endpoint equalities.  The latter are the
source's subset convention, which is not available for arbitrary `SSet`
objects. -/
theorem finite_simplicial_set_filtration
    {U V : SSet.{u}} (i : U ⟶ V) [Mono i]
    (hU : ∀ n, Finite (U _⦋n⦌) ∧ Nonempty (U _⦋n⦌))
    (hV : ∀ n, Finite (V _⦋n⦌) ∧ Nonempty (V _⦋n⦌))
    [U.Finite] [V.Finite] :
    ∃ (r : ℕ) (W : Fin (r + 1) → SSet.{u})
      (f : ∀ j : Fin r, W j.castSucc ⟶ W j.succ)
      (g : ∀ j : Fin (r + 1), W j ⟶ V),
      ∃ (e₀ : W 0 ≅ U) (eᵣ : W ⟨r, Nat.lt_succ_self r⟩ ≅ V),
        g 0 = e₀.hom ≫ i ∧
        g ⟨r, Nat.lt_succ_self r⟩ = eᵣ.hom ∧
        (∀ j, f j ≫ g j.succ = g j.castSucc) ∧
    (∀ j, Mono (f j)) ∧
        (∀ j, ∃ (n : ℕ) (x : (W j.succ) _⦋n⦌),
          SimplexAttachment (f j) n x) := by
  sorry

/-! ## The abelian-category consequence -/

/-- The normalized object of `iₘ!U` is a zero object above the truncation degree.

The source writes this as equality with `0`; here `normalizedObject` is the
chosen underlying object of a `Subobject`, so the categorical `IsZero`
interface avoids requiring a literal equality between that representative and
the chosen zero object.
-/
theorem leftAdjoint_normalizedObject_eq_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) (h : m < n) :
    IsZero (Unit18.normalizedObject ((leftAdjoint (C := C) m).obj U) n) := by
  classical
  letI : HasLeftSkeletonFunctor C m :=
    has_left_skeleton_functor_of_has_finite_colimits m
  letI : (leftSkeletonInclusion m).HasLeftKanExtension U :=
    has_left_skeleton_functor_of_has_finite_colimits m U
  let X : SimplicialObject C := (leftSkeletonInclusion m).leftKanExtension U
  obtain ⟨s, hs⟩ := Unit18.abelian_category_has_normalized_splitting X
  obtain ⟨eN, heN⟩ := hs.1 n
  have hN : IsZero (s.N n) := by
    let F : ∀ A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌),
        s.N A.1.unop.len ⟶ s.N n := fun A =>
        dite A.EqId (fun hA =>
          eqToHom (by
            rw [(SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq A).mp hA]))
          (fun _ => 0)
    let q : X.obj (op ⦋n⦌) ⟶ s.N n := s.desc (op ⦋n⦌) F
    have hdeg : ∀ {Δ : SimplexCategoryᵒᵖ}
        (p : Δ ⟶ op ⦋n⦌), Δ.unop.len < n →
        X.map p ≫ q = 0 := by
      intro Δ p hp
      let e : SimplexCategory := image p.unop
      let ep : ⦋n⦌ ⟶ e := factorThruImage p.unop
      let im : e ⟶ Δ.unop := image.ι p.unop
      letI : Epi ep := by
        dsimp [ep]
        infer_instance
      letI : Mono im := by
        dsimp [im]
        infer_instance
      have hfac : p = im.op ≫ ep.op := by
        apply Quiver.Hom.unop_inj
        simpa [ep, im] using (image.fac p.unop)
      have helt : e.len < n := by
        have hle : e.len ≤ Δ.unop.len :=
          SimplexCategory.len_le_of_mono im
        exact lt_of_le_of_lt hle hp
      have hq : X.map ep.op ≫ q = 0 := by
        apply (s.isColimit (op e)).hom_ext
        intro ⟨B⟩
        have hnat := s.cofan_inj_epi_naturality B ep.op
        have hnat' := congrArg (fun z => z ≫ q) hnat
        simp only [Cofan.inj] at hnat'
        rw [← Category.assoc]
        simp only [comp_zero]
        rw [hnat']
        let B' := B.epiComp ep.op
        have hB : ¬ B'.EqId := by
          intro hB
          have hlen :=
            (SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq B').mp hB
          have hle : B.1.unop.len ≤ e.len :=
            SimplexCategory.len_le_of_epi B.e
          dsimp [B', SimplicialObject.Splitting.IndexSet.epiComp] at hlen
          omega
        have hF : F B' = 0 := by
          change (if h : B'.EqId then _ else 0) = 0
          exact dif_neg hB
        have hd := s.ι_desc (op ⦋n⦌) F B'
        rw [hF] at hd
        dsimp [B', SimplicialObject.Splitting.IndexSet.epiComp, Cofan.inj] at hd ⊢
        change (s.cofan (op ⦋n⦌)).ι.app (Discrete.mk
          ⟨B.fst, ⟨ep ≫ B.e, epi_comp _ _⟩⟩) ≫ s.desc (op ⦋n⦌) F = 0
        exact hd
      rw [hfac, X.map_comp, Category.assoc, hq, comp_zero]
    have hcol : HasColimit
        (CostructuredArrow.proj (leftSkeletonInclusion m) (op ⦋n⦌) ⋙ U) := by
      simpa [leftSkeletonDiagram] using
        (has_left_skeleton_colimit_of_has_finite_colimits m n U)
    letI := hcol
    let e : X.obj (op ⦋n⦌) ≅
        colimit (CostructuredArrow.proj (leftSkeletonInclusion m) (op ⦋n⦌) ⋙ U) :=
      Functor.leftKanExtensionObjIsoColimit (leftSkeletonInclusion m) U
        (op ⦋n⦌)
    have hq : e.inv ≫ q = 0 := by
      apply (colimit.isColimit
        (CostructuredArrow.proj (leftSkeletonInclusion m) (op ⦋n⦌) ⋙ U)).hom_ext
      intro A
      dsimp [e, X]
      rw [← Category.assoc]
      rw [Functor.ι_leftKanExtensionObjIsoColimit_inv]
      have hp : A.left.unop.obj.len < n := by
        exact lt_of_le_of_lt A.left.unop.property h
      simp only [comp_zero]
      change (((leftSkeletonInclusion m).leftKanExtensionUnit U).app A.left ≫
        X.map A.hom) ≫ q = 0
      rw [Category.assoc, hdeg A.hom hp, comp_zero]
    have hq' : q = 0 := by
      rw [← e.hom_inv_id_assoc q, hq, comp_zero]
    have hid : s.ι n ≫ q = 𝟙 (s.N n) := by
      rw [← s.cofan_inj_id n]
      have hFid : F (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌)) =
          𝟙 (s.N n) := by
        have hi : (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌)).EqId :=
          (SimplicialObject.Splitting.IndexSet.eqId_iff_eq _).2 rfl
        simp only [F, dif_pos hi]
        exact eqToHom_refl _ _
      have hd := s.ι_desc (op ⦋n⦌) F
        (SimplicialObject.Splitting.IndexSet.id (op ⦋n⦌))
      rw [hFid] at hd
      simpa only [q, SimplicialObject.Splitting.summand,
        SimplicialObject.Splitting.IndexSet.id] using hd
    rw [hq'] at hid
    rw [IsZero.iff_id_eq_zero]
    simpa using hid.symm
  change IsZero (Unit18.normalizedObject X n)
  exact hN.of_iso eN.symm

/-- The abelian `n`-skeleton is the earlier normalized-subobject skeleton. -/
theorem leftAdjoint_identifies_abelian_skeleton
    {C : Type u} [Category.{v} C] [Abelian C] (n : ℕ)
    (U : SimplicialObject C) :
    ∃ (U' : SimplicialObject C) (i : U' ⟶ U),
      Mono i ∧
      (∀ m, imageSubobject (i.app (op ⦋m⦌)) =
        Unit18.abelianNSkeletonSubobject U n m) ∧
      (∀ m, m ≤ n → imageSubobject (i.app (op ⦋m⦌)) = ⊤) ∧
      (∀ m, n < m → Unit18.normalizedSubobject U' m = ⊥) ∧
      ∃ e : (leftAdjoint (C := C) n).obj
          ((SimplicialObject.truncation (C := C) n).obj U) ≅ U',
        e.hom ≫ i = leftAdjointCounit (C := C) n U := by
  sorry

/-! ## The final `coskₙ skₙ` formula -/

/-- The degreewise coproduct used for the source's notation `X × U`. -/
noncomputable def objectProductWithSimplicialSet
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (U : SSet.{w})
    (hU : Unit13.FiniteNonemptySimplicialSet U) : SimplicialObject C :=
  Unit13.simplicialSetProduct U ((SimplicialObject.const C).obj X) hU

/-- The restriction of `X × Δ[n+1]`, i.e. `X × skₙΔ[n+1]`. -/
noncomputable def truncatedProductWithStandardSimplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (n : ℕ) : SimplicialObject.Truncated C n :=
    (SimplicialObject.truncation (C := C) n).obj
    (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{w})
      (Unit13.standardSimplex_finite_nonempty (n + 1)))

/-- The first product identity in the source is definitional for this model. -/
theorem truncation_product_with_standard_simplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (n : ℕ) :
    (SimplicialObject.truncation (C := C) n).obj
      (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{w})
          (Unit13.standardSimplex_finite_nonempty (n + 1))) =
      truncatedProductWithStandardSimplex.{v, u, w} X n := by
  rfl

/-- The product compatibility of `iₙ!` used in the final proof. -/
theorem leftAdjoint_product_with_standard_simplex
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [HasFiniteColimits C] (X : C) (n : ℕ)
    (hA : Unit13.FiniteNonemptySimplicialSet
      ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type w) n).obj
          (Δ[n + 1] : SSet.{w})))) :
    Nonempty (
      (leftAdjoint (C := C) n).obj
          (truncatedProductWithStandardSimplex X n) ≅
        objectProductWithSimplicialSet X
          ((simplicialSetLeftAdjoint n).obj
            ((SimplicialObject.truncation (C := Type w) n).obj
              (Δ[n + 1] : SSet.{w})))
          hA) := by
  sorry

/-- The simplicial set `Mor_C(X,W)` used in the source's proof. -/
def objectHomSimplicialSet
    {C : Type u} [Category.{v} C] (X : C) (W : SimplicialObject C) :
    SSet.{v} where
  obj A := X ⟶ W.obj A
  map f := ↾fun g => g ≫ W.map f
  map_id A := by
    ext g
    change g ≫ W.map (𝟙 A) = g
    simp
  map_comp f g := by
    ext h
    change h ≫ W.map (f ≫ g) =
      (h ≫ W.map f) ≫ W.map g
    simp [Category.assoc]

/-- The same `Mor_C(X,W)` construction for a truncated simplicial object. -/
def objectHomTruncatedSimplicialSet
    {C : Type u} [Category.{v} C] (n : ℕ) (X : C)
    (W : SimplicialObject.Truncated C n) :
    SimplicialObject.Truncated (Type v) n where
  obj A := X ⟶ W.obj A
  map f := ↾fun g => g ≫ W.map f
  map_id A := by
    ext g
    change g ≫ W.map (𝟙 A) = g
    simp
  map_comp f g := by
    ext h
    change h ≫ W.map (f ≫ g) =
      (h ≫ W.map f) ≫ W.map g
    simp [Category.assoc]

/-- Restricting `Mor_C(X,W)` agrees with the truncated construction. -/
theorem objectHomTruncatedSimplicialSet_truncation
    {C : Type u} [Category.{v} C] (n : ℕ) (X : C)
    (W : SimplicialObject C) :
    objectHomTruncatedSimplicialSet n X
        ((SimplicialObject.truncation (C := C) n).obj W) =
      (SimplicialObject.truncation (C := Type v) n).obj
        (objectHomSimplicialSet X W) := by
  sorry

/-- The source's `Mor(U × X,W)=Mor(U,Mor_C(X,W))` equivalence. -/
theorem objectHomSimplicialSet_product_hom_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (X : C) (U : SSet.{v})
    (hU : Unit13.FiniteNonemptySimplicialSet U) (W : SimplicialObject C) :
    Nonempty ((objectProductWithSimplicialSet X U hU ⟶ W) ≃
      (U ⟶ objectHomSimplicialSet X W)) := by
  sorry

/-- Data for the degree-zero simplicial-object Hom used by the source. -/
structure SimplicialSetHomZeroData
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) where
  object : C
  homEquiv : ∀ X : C,
    (X ⟶ object) ≃ (objectProductWithSimplicialSet X U hU ⟶ V)

/-- Existence of the degree-zero object `Hom(U,V)₀`. -/
abbrev HasSimplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U) : Prop :=
  Nonempty (SimplicialSetHomZeroData U V hU)

/-- A chosen degree-zero Hom object. -/
noncomputable def simplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (h : HasSimplicialSetHomZero U V hU) : C :=
  (Classical.choice h).object

/-- Its representing equivalence. -/
noncomputable def simplicialSetHomZeroHomEquiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (h : HasSimplicialSetHomZero U V hU) (X : C) :
    (X ⟶ simplicialSetHomZero U V hU h) ≃
      (objectProductWithSimplicialSet X U hU ⟶ V) :=
  (Classical.choice h).homEquiv X

/-- The finite/degenerate hypotheses from the preceding Hom construction give `Hom(U,V)₀`. -/
theorem exists_simplicialSetHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (U : SSet.{v}) (V : SimplicialObject C)
    (hU : Unit13.FiniteNonemptySimplicialSet U)
    (hUdeg : ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ x : U _⦋n⦌, x ∈ U.degenerate n) :
    HasSimplicialSetHomZero U V hU := by
  sorry

/-- The standard simplex after applying `skₙ` and `iₙ!`. -/
noncomputable def standardSimplexLeftSkeleton (n : ℕ) : SSet.{v} :=
  (simplicialSetLeftAdjoint n).obj
    ((SimplicialObject.truncation (C := Type v) n).obj
      (Δ[n + 1] : SSet.{v}))

/-- The standard simplex left skeleton has the finite nonempty property. -/
theorem standardSimplexLeftSkeleton_finite_nonempty (n : ℕ) :
    Unit13.FiniteNonemptySimplicialSet
      (standardSimplexLeftSkeleton n) := by
  sorry

/-- The preceding finite Hom construction applies to `iₙ!skₙΔ[n+1]`. -/
theorem standardSimplexLeftSkeleton_has_hom_zero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) :
    HasSimplicialSetHomZero (standardSimplexLeftSkeleton n) V
      (standardSimplexLeftSkeleton_finite_nonempty n) := by
  sorry

/-- The source notation `Hom(iₙ!skₙΔ[n+1],V)₀`. -/
noncomputable def standardSimplexHomZero
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) : C :=
  simplicialSetHomZero (standardSimplexLeftSkeleton n) V
    (standardSimplexLeftSkeleton_finite_nonempty n)
    (standardSimplexLeftSkeleton_has_hom_zero n V)

/-- The Hom object represents maps from `X × iₙ!skₙΔ[n+1]` into `V`. -/
theorem standardSimplexHomZero_hom_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty ((X ⟶ standardSimplexHomZero n V) ≃
      (objectProductWithSimplicialSet X
        (standardSimplexLeftSkeleton n)
        (standardSimplexLeftSkeleton_finite_nonempty n) ⟶ V)) := by
  sorry

/-- The final degree formula for `coskₙskₙV`. -/
theorem coskeleton_skeleton_degree_formula
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) :
    Nonempty (
      ((sourceCoskeletonEndofunctor (C := C) n).obj
          V).obj
            (op (SimplexCategory.mk (n + 1))) ≅
        standardSimplexHomZero n V) := by
  sorry

/-- The complete chain of mapping objects used to prove the final formula. -/
theorem coskeleton_skeleton_mapping_chain
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty (
      (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{v})
          (Unit13.standardSimplex_finite_nonempty (n + 1)) ⟶
        (sourceCoskeletonEndofunctor (C := C) n).obj V) ≃
      (objectProductWithSimplicialSet X
          (standardSimplexLeftSkeleton n)
          (standardSimplexLeftSkeleton_finite_nonempty n) ⟶ V)) := by
  sorry

/-- The first displayed mapping equivalence in the proof of the final formula. -/
theorem coskeleton_skeleton_first_mapping_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasFiniteLimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C) :
    Nonempty (
      (objectProductWithSimplicialSet X (Δ[n + 1] : SSet.{v})
          (Unit13.standardSimplex_finite_nonempty (n + 1)) ⟶
        (sourceCoskeletonEndofunctor (C := C) n).obj V) ≃
      (truncatedProductWithStandardSimplex X n ⟶
        (SimplicialObject.truncation (C := C) n).obj V)) := by
  sorry

/-- The second displayed mapping equivalence in the proof of the final formula. -/
theorem coskeleton_skeleton_second_mapping_equiv
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    [HasFiniteColimits C]
    (n : ℕ) (V : SimplicialObject C) (X : C)
    (hA : Unit13.FiniteNonemptySimplicialSet
      ((simplicialSetLeftAdjoint n).obj
        ((SimplicialObject.truncation (C := Type v) n).obj
          (Δ[n + 1] : SSet.{v})))) :
    Nonempty (
      (truncatedProductWithStandardSimplex X n ⟶
        (SimplicialObject.truncation (C := C) n).obj V) ≃
      (objectProductWithSimplicialSet X
          ((simplicialSetLeftAdjoint n).obj
            ((SimplicialObject.truncation (C := Type v) n).obj
              (Δ[n + 1] : SSet.{v}))) hA ⟶ V)) := by
  sorry

end Formalization.Books.Simplicial.Unit21
