import Formalization.Books.Exercises.Unit30.Core
import Formalization.Books.Homology.Unit13.Complexes
import Formalization.Books.Homology.Unit27.Injectives
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Exercises, Chapter 30: Filtered derived category

The theorem interfaces follow the nine numbered exercises in the source.
Proofs are deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe v u

namespace Formalization.Books.Exercises.Unit30

open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit13

/-! ## Exercise 30.1 -/

/-- A filtered injective object splits as the finite direct sum of its graded
pieces, with the filtration transported to the degreewise direct-sum
filtration. -/
/- Proof roadmap.
1. From `hfinite`, choose a top step `a` and a bottom step `b`.  If the
   carrier is nonzero, antitonicity gives `a < b`; put `n := a` and
   `m := b - 1`.  Treat the zero carrier separately with `n = m = 0`.
2. Descend from `m` to `n`.  At `p`, use the short complex with
   `Subobject.ofLE (I.filtration.obj (p + 1)) (I.filtration.obj p) _` and
   `gradedPieceπ I p`.  `ShortComplex.exact_cokernel` and
   `ShortComplex.ShortExact.splittingOfInjective` apply because the induction
   hypothesis makes the `(p+1)`-step a finite biproduct of injectives
   (`Injective` is closed under finite biproducts in
   `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`).  Use
   `ShortComplex.Splitting.isoBinaryBiproduct` for the next splitting.
3. Compose these splittings and the finite-biproduct associativity/reindexing
   isomorphisms to obtain `e`.  For each `p`, split into `p <= n`,
   `n < p <= m`, and `m < p`; antitonicity handles the outer cases and the
   recursive splitting identifies the middle step with exactly the summands
   whose indices are at least `p`.  Prove the subobject equality after
   composing both arrows with `e.inv`; `Subobject.exists_iso_map` and
   `Subobject.underlyingIso` are the normalization lemmas used here.
-/
theorem split_filtered_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (hfinite : I.IsFinite)
    (hgraded : ∀ p : ℤ, Injective (gradedPiece I p)) :
    ∃ n m : ℤ,
      n ≤ m ∧ I.filtration.obj n = ⊤ ∧
        I.filtration.obj (m + 1) = ⊥ ∧
        ∃ e : I.carrier ≅ finiteGradedSum I n m,
          IsGradedDirectSumFiltration I n m e := by
  sorry

/-! ## Exercise 30.2 and the terminology immediately following it -/

/-- A filtered morphism whose associated graded morphism is a monomorphism in
the abelian category of underlying objects. -/
def GradedInjectiveMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (α : A ⟶ B) : Prop :=
  ∀ p : ℤ, Mono (gradedPieceMap α p)

/-- The strict monomorphisms used in the filtered category. -/
def StrictMonomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (α : A ⟶ B) : Prop :=
  Mono α ∧ Strict α

/-- The lifting criterion for filtered injectivity. -/
/- Proof roadmap.
Forward: first prove locally that a graded monomorphism between finite
filtered objects is a strict monomorphism.  The ingredients are
`graded_piece_kernel_exact`, `graded_piece_cokernel_exact`, and
`filtered_acyclic` in `Formalization/Books/Homology/Unit19/Filtrations.lean`;
this is the reusable core of `graded_injective_iff_strict_monomorphism`
below, which cannot be referenced here because of source order.  Split `I`
with `split_filtered_injective`.  The `q`th coordinate of a filtered map to
the split object factors through `filtrationQuotient A (q + 1)`, and the
corresponding quotient map for `α` is mono.  Extend that coordinate with
`Injective.factorThru`, assemble the finite biproduct map, and transport it
back along the splitting; `Injective.comp_factorThru` proves the equation.

Reverse: fix a mono `u : X ⟶ Y` and `g : X ⟶ gradedPiece I p`.  Pull back the
extension `F^(p+1)I ⟶ F^p I ⟶ gr^p I` along `g`, push it out along `u`, and
insert the resulting extension as the `p`th step of two finite filtered
objects `A ⟶ B`.  Their graded map is the identity away from `p` and `u` at
`p`.  Apply the assumed lift to the canonical `A ⟶ I` and pass to the `p`th
graded piece.  This gives the required extension `Y ⟶ gradedPiece I p`.
Use `filtered_pullback_exists`, `filtered_pushout_exists`,
`filtered_pushout_preserves_strict`, and
`graded_piece_subobject_short_exact` from Homology Unit 19; finiteness follows
from the unchanged top and bottom steps.  Finish with the defining
`Injective.factorThru` criterion from
`Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`.
-/
theorem filtered_injective_iff_lifting
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (hfinite : I.IsFinite) :
    (∀ p : ℤ, Injective (gradedPiece I p)) ↔
      ∀ {A B : FilteredObject C} (α : A ⟶ B),
        A.IsFinite → B.IsFinite → GradedInjectiveMorphism α →
          ∀ γ : A ⟶ I, ∃ β : B ⟶ I, α ≫ β = γ := by
  sorry

/-- For finite filtrations, injectivity of the associated graded morphism is
equivalent to strict monomorphy in the filtered category. -/
theorem graded_injective_iff_strict_monomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : FilteredObject C} (α : A ⟶ B)
    (hfiniteA : A.IsFinite) (hfiniteB : B.IsFinite) :
    GradedInjectiveMorphism α ↔ StrictMonomorphism α := by
  rw [GradedInjectiveMorphism, StrictMonomorphism]
  have strict_to_graded :
      ∀ {X Y : FilteredObject C} (f : X ⟶ Y),
        Mono f → Strict f → ∀ p : ℤ, Mono (gradedPieceMap f p) := by
    intro X Y f hmono hs p
    let : Mono f := hmono
    have hS := graded_piece_kernel_exact f p hs
    have hK : IsZero (filteredKernel f) :=
      KernelFork.IsLimit.isZero_of_mono (filteredKernelFork_isLimit f)
    let e := hK.iso (zeroFilteredObject_isZero (C := C))
    have eC : (filteredKernel f).carrier ≅
        (zeroFilteredObject (C := C)).carrier :=
      { hom := e.hom.hom
        inv := e.inv.hom
        hom_inv_id := by
          have h := congrArg FilteredHom.hom e.hom_inv_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h
        inv_hom_id := by
          have h := congrArg FilteredHom.hom e.inv_hom_id
          simpa only [filteredHom_comp_hom, filteredHom_id_hom] using h }
    have hKC : IsZero (filteredKernel f).carrier :=
      IsZero.of_iso (isZero_zero C) eC
    have hstep : IsZero ((filteredKernel f).filtration.obj p : C) :=
      IsZero.of_mono ((filteredKernel f).filtration.obj p).arrow hKC
    have hpiece : IsZero (gradedPiece (filteredKernel f) p) := by
      let j := (filteredKernel f).filtration.obj (p + 1)
      let k := (filteredKernel f).filtration.obj p
      let : Epi (Subobject.ofLE j k
          ((filteredKernel f).filtration.antitone (by omega))) := hstep.epi _
      exact isZero_cokernel_of_epi _
    have hfzero : gradedPieceMap (filteredKernelι f) p = 0 :=
      hpiece.eq_zero_of_src _
    exact ((filteredKernelGradedShortComplex f p).exact_iff_mono hfzero).mp hS
  constructor
  · intro h
    have hKιmono : Mono (filteredKernelι α) := by
      apply (filtered_mono_iff_underlying_mono (filteredKernelι α)).2
      change Mono (Subobject.mk (kernel.ι α.hom)).arrow
      infer_instance
    have hKιstrict : Strict (filteredKernelι α) := by
      exact strict_induced_iff (Subobject.mk (kernel.ι α.hom))
    have hKιgraded : ∀ p : ℤ,
        Mono (gradedPieceMap (filteredKernelι α) p) :=
      strict_to_graded (filteredKernelι α) hKιmono hKιstrict
    have hKfinite : (filteredKernel α).IsFinite := by
      rcases hfiniteA with ⟨n, m, hn, hm⟩
      refine ⟨n, m, ?_, ?_⟩
      · dsimp [filteredKernel, inducedFilteredObject, inducedFiltration]
        change (Subobject.pullback (Subobject.mk (kernel.ι α.hom)).arrow).obj
          (A.filtration.obj n) = ⊤
        rw [hn]
        exact Subobject.pullback_top _
      · dsimp [filteredKernel, inducedFilteredObject, inducedFiltration]
        change (Subobject.pullback (Subobject.mk (kernel.ι α.hom)).arrow).obj
          (A.filtration.obj m) = ⊥
        rw [hm]
        apply le_antisymm
        · apply Subobject.le_of_factors
          apply (Subobject.bot_factors_iff_zero _).2
          apply (cancel_mono (Subobject.mk (kernel.ι α.hom)).arrow).1
          rw [← (Subobject.isPullback (Subobject.mk (kernel.ι α.hom)).arrow
            (⊥ : Subobject A.carrier)).w]
          simp
        · exact bot_le
    have hKgrzero : ∀ p : ℤ, IsZero (gradedPiece (filteredKernel α) p) := by
      intro p
      have hzero : gradedPieceMap (filteredKernelι α) p = 0 := by
        apply (cancel_mono (gradedPieceMap α p)).1
        rw [zero_comp]
        exact (filteredKernelGradedShortComplex α p).zero
      let : Mono (gradedPieceMap (filteredKernelι α) p) := hKιgraded p
      exact IsZero.of_mono_eq_zero _ hzero
    let Z := zeroFilteredObject (C := C)
    let f : Z ⟶ filteredKernel α := 0
    let g : filteredKernel α ⟶ Z := 0
    have hfg : f ≫ g = 0 := by simp [f, g]
    have hZfinite : Z.IsFinite := by
      refine ⟨0, 0, ?_, ?_⟩
      · change Subobject.mk (𝟙 Z.carrier) = ⊤
        exact Subobject.mk_eq_top_of_isIso _
      · change Subobject.mk (𝟙 Z.carrier) = ⊥
        apply (Subobject.mk_eq_bot_iff_zero).2
        exact (isZero_zero C).eq_of_src _ _
    have hgradedZ : ∀ p : ℤ,
        (gradedPieceComplex f g hfg p).Exact := by
      intro p
      have hmapf : gradedPieceMap f p = 0 := by
        let : (gradedPieceFunctor (C := C) p).Additive :=
          gradedPieceFunctor_is_additive p
        change (gradedPieceFunctor (C := C) p).map f = 0
        exact (gradedPieceFunctor (C := C) p).map_zero Z (filteredKernel α)
      have hm : Mono (gradedPieceMap g p) := (hKgrzero p).mono _
      exact ((gradedPieceComplex f g hfg p).exact_iff_mono hmapf).2 hm
    have hzero_exact :=
      (filtered_acyclic f g hfg hZfinite hKfinite hZfinite hgradedZ).2.2.2.2.2
    have hmono_g : Mono g.hom := by
      have hzcomp : f.hom ≫ g.hom = 0 := by
        have h := congrArg FilteredHom.hom hfg
        have hz : FilteredHom.hom (0 : Z ⟶ Z) = 0 := rfl
        simpa only [filteredHom_comp_hom, hz] using h
      apply ((ShortComplex.mk f.hom g.hom hzcomp).exact_iff_mono (by
        change f.hom = 0
        change (0 : Z.carrier ⟶ (filteredKernel α).carrier) = 0
        rfl)).1
      exact hzero_exact
    have hKcarrier : IsZero (filteredKernel α).carrier :=
      IsZero.of_mono g.hom (isZero_zero C)
    have hkernel : IsZero (kernel α.hom) :=
      IsZero.of_iso hKcarrier (Subobject.underlyingIso (kernel.ι α.hom)).symm
    have hmono : Mono α := by
      apply (filtered_mono_iff_underlying_mono α).2
      exact (mono_iff_isZero_kernel α.hom).2 hkernel
    have hKgradedComplex : ∀ p : ℤ,
        (gradedPieceComplex (filteredKernelι α) α (filteredKernelι_comp α) p).Exact := by
      intro p
      have hzero : gradedPieceMap (filteredKernelι α) p = 0 := by
        apply (cancel_mono (gradedPieceMap α p)).1
        rw [zero_comp]
        exact (filteredKernelGradedShortComplex α p).zero
      exact (ShortComplex.exact_iff_mono _ hzero).2 (h p)
    have hstrict_exact :=
      filtered_acyclic (filteredKernelι α) α (filteredKernelι_comp α)
        hKfinite hfiniteA hfiniteB hKgradedComplex
    exact ⟨hmono, hstrict_exact.2.2.2.2.1⟩
  · rintro ⟨hmono, hs⟩ p
    exact strict_to_graded α hmono hs p

/-- A finite filtered object whose graded pieces are injective. -/
def IsFilteredInjective
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) : Prop :=
  I.IsFinite ∧ ∀ p : ℤ, Injective (gradedPiece I p)

/-- The full subcategory of filtered objects with finite filtration. -/
def finiteFilteredProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (FilteredObject C) :=
  fun I => I.IsFinite

/-- `Fil^f(C)`, the full subcategory of finite filtered objects. -/
abbrev FiniteFilteredObject
    (C : Type u) [Category.{v} C] [Abelian C] :=
  (finiteFilteredProperty C).FullSubcategory

/-! ## Exercise 30.3 -/

/-- Every finite filtered object admits a strict monomorphism into a filtered
injective finite filtered object when the underlying category has enough
injectives. -/
/- Proof roadmap.
Choose ordered support bounds `a <= b` for `A.obj` as in the roadmap for
`split_filtered_injective`.  For every `n : finiteGradedIndex a b`, choose
`P n : InjectivePresentation (filtrationQuotient A.obj (n.1 + 1))`; the
presentation fields and their instances are in
`Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`.  Form the finite
biproduct of the `P n |>.J`, filtered by the summands with index at least
`p` (the same `biproduct.fromSubtype`/`biproduct.toSubtype` construction as
`finiteGradedSumStep` in `Unit30/Core.lean`).  The component of `α` at `n` is
the quotient projection followed by `P n |>.f`.

Check filteredness by observing that `F^p A` maps to zero in the `n`th
quotient whenever `n < p`.  The target is finite (top below `a`, bottom above
`b`) and its `n`th graded piece is isomorphic to `P n |>.J`; transport
injectivity with `Injective.of_iso`.  The diagonal component of
`gradedPieceMap α n` is the mono `P n |>.f`, so every graded map is mono.
Apply `graded_injective_iff_strict_monomorphism α A.property hI` for the
strict-monomorphism conclusion and package the target with its finiteness
proof as a `FiniteFilteredObject C`.
-/
theorem exists_strict_mono_into_filtered_injective
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A : FiniteFilteredObject C) :
    ∃ I : FiniteFilteredObject C, ∃ α : A.obj ⟶ I.obj,
    StrictMonomorphism α ∧ IsFilteredInjective I.obj := by
  sorry

/-! ## The filtered complex interfaces used in Exercise 30.4 and later -/

/-- Cochain complexes in the category of filtered objects. -/
abbrev FilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] :=
  CochainComplex (FilteredObject C) ℤ

/-- A filtered complex has finite filtration termwise. -/
def FiniteFilteredComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

/-- A cochain complex is bounded below when all terms below some degree are
zero. -/
def BoundedBelow
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    (K : CochainComplex D ℤ) : Prop :=
  ∃ n : ℤ, K.IsStrictlyGE n

/-- Every term of the complex is filtered injective. -/
def FilteredInjectiveComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, IsFilteredInjective (K.X n)

/-- The complex obtained by applying the `p`th filtration step termwise. -/
noncomputable def filtrationStepFunctor
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredObject C ⥤ C where
  obj A := filtrationStep A p
  map f := filtrationStepMap f p
  map_id := by
    intro A
    apply (cancel_mono (A.filtration.obj p).arrow).1
    simp only [filtrationStep, filtrationStepMap, Subobject.factorThru_arrow,
      filteredHom_id_hom]
    rw [Category.comp_id, Category.id_comp]
  map_comp := by
    intro A B D f g
    apply (cancel_mono (D.filtration.obj p).arrow).1
    dsimp [filtrationStepMap, filtrationStep]
    rw [Category.assoc, Subobject.factorThru_arrow, ← Category.assoc,
      Subobject.factorThru_arrow]
    rw [← Category.assoc, Subobject.factorThru_arrow]

instance filtrationStepFunctor_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    (filtrationStepFunctor (C := C) p).PreservesZeroMorphisms where
  map_zero A B := by
    apply (cancel_mono (B.filtration.obj p).arrow).1
    simp only [filtrationStep, filtrationStepFunctor, filtrationStepMap]
    rw [Subobject.factorThru_arrow]
    change
      (A.filtration.obj p).arrow ≫ (0 : A.carrier ⟶ B.carrier) =
        (0 : (A.filtration.obj p : C) ⟶ (B.filtration.obj p : C)) ≫
          (B.filtration.obj p).arrow
    simp

/-- The complex obtained by applying the `p`th filtration quotient termwise. -/
noncomputable def filtrationQuotientFunctor
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredObject C ⥤ C where
  obj A := filtrationQuotient A p
  map f := filtrationQuotientMap f p
  map_id := by
    intro A
    apply (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1
    dsimp [filtrationQuotientMap, filtrationQuotient]
    simp
  map_comp := by
    intro A B D f g
    apply (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1
    dsimp [filtrationQuotientMap, filtrationQuotient]
    simp [Category.assoc]

instance filtrationQuotientFunctor_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    (filtrationQuotientFunctor (C := C) p).PreservesZeroMorphisms where
  map_zero A B := by
    apply (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1
    dsimp [filtrationQuotientFunctor, filtrationQuotientMap, filtrationQuotient]
    rw [cokernel.π_desc]
    change
      (0 : A.carrier ⟶ B.carrier) ≫ cokernel.π (B.filtration.obj p).arrow =
        cokernel.π (A.filtration.obj p).arrow ≫ 0
    simp

/-- The `p`th associated graded complex. -/
noncomputable def filteredGradedComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ := by
  letI : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive p
  exact ((gradedPieceFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map of associated graded complexes induced by a filtered complex map. -/
noncomputable def filteredGradedComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) (p : ℤ) :
    filteredGradedComplex K p ⟶ filteredGradedComplex L p := by
  letI : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive p
  exact ((gradedPieceFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

/-- A filtered quasi-isomorphism is a quasi-isomorphism on every graded
complex. -/
def FilteredQuasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) : Prop :=
  ∀ p : ℤ, QuasiIso (filteredGradedComplexMap α p)

/-- The `p`th filtration-step complex. -/
noncomputable def filteredStepComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  ((filtrationStepFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map on the `p`th filtration-step complexes. -/
noncomputable def filteredStepComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) (p : ℤ) :
    filteredStepComplex K p ⟶ filteredStepComplex L p :=
  ((filtrationStepFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

/-- The `p`th quotient complex. -/
noncomputable def filteredQuotientComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  ((filtrationQuotientFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map on the `p`th quotient complexes. -/
noncomputable def filteredQuotientComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) (p : ℤ) :
    filteredQuotientComplex K p ⟶ filteredQuotientComplex L p :=
  ((filtrationQuotientFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

/-- Filtered acyclicity means termwise finite filtration and acyclicity of
every associated graded complex. -/
def FilteredAcyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  FiniteFilteredComplex K ∧ ∀ p : ℤ, (filteredGradedComplex K p).Acyclic

/-- The usual mapping cone, formed in the category of filtered objects. -/
noncomputable def filteredMappingCone
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) : FilteredComplex C :=
  CochainComplex.mappingCone α

/-- Forget the filtration on a filtered complex. -/
noncomputable def forgetFilteredFunctor
    {C : Type u} [Category.{v} C] [Abelian C] :
    FilteredObject C ⥤ C where
  obj A := A.carrier
  map f := f.hom
  map_id := by
    intro A
    rfl
  map_comp := by
    intro A B D f g
    rfl

instance forgetFilteredFunctor_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [Abelian C] :
    (forgetFilteredFunctor (C := C)).PreservesZeroMorphisms where
  map_zero A B := by rfl

/-- The underlying unfiltered complex of a filtered complex. -/
noncomputable def underlyingComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : CochainComplex C ℤ :=
  ((forgetFilteredFunctor (C := C)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The map of underlying complexes induced by a filtered complex map. -/
noncomputable def underlyingComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) :
    underlyingComplex K ⟶ underlyingComplex L :=
  ((forgetFilteredFunctor (C := C)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

/-- The usual quasi-isomorphism assertion for filtered complexes, obtained by
forgetting the filtration. -/
def UnderlyingQuasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L) : Prop :=
  QuasiIso (underlyingComplexMap α)

/- Shared roadmap for Exercise 30.4.
Establish three local comparison lemmas once.

* An additive functor commutes with cones via
  `CochainComplex.mappingCone.mapHomologicalComplexIso` in
  `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`.  Specialize
  this to `gradedPieceFunctor`, `filtrationStepFunctor`,
  `filtrationQuotientFunctor`, and `forgetFilteredFunctor`.
* For finite filtered terms, graded exactness of the three-term differential
  at every cochain degree implies step, quotient, and underlying exactness by
  `filtered_acyclic` in Homology Unit 19 and
  `HomologicalComplex.acyclic_iff` in
  `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`.
* Build the termwise short exact complexes
  `F^(p+1)K ⟶ F^p K ⟶ gr^p K` and
  `gr^p K ⟶ K/F^(p+1)K ⟶ K/F^p K`.
  `HomologicalComplex.shortExact_iff_degreewise_shortExact` and
  `ShortComplex.exact_cokernel` prove short exactness.  For a morphism of
  these sequences,
  `HomologicalComplex.HomologySequence.quasiIso_τ₃` in
  `Mathlib/Algebra/Homology/HomologySequenceLemmas.lean` transfers two
  quasi-isomorphisms to the third; use the opposite sequence for `τ₁`.

Also record locally the standard cone criterion
`QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic`.  Prove it degreewise
from the mapping-cone homology sequence using `quasiIso_iff` and
`HomologicalComplex.exactAt_iff_isZero_homology`; do not replace it by a
one-way cone lemma.
-/

/-! ## Exercise 30.4 -/

/-- The four equivalent descriptions of a filtered quasi-isomorphism for
bounded-below finite filtered complexes. -/
/- Proof roadmap.
Use the four shared comparison lemmas above.  The cone comparison turns
`FilteredQuasiIso α` into graded acyclicity of `filteredMappingCone α`;
finite filtration of each cone term follows by taking the min/max of the
bounds for its two biproduct summands.  Applying `filtered_acyclic` at every
cochain degree gives the step and quotient implications.  Conversely, the
two termwise short exact sequences transfer the step family, respectively
the quotient family, back to the graded family.  The cone condition returns
the graded family directly by the cone criterion.  Prove all three iff
components separately; proving only the reverse implication from their
conjunction would not establish the advertised four-way equivalence.
-/
theorem filtered_quasiIso_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L)
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hKbelow : BoundedBelow K) (hLbelow : BoundedBelow L) :
    (FilteredQuasiIso α ↔
      ∀ p : ℤ, QuasiIso (filteredStepComplexMap α p)) ∧
    (FilteredQuasiIso α ↔
      ∀ p : ℤ, QuasiIso (filteredQuotientComplexMap α p)) ∧
    (FilteredQuasiIso α ↔ FilteredAcyclic (filteredMappingCone α)) := by
  sorry

/-- A filtered quasi-isomorphism between bounded-below finite filtered
complexes is a usual quasi-isomorphism. -/
/- Proof roadmap.
Take the cone-acyclic component of `filtered_quasiIso_iff α ...` and unfold
`FilteredAcyclic`.  At every degree, apply the underlying-exactness component
of Homology Unit 19's `filtered_acyclic` to the three consecutive cone terms;
this proves `(underlyingComplex (filteredMappingCone α)).Acyclic`.  Transport
it across `CochainComplex.mappingCone.mapHomologicalComplexIso α
(forgetFilteredFunctor (C := C))`, then use the shared cone criterion in the
reverse direction to obtain `QuasiIso (underlyingComplexMap α)`.  The two
bounded-below hypotheses are used only to invoke `filtered_quasiIso_iff`.
-/
theorem filtered_quasiIso_is_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L)
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hKbelow : BoundedBelow K) (hLbelow : BoundedBelow L)
    (hα : FilteredQuasiIso α) : UnderlyingQuasiIso α := by
  sorry

/-! ## Exercise 30.5 -/

/-- The complex concentrated in degree zero at a filtered object. -/
noncomputable def filteredObjectSingle
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : FilteredObject C) : FilteredComplex C :=
  (Formalization.Books.Homology.Unit13.cochainComplexSingle
    (FilteredObject C)).obj A

/-- A finite filtered object admits a nonnegative filtered injective
resolution. -/
/- Proof roadmap.
Construct successors recursively.  Start with the strict mono
`u 0 : A.obj ⟶ J 0` supplied by
`exists_strict_mono_into_filtered_injective`; set
`Q 0 := filteredCokernel (u 0)`.  Given `Q n`, choose a strict mono
`u (n+1) : Q n ⟶ J (n+1)` and put
`Q (n+1) := filteredCokernel (u (n+1))`.  The quotient-filtration formula
shows every `Q n` is finite using the bounds of `J n`.

Define the complex to be zero in negative degrees and `J n` in degree
`n : ℕ`; its differential is `filteredCokernelπ (u n) ≫ u (n+1)`.
`filteredCokernel_comp` gives `d ≫ d = 0`.  The augmentation is `u 0` in
degree zero and zero elsewhere; construct it with the fields of
`HomologicalComplex.Hom` (the single-complex component simplifications are
in `Mathlib/Algebra/Homology/Single.lean`).

For every filtration index `p`,
`graded_piece_cokernel_exact` and strictness of `u n` identify the graded
complex as the ordinary exact injective resolution built from these
cokernels.  Use `HomologicalComplex.acyclic_iff`/`quasiIso_iff` to prove the
graded augmentation is a quasi-isomorphism.  Finiteness, strict support at
zero, and termwise `IsFilteredInjective` follow directly from the recursive
choices (the negative zero terms use `Injective.zero_injective`).
-/
theorem exists_filtered_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (A : FiniteFilteredObject C) :
    ∃ I : FilteredComplex C,
      FiniteFilteredComplex I ∧
      I.IsStrictlyGE 0 ∧
      FilteredInjectiveComplex I ∧
      ∃ α : filteredObjectSingle A.obj ⟶ I, FilteredQuasiIso α := by
  sorry

/-! ## Exercise 30.6 -/

/-- A bounded-below finite filtered complex admits a bounded-below complex
with filtered injective terms, connected to it by a filtered
quasi-isomorphism; the comparison can be chosen degreewise strict. -/
/- Proof roadmap.
Choose `a` with `K.IsStrictlyGE a` and shift indices so the construction is
first-quadrant.  For every degree `r`, use the canonical finite filtered
objects `filteredKernel (K.d r (r+1))` and
`filteredCoimage (K.d r (r+1))`; their graded short sequence is short exact
by `graded_piece_kernel_coimage_short_exact` in Homology Unit 19.  Resolve
both objects with `exists_filtered_injective_resolution`.  Prove, as local
shared claims, (i) the comparison theorem for a map of objects by successive
uses of `filtered_injective_iff_lifting`, and (ii) the horseshoe construction
for that short exact sequence, with middle row the termwise filtered
biproduct.  These give a row resolution `R r` and maps `R r ⟶ R (r+1)` whose
composites vanish.

Package the rows as `DoubleComplex (FilteredObject C)` and totalize it with
`TotalComplexPresentation` and
`totalComplexPresentation_exists_of_finite_support` from
`Formalization/Books/Homology/Unit18/DoubleComplexes.lean`; finite support
comes from `a` and the nonnegative row resolutions.  For each `p`, map this
double complex by `gradedPieceFunctor (C := C) p`.  Its columns satisfy
`DoubleComplexResolutionHypotheses`, so
`doubleComplex_gives_resolution` from
`Formalization/Books/Homology/Unit25/DoubleComplexes.lean` proves the
totalized graded map is a quasi-isomorphism.  Use
`CochainComplex.mappingCone.mapHomologicalComplexIso`-style component
comparisons to identify this map with `filteredGradedComplexMap α p`.

Each total term is a finite biproduct of filtered-injective entries, hence is
finite and has injective graded pieces.  The horseshoe augmentations are
strict monos; finite biproducts preserve that property, giving
`StrictMonomorphism (α.f n)`.  The same diagonal-support estimate gives the
claimed lower bound.
-/
theorem exists_filtered_injective_resolution_of_complex
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {K : FilteredComplex C}
    (hKfinite : FiniteFilteredComplex K) (hKbelow : BoundedBelow K) :
    ∃ I : FilteredComplex C,
      FiniteFilteredComplex I ∧ BoundedBelow I ∧
      FilteredInjectiveComplex I ∧
      ∃ α : K ⟶ I,
        FilteredQuasiIso α ∧ ∀ n : ℤ, StrictMonomorphism (α.f n) := by
  sorry

/-! ## Exercise 30.7 -/

/- Shared roadmap for Exercises 30.7--30.9.
First isolate the relative extension operation.  If `u : A ⟶ B` is a strict
mono between finite filtered objects and `J` is filtered injective, obtain
`GradedInjectiveMorphism u` from
`graded_injective_iff_strict_monomorphism`, then apply the forward direction
of `filtered_injective_iff_lifting J hJ.1` to `hJ.2`.  This is the filtered
analogue of `Injective.factorThru` and should be a small private helper.

The second shared helper is the relative Hom-complex boundary lemma: if `M`
is finite filtered acyclic and `J` is bounded below and termwise filtered
injective, every `z : Cocycle M J r` is `δ (r-1) r w` for some
`w : Cochain M J (r-1)`.  Choose a lower bound for `J` and construct the
components of `w` by induction on `n - bound`.  At each successor,
`HomologicalComplex.acyclic_iff` and Homology Unit 19's `filtered_acyclic`
make the relevant image inclusion a finite strict mono; extend the residual
component with the private relative extension operation.  Below the bound,
use `IsZero.eq_of_tgt`.  The factorization through image/coimage uses
`ShortComplex.Exact.desc`/`g_desc` from
`Mathlib/Algebra/Homology/ShortComplex/Exact.lean`; strictness transports it
to `filteredImage`.  Assemble the chosen components as a `Cochain` and prove
the boundary equation with `Cochain.ext`.  This one lemma supplies the
existence proof below and its degree-zero specialization supplies Exercise
30.8; promote it to a private declaration when implementing so the induction
is not duplicated.
-/

/-- A filtered quasi-isomorphism admits a lift into a bounded-below complex
with filtered injective terms, commuting with a prescribed map up to
cochain homotopy. -/
/- Proof roadmap.
Let `M := filteredMappingCone α`.  The cone component of
`filtered_quasiIso_iff α ...` makes `M` filtered acyclic; the cone terms and
lower bound are obtained from the two finite, bounded-below inputs by the
binary-biproduct formulas.  In the Hom complex, form the degree-one cocycle
from `CochainComplex.mappingCone.fst α` by postcomposing with `γ`
(`Cocycle.postcomp` in
`Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`).  Apply the
shared boundary lemma to write it as `δ 0 1 w` for a degree-zero cochain
`w : Cochain M I 0`.

Restrict `w` along `CochainComplex.mappingCone.inr α`; the boundary equation
says this restriction is a zero-cocycle, so `Cocycle.homOf` gives
`β : L ⟶ I`.  Restrict along `mappingCone.inl α` to get a degree `-1`
cochain from `K` to `I`.  The same equation, simplified with
`mappingCone.inl_v_fst_v`, `mappingCone.inr_f_fst_v`, and
`Cochain.δ_comp`, is exactly
`Cochain.ofHom (α ≫ β) = δ (-1) 0 h + Cochain.ofHom γ`.
Apply `(Cochain.equivHomotopy (α ≫ β) γ).symm` to obtain the required
homotopy.
-/
theorem filtered_lift_up_to_homotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L I : FilteredComplex C}
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hIfinite : FiniteFilteredComplex I)
    (hKbelow : BoundedBelow K)
    (hLbelow : BoundedBelow L)
    (hIbelow : BoundedBelow I)
    (hIinjective : FilteredInjectiveComplex I)
    (α : K ⟶ L) (hα : FilteredQuasiIso α)
    (γ : K ⟶ I) :
    ∃ β : L ⟶ I, cochainHomotopic (α ≫ β) γ := by
  sorry

/-- Under degreewise strict monomorphy, the lift in the preceding statement
can be chosen to commute exactly. -/
/- Proof roadmap.
Obtain `β₀` and a homotopy from `filtered_lift_up_to_homotopy`.  Convert the
homotopy to `h : Cochain K I (-1)` with `Cochain.equivHomotopy`.  For every
allowed pair `i + (-1) = j`, extend `h.v i j` along the finite strict mono
`α.f i` using the private relative extension helper and
`hIinjective j`; use zero for disallowed pairs.  These components define
`H : Cochain L I (-1)` and satisfy
`(Cochain.ofHom α).comp H (zero_add _) = h` by `Cochain.ext` and the helper's
factorization equation.

The coboundary `δ (-1) 0 H` is a zero-cocycle, hence corresponds via
`Cocycle.homOf` to a complex map `c : L ⟶ I`.  Set `β := β₀ - c` (or the
opposite sign, according to the normalized equation returned by
`equivHomotopy`).  Naturality of `δ` under precomposition (`δ_ofHom_comp` in
`HomComplex.lean`) and `Cochain.ofHom_injective` reduce
`α ≫ β = γ` to the homotopy equation and the defining extension equality.
-/
theorem filtered_lift_exact_of_strict
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L I : FilteredComplex C}
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hIfinite : FiniteFilteredComplex I)
    (hKbelow : BoundedBelow K)
    (hLbelow : BoundedBelow L)
    (hIbelow : BoundedBelow I)
    (hIinjective : FilteredInjectiveComplex I)
    (α : K ⟶ L) (hα : FilteredQuasiIso α)
    (hαstrict : ∀ n : ℤ, StrictMonomorphism (α.f n))
    (γ : K ⟶ I) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  sorry

/-! ## Exercise 30.8 -/

/-- A map from a bounded-below filtered acyclic complex to a bounded-below
complex with filtered injective terms is homotopic to zero.  The second
complex is named `I`, correcting the repeated `K` in the source statement. -/
/- Proof roadmap.
Apply the shared relative Hom-complex boundary lemma at degree zero to
`Cocycle.ofHom f`.  It yields `w : Cochain K I (-1)` with
`Cochain.ofHom f = δ (-1) 0 w + Cochain.ofHom 0`.  This is precisely the
subtype expected by `(Cochain.equivHomotopy f 0).symm`.  Here
`hKacyclic.1` supplies the termwise finiteness needed by the induction and
`hKacyclic.2` supplies graded acyclicity; `hKfinite`, `hIfinite`, and
`hKbelow` are intentionally harmless source-level redundancies.  Do not try
to instantiate Mathlib's ordinary `IsKInjective`: `FilteredObject C` is not
abelian and the lifting property here is only for finite strict monos.
-/
theorem filtered_acyclic_map_homotopic_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {K I : FilteredComplex C}
    (hKfinite : FiniteFilteredComplex K)
    (hIfinite : FiniteFilteredComplex I)
    (hKbelow : BoundedBelow K)
    (hIbelow : BoundedBelow I)
    (hKacyclic : FilteredAcyclic K)
    (hIinjective : FilteredInjectiveComplex I)
    (f : K ⟶ I) :
    cochainHomotopic f 0 := by
  sorry

/-! ## Exercise 30.9 -/

/-- Two lifts into a bounded-below filtered-injective complex which agree
up to homotopy after precomposition with a filtered quasi-isomorphism are
homotopic. -/
/- Proof roadmap.
Choose the two homotopies and compose the first with the symmetry of the
second using `Homotopy.trans`/`Homotopy.symm`; after
`Homotopy.equivSubZero`, this is a null-homotopy of
`α ≫ (β₁ - β₂)`.  Convert it with `Cochain.equivHomotopy` to a degree `-1`
cochain `h` satisfying the equation required by
`CochainComplex.mappingCone.desc α h (β₁ - β₂)`.  Call the resulting map
`q : filteredMappingCone α ⟶ I`; `mappingCone.inr_desc` identifies its
restriction to `L` with `β₁ - β₂`.

The cone is finite and bounded below by the biproduct bounds, and it is
filtered acyclic by the cone component of
`filtered_quasiIso_iff α ...`.  Apply
`filtered_acyclic_map_homotopic_zero` to `q`, then precompose the resulting
homotopy with `mappingCone.inr α` via `Homotopy.compLeft`.  Simplification by
`mappingCone.inr_desc` gives a homotopy from `β₁ - β₂` to zero; finally use
`Homotopy.equivSubZero.symm` to obtain `cochainHomotopic β₁ β₂`.
-/
theorem filtered_lifts_homotopic
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L I : FilteredComplex C}
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hIfinite : FiniteFilteredComplex I)
    (hKbelow : BoundedBelow K)
    (hLbelow : BoundedBelow L)
    (hIbelow : BoundedBelow I)
    (hIinjective : FilteredInjectiveComplex I)
    (α : K ⟶ L) (hα : FilteredQuasiIso α)
    (γ : K ⟶ I) (β₁ β₂ : L ⟶ I)
    (h₁ : cochainHomotopic (α ≫ β₁) γ)
    (h₂ : cochainHomotopic (α ≫ β₂) γ) :
    cochainHomotopic β₁ β₂ := by
  sorry

end Formalization.Books.Exercises.Unit30
