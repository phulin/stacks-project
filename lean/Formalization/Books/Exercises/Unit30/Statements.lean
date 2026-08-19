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
theorem split_filtered_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (hfinite : I.IsFinite)
    (hgraded : ∀ p : ℤ, Injective (gradedPiece I p)) :
    ∃ n m : ℤ,
      I.filtration.obj n = ⊤ ∧ I.filtration.obj m = ⊥ ∧
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
    letI : Mono f := hmono
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
      letI : Epi (Subobject.ofLE j k
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
        change gradedPieceMap (filteredKernelι α) p ≫ gradedPieceMap α p = 0
        exact (filteredKernelGradedShortComplex α p).zero
      letI : Mono (gradedPieceMap (filteredKernelι α) p) := hKιgraded p
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
        letI : (gradedPieceFunctor (C := C) p).Additive :=
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
        change gradedPieceMap (filteredKernelι α) p ≫ gradedPieceMap α p = 0
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
    sorry

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

/-! ## Exercise 30.4 -/

/-- The four equivalent descriptions of a filtered quasi-isomorphism for
bounded-below finite filtered complexes. -/
theorem filtered_quasiIso_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (α : K ⟶ L)
    (hKfinite : FiniteFilteredComplex K)
    (hLfinite : FiniteFilteredComplex L)
    (hKbelow : BoundedBelow K) (hLbelow : BoundedBelow L) :
    FilteredQuasiIso α ↔
      (∀ p : ℤ, QuasiIso (filteredStepComplexMap α p)) ∧
      (∀ p : ℤ, QuasiIso (filteredQuotientComplexMap α p)) ∧
      FilteredAcyclic (filteredMappingCone α) := by
  sorry

/-- A filtered quasi-isomorphism between bounded-below finite filtered
complexes is a usual quasi-isomorphism. -/
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

/-- A filtered quasi-isomorphism admits a lift into a bounded-below complex
with filtered injective terms, commuting with a prescribed map up to
cochain homotopy. -/
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
