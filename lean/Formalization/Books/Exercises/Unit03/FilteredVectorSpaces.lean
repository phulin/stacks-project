import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.LinearAlgebra.Prod

/-!
# Exercises, Chapter 3: filtered vector spaces

This file records the three assertions in the filtered-vector-space exercise.
The filtered-vector-space category and its universal-property infrastructure
are reused from Homology, Chapter 3.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Exercises.Unit03

/-! ## (1) Additivity and direct sums -/

/-- The direct sum of filtered vector spaces has the product underlying module
and the product filtration at every index. -/
def filteredVectorSpaceDirectSum
    {k : Type u} [Field k]
    (V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :
    Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (V.underlying × W.underlying)
  filtration := fun i => Submodule.prod (V.filtration i) (W.filtration i)
  decreasing := by
    intro i
    exact Submodule.prod_mono (V.decreasing i) (W.decreasing i)

theorem filteredVectorSpaceDirectSum_mem_iff
    {k : Type u} [Field k]
    (V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k)
    (i : ℤ) (x : V.underlying × W.underlying) :
    x ∈ (filteredVectorSpaceDirectSum V W).filtration i ↔
      x.1 ∈ V.filtration i ∧ x.2 ∈ W.filtration i := by
  rfl

/-- Filtered vector spaces form an additive category. -/
theorem filteredVectorSpace_additive
    (k : Type u) [Field k] :
    Nonempty
      (Formalization.Books.Homology.Unit03.AdditiveCategory
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k)) := by
  let zero : Formalization.Books.Homology.Unit03.FilteredVectorSpace k :=
    { underlying := ModuleCat.of k PUnit
      filtration := fun _ => ⊥
      decreasing := by intro i; rfl }
  let terminal : IsTerminal zero :=
    IsTerminal.ofUniqueHom (fun X => 0) (by
      intro X m
      apply Subtype.ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)
  let : HasTerminal
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
    terminal.hasTerminal
  let : ∀ {X Y : Formalization.Books.Homology.Unit03.FilteredVectorSpace k},
      HasLimit (pair X Y) := by
    intro X Y
    let fst : filteredVectorSpaceDirectSum X Y ⟶ X :=
      ⟨ModuleCat.ofHom (LinearMap.fst k X.underlying Y.underlying), by
        intro i z hz
        exact hz.1⟩
    let snd : filteredVectorSpaceDirectSum X Y ⟶ Y :=
      ⟨ModuleCat.ofHom (LinearMap.snd k X.underlying Y.underlying), by
        intro i z hz
        exact hz.2⟩
    refine ⟨⟨BinaryFan.mk fst snd, ?_⟩⟩
    exact BinaryFan.IsLimit.mk (BinaryFan.mk fst snd)
      (fun {Z} a b =>
        ⟨ModuleCat.ofHom (LinearMap.prod a.1.hom b.1.hom), by
          intro i z hz
          exact ⟨a.2 i z hz, b.2 i z hz⟩⟩)
      (fun {Z} a b => by
        apply Subtype.ext
        apply ModuleCat.hom_ext
        change (LinearMap.fst k X.underlying Y.underlying).comp
            (LinearMap.prod a.1.hom b.1.hom) = a.1.hom
        exact LinearMap.fst_prod a.1.hom b.1.hom)
      (fun {Z} a b => by
        apply Subtype.ext
        apply ModuleCat.hom_ext
        change (LinearMap.snd k X.underlying Y.underlying).comp
            (LinearMap.prod a.1.hom b.1.hom) = b.1.hom
        exact LinearMap.snd_prod a.1.hom b.1.hom)
      (fun {Z} a b m h₁ h₂ => by
        apply Subtype.ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        have h₁' : m.1 ≫
            ModuleCat.ofHom (LinearMap.fst k X.underlying Y.underlying) = a.1 :=
          congrArg (fun q : Z ⟶ X => q.1) h₁
        have h₂' : m.1 ≫
            ModuleCat.ofHom (LinearMap.snd k X.underlying Y.underlying) = b.1 :=
          congrArg (fun q : Z ⟶ Y => q.1) h₂
        have h₁'' :
            (LinearMap.fst k X.underlying Y.underlying).comp m.1.hom = a.1.hom := by
          have h := congrArg
            (fun q : Z.underlying ⟶ X.underlying => q.hom) h₁'
          change (LinearMap.fst k X.underlying Y.underlying).comp m.1.hom = a.1.hom at h
          exact h
        have h₂'' :
            (LinearMap.snd k X.underlying Y.underlying).comp m.1.hom = b.1.hom := by
          have h := congrArg
            (fun q : Z.underlying ⟶ Y.underlying => q.hom) h₂'
          change (LinearMap.snd k X.underlying Y.underlying).comp m.1.hom = b.1.hom at h
          exact h
        change m.1.hom z = (a.1.hom z, b.1.hom z)
        exact Prod.ext
          (by
            change (LinearMap.fst k X.underlying Y.underlying).comp m.1.hom z = a.1.hom z
            simpa only [LinearMap.comp_apply] using
            congrArg (fun q : Z.underlying →ₗ[k] X.underlying => q z) h₁'')
          (by
            change (LinearMap.snd k X.underlying Y.underlying).comp m.1.hom z = b.1.hom z
            simpa only [LinearMap.comp_apply] using
            congrArg (fun q : Z.underlying →ₗ[k] Y.underlying => q z) h₂''))
  let hproducts : HasBinaryProducts
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
    @hasBinaryProducts_of_hasLimit_pair
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) _ this
  let hfinite : HasFiniteProducts
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
    @hasFiniteProducts_of_has_binary_and_terminal
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) _ hproducts
      terminal.hasTerminal
  exact ⟨{ toPreadditive := inferInstance, toHasFiniteProducts := hfinite }⟩

/-! ## (2) Induced kernels and quotient cokernels -/

/-- The induced filtration on the ordinary module kernel of a filtered map. -/
def filteredVectorSpaceKernelObject
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (LinearMap.ker f.1.hom)
  filtration := fun i =>
    (V.filtration i).comap (LinearMap.ker f.1.hom).subtype
  decreasing := by
    intro i
    exact Submodule.comap_mono (V.decreasing i)

/-- The filtered inclusion of the induced kernel. -/
def filteredVectorSpaceKernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : filteredVectorSpaceKernelObject f ⟶ V :=
  ⟨ModuleCat.ofHom (LinearMap.ker f.1.hom).subtype, by
    intro i x hx
    exact hx⟩

theorem filteredVectorSpaceKernelMap_comp
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : filteredVectorSpaceKernelMap f ≫ f = 0 := by
  apply Subtype.ext
  change ModuleCat.ofHom (LinearMap.ker f.1.hom).subtype ≫ f.1 = 0
  apply ModuleCat.hom_ext
  exact LinearMap.comp_ker_subtype f.1.hom

def filteredVectorSpaceKernelFork
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : KernelFork f :=
  KernelFork.ofι (filteredVectorSpaceKernelMap f)
    (filteredVectorSpaceKernelMap_comp f)

/-- The induced-filtration kernel fork is universal. -/
theorem filteredVectorSpaceKernelFork_isLimit
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Nonempty (IsLimit (filteredVectorSpaceKernelFork f)) := by
  let kernelLift {Z : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
      (a : Z ⟶ V) (ha : a ≫ f = 0) :
      Z.underlying ⟶ (filteredVectorSpaceKernelObject f).underlying := by
    have ha' : a.1 ≫ f.1 = 0 := congrArg (fun g : Z ⟶ W => g.1) ha
    have ha'' := congrArg
      (fun g : Z.underlying ⟶ W.underlying => g.hom) ha'
    change f.1.hom.comp a.1.hom = 0 at ha''
    exact ModuleCat.ofHom
      (LinearMap.codRestrict (LinearMap.ker f.1.hom) a.1.hom (fun z => by
        rw [LinearMap.mem_ker]
        have hz := congrArg
          (fun g : Z.underlying →ₗ[k] W.underlying => g z) ha''
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz))
  refine ⟨KernelFork.IsLimit.ofι (filteredVectorSpaceKernelMap f)
    (filteredVectorSpaceKernelMap_comp f)
    (fun {Z} a ha => by
      refine ⟨kernelLift a ha, ?_⟩
      intro i z hz
      change a.1.hom z ∈ V.filtration i
      exact a.2 i z hz)
    (fun {Z} a ha => by
      apply Subtype.ext
      apply ModuleCat.hom_ext
      change (LinearMap.ker f.1.hom).subtype.comp (kernelLift a ha).hom = a.1.hom
      dsimp [kernelLift]
      rfl)
    (fun {Z} a ha m hm => by
      apply Subtype.ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      have hm' : m.1 ≫
          ModuleCat.ofHom (LinearMap.ker f.1.hom).subtype = a.1 :=
        congrArg (fun g : Z ⟶ V => g.1) hm
      have hm'' : (LinearMap.ker f.1.hom).subtype.comp m.1.hom = a.1.hom := by
        have h := congrArg
          (fun g : Z.underlying ⟶ V.underlying => g.hom) hm'
        change (LinearMap.ker f.1.hom).subtype.comp m.1.hom = a.1.hom at h
        exact h
      change (LinearMap.ker f.1.hom).subtype (m.1.hom z) = a.1.hom z
      have h := congrArg (fun g : Z.underlying →ₗ[k] V.underlying => g z) hm''
      change (LinearMap.ker f.1.hom).subtype (m.1.hom z) = a.1.hom z at h
      exact h)⟩

/-- The quotient module of a filtered map with its quotient filtration. -/
def filteredVectorSpaceCokernelObject
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (W.underlying ⧸ LinearMap.range f.1.hom)
  filtration := fun i =>
    Submodule.map (LinearMap.range f.1.hom).mkQ (W.filtration i)
  decreasing := by
    intro i
    exact Submodule.map_mono (W.decreasing i)

/-- The filtered quotient map for the quotient filtration. -/
def filteredVectorSpaceCokernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : W ⟶ filteredVectorSpaceCokernelObject f :=
  ⟨ModuleCat.ofHom (LinearMap.range f.1.hom).mkQ, by
    intro i x hx
    exact ⟨x, hx, rfl⟩⟩

theorem filteredVectorSpace_comp_cokernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : f ≫ filteredVectorSpaceCokernelMap f = 0 := by
  apply Subtype.ext
  change f.1 ≫ ModuleCat.ofHom (LinearMap.range f.1.hom).mkQ = 0
  apply ModuleCat.hom_ext
  exact LinearMap.range_mkQ_comp f.1.hom

def filteredVectorSpaceCokernelCofork
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : CokernelCofork f :=
  CokernelCofork.ofπ (filteredVectorSpaceCokernelMap f)
    (filteredVectorSpace_comp_cokernelMap f)

/-- The quotient-filtration cokernel cofork is universal. -/
theorem filteredVectorSpaceCokernelCofork_isColimit
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) :
    Nonempty (IsColimit (filteredVectorSpaceCokernelCofork f)) := by
  let range_le_ker {Z : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
      (a : W ⟶ Z) (ha : f ≫ a = 0) :
      LinearMap.range f.1.hom ≤ LinearMap.ker a.1.hom := by
    have ha' : f.1 ≫ a.1 = 0 := congrArg (fun g : V ⟶ Z => g.1) ha
    have ha'' := congrArg
      (fun g : V.underlying ⟶ Z.underlying => g.hom) ha'
    change a.1.hom.comp f.1.hom = 0 at ha''
    intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hx := congrArg
      (fun g : V.underlying →ₗ[k] Z.underlying => g x) ha''
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx
  let quotientLift {Z : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
      (a : W ⟶ Z) (ha : f ≫ a = 0) :
      (filteredVectorSpaceCokernelObject f).underlying ⟶ Z.underlying := by
    exact ModuleCat.ofHom
      ((LinearMap.range f.1.hom).liftQ a.1.hom (range_le_ker a ha))
  refine ⟨CokernelCofork.IsColimit.ofπ (filteredVectorSpaceCokernelMap f)
    (filteredVectorSpace_comp_cokernelMap f)
    (fun {Z} a ha => by
      refine ⟨quotientLift a ha, ?_⟩
      intro i x hx
      change x ∈ Submodule.map (LinearMap.range f.1.hom).mkQ
        (W.filtration i) at hx
      rcases hx with ⟨y, hy, rfl⟩
      dsimp [quotientLift]
      change (LinearMap.range f.1.hom).liftQ a.1.hom _
        ((LinearMap.range f.1.hom).mkQ y) ∈ Z.filtration i
      have hq := congrArg
        (fun g : W.underlying →ₗ[k] Z.underlying => g y)
        ((LinearMap.range f.1.hom).liftQ_mkQ a.1.hom (range_le_ker a ha))
      rw [show (LinearMap.range f.1.hom).liftQ a.1.hom _
          ((LinearMap.range f.1.hom).mkQ y) = a.1.hom y by
        simpa only [LinearMap.comp_apply] using hq]
      exact a.2 i y hy)
    (fun {Z} a ha => by
      apply Subtype.ext
      apply ModuleCat.hom_ext
      change (quotientLift a ha).hom.comp (LinearMap.range f.1.hom).mkQ = a.1.hom
      dsimp [quotientLift]
      exact (LinearMap.range f.1.hom).liftQ_mkQ a.1.hom _)
    (fun {Z} a ha m hm => by
      apply Subtype.ext
      let q : W.underlying ⟶ (filteredVectorSpaceCokernelObject f).underlying :=
        (filteredVectorSpaceCokernelMap f).1
      letI : Epi q := by
        dsimp [q, filteredVectorSpaceCokernelMap, filteredVectorSpaceCokernelObject]
        apply (ModuleCat.epi_iff_range_eq_top _).2
        simpa only [ModuleCat.hom_ofHom] using
          (Submodule.range_mkQ (LinearMap.range f.1.hom))
      apply (cancel_epi q).1
      have hm' : q ≫ m.1 = a.1 := by
        exact congrArg (fun g : W ⟶ Z => g.1) hm
      rw [hm']
      symm
      apply ModuleCat.hom_ext
      dsimp [q, quotientLift]
      exact (LinearMap.range f.1.hom).liftQ_mkQ a.1.hom
        (range_le_ker a ha))⟩

/-! ## (3) The coimage/image counterexample -/

/-- The source's filtered-vector-space example has zero kernel and cokernel,
but its identity-on-underlying-spaces map is not an isomorphism. -/
theorem filteredVectorSpace_counterexample
    (k : Type u) [Field k] :
    letI : HasKernels
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
      Formalization.Books.Homology.Unit03.filtered_vector_space_has_kernels k
    letI : HasCokernels
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
      Formalization.Books.Homology.Unit03.filtered_vector_space_has_cokernels k
    IsZero
        (kernel
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) ∧
      IsZero
        (cokernel
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) ∧
      ¬ IsIso
        (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ∧
      Nonempty
        (Abelian.coimage
            (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ≅
          Formalization.Books.Homology.Unit03.filteredLineV k) ∧
      Nonempty
        (Abelian.image
            (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ≅
          Formalization.Books.Homology.Unit03.filteredLineW k) ∧
      ¬ IsIso
        (Abelian.coimageImageComparison
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) := by
  let : HasKernels
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
    Formalization.Books.Homology.Unit03.filtered_vector_space_has_kernels k
  let : HasCokernels
      (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
    Formalization.Books.Homology.Unit03.filtered_vector_space_has_cokernels k
  let F : Formalization.Books.Homology.Unit03.filteredLineV k ⟶
      Formalization.Books.Homology.Unit03.filteredLineW k :=
    Formalization.Books.Homology.Unit03.filteredLineIdentity k
  have hsource :=
    Formalization.Books.Homology.Unit03.filtered_vector_space_counterexample k
  have hkzero : IsZero (kernel F) := hsource.1
  have hczero : IsZero (cokernel F) := hsource.2.1
  have hnotiso : ¬ IsIso F := hsource.2.2.1
  have hcoi : Nonempty
      (Abelian.coimage F ≅ Formalization.Books.Homology.Unit03.filteredLineV k) :=
    hsource.2.2.2.1
  have him : Nonempty
      (Abelian.image F ≅ Formalization.Books.Homology.Unit03.filteredLineW k) :=
    hsource.2.2.2.2.1
  have hkι : kernel.ι F = 0 := hkzero.eq_of_src _ _
  have hπ : cokernel.π F = 0 := hczero.eq_of_tgt _ _
  have hcoiπ : IsIso (Abelian.coimage.π F) := by
    change IsIso (cokernel.π (kernel.ι F))
    let g : Abelian.coimage F ⟶ Formalization.Books.Homology.Unit03.filteredLineV k :=
      cokernel.desc (kernel.ι F) (𝟙 _) (by rw [hkι, zero_comp])
    refine ⟨⟨g, ?_⟩⟩
    refine ⟨cokernel.π_desc (kernel.ι F) (𝟙 _) _, ?_⟩
    apply (cancel_epi (cokernel.π (kernel.ι F))).1
    simp [g, Category.assoc]
  have himι : IsIso (Abelian.image.ι F) := by
    change IsIso (kernel.ι (cokernel.π F))
    let g : Formalization.Books.Homology.Unit03.filteredLineW k ⟶
        Abelian.image F :=
      kernel.lift (cokernel.π F) (𝟙 _) (by rw [hπ, comp_zero])
    refine ⟨⟨g, ?_⟩⟩
    refine ⟨?_, kernel.lift_ι (cokernel.π F) (𝟙 _)
      (by rw [hπ, comp_zero])⟩
    apply (cancel_mono (kernel.ι (cokernel.π F))).1
    simp [g, Category.assoc]
  refine ⟨hkzero, hczero, hnotiso, hcoi, him, ?_⟩
  intro hcomp
  letI : IsIso (Abelian.coimageImageComparison F) := hcomp
  have hFiso : IsIso F := by
    rw [← Formalization.Books.Homology.Unit03.coimage_image_factorization F]
    infer_instance
  exact hnotiso hFiso

end Formalization.Books.Exercises.Unit03
