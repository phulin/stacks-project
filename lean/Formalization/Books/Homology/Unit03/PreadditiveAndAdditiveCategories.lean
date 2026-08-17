import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Homological Algebra, Chapter 3: Preadditive and additive categories

The source section uses the usual preadditive terminology.  Mathlib already
provides the canonical `Preadditive` and `Functor.Additive` interfaces, as
well as binary/finite biproducts and the universal-property interfaces for
kernels and cokernels.  The declarations below expose the source assertions
through those APIs.  In particular, no parallel preadditive, direct-sum,
kernel, or cokernel structures are introduced.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped ZeroObject

universe v u

namespace Formalization.Books.Homology.Unit03

/-! ## Preadditivity, zero objects, and direct sums -/

/- The definition of a preadditive category is Mathlib's `Preadditive`; the
   definition of an additive functor is `Functor.Additive`. -/

theorem additive_functor_map_add
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} (f g : X ⟶ Y) :
    F.map (f + g) = F.map f + F.map g :=
  F.map_add

/- A preadditive category has a zero morphism between every pair of objects;
   this is the existing `HasZeroMorphisms` instance induced by `Preadditive`. -/

theorem preadditive_has_zero_morphism
    {C : Type u} [Category.{v} C] [Preadditive C] (X Y : C) :
    Nonempty (X ⟶ Y) :=
  ⟨0⟩

/- The source's three-way characterization is expressed using Mathlib's
   `IsInitial`, `IsTerminal`, and `IsZero` predicates. -/

theorem initial_terminal_id_eq_zero
    {C : Type u} [Category.{v} C] [Preadditive C] (X : C) :
    (Nonempty (IsInitial X) ↔ Nonempty (IsTerminal X)) ∧
      (Nonempty (IsInitial X) ↔ 𝟙 X = 0) := by
  constructor <;> constructor <;> first | (rintro ⟨h⟩; exact ⟨h.isZero.isTerminal⟩) | (rintro ⟨h⟩; exact ⟨h.isZero.isInitial⟩) | (rintro ⟨h⟩; exact h.isZero.eq_of_src _ _) | (intro h; exact ⟨(IsZero.iff_id_eq_zero X).mpr h |>.isInitial⟩)

theorem is_zero_iff_initial_and_terminal
    {C : Type u} [Category.{v} C] [Preadditive C] (X : C) :
    IsZero X ↔ Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X) := by
  constructor <;> first | (intro h; exact ⟨⟨h.isInitial⟩, ⟨h.isTerminal⟩⟩) | (rintro ⟨hI, hT⟩; exact hI.some.isZero)

theorem factors_through_zero_iff
    {C : Type u} [Category.{v} C] [Preadditive C]
    {Y Z O : C} (hO : IsZero O) (f : Y ⟶ Z) :
    (∃ (a : Y ⟶ O) (b : O ⟶ Z), a ≫ b = f) ↔ f = 0 := by
  constructor <;> first | (rintro ⟨a, b, hab⟩; rw [← hab, hO.eq_zero_of_tgt a, zero_comp]) | (intro hf; subst f; exact ⟨0, 0, by simp⟩)

/- Mathlib's `IsZero` is the source's zero-object definition, and
   `HasZeroObject` is its existence interface. -/

theorem finite_products_give_finite_biproducts
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteProducts C] :
    HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem finite_biproducts_give_finite_products
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C] :
    HasFiniteProducts C := by
  infer_instance

theorem finite_products_give_zero_object
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteProducts C] :
    HasZeroObject C := by
  let h : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  exact @hasZeroObject_of_hasFiniteBiproducts C _ inferInstance h

/- Mathlib's `HasBinaryBiproduct` is the source's direct-sum interface. -/

theorem binary_biproduct_of_binary_product
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.of_hasBinaryProduct X Y

theorem binary_biproduct_of_binary_coproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.of_hasBinaryCoproduct X Y

theorem binary_coproduct_of_binary_product
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryCoproduct X Y := by
  let h : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
  exact @HasBinaryBiproduct.hasColimit_pair C _ inferInstance X Y h

theorem binary_product_of_binary_coproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryProduct X Y := by
  let h : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryCoproduct X Y
  exact @HasBinaryBiproduct.hasLimit_pair C _ inferInstance X Y h

def binary_coproduct_iso_product
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryProduct X Y] :
    letI : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
    (X ⨿ Y) ≅ (X ⨯ Y) := by
  letI : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
  exact (biprod.isoCoprod X Y).symm.trans (biprod.isoProd X Y)

def binary_coproduct_iso_product_of_binary_coproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X Y : C) [HasBinaryCoproduct X Y] :
    letI : HasBinaryProduct X Y := binary_product_of_binary_coproduct X Y
    (X ⨿ Y) ≅ (X ⨯ Y) := by
  letI : HasBinaryProduct X Y := binary_product_of_binary_coproduct X Y
  exact binary_coproduct_iso_product X Y

theorem direct_sum_total
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [HasBinaryBiproduct X Y] :
    biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
  biprod.total

/- The converse characterization packages the four maps in Mathlib's
   `BinaryBicone`.  It is the source's final assertion in the direct-sum
   remark, and gives a real construction of the biproduct data. -/

def direct_sum_data_of_maps
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y Z : C}
    (i : X ⟶ Z) (j : Y ⟶ Z) (p : Z ⟶ X) (q : Z ⟶ Y)
    (hpi : i ≫ p = 𝟙 X) (hqj : j ≫ q = 𝟙 Y)
    (hpj : j ≫ p = 0) (hqi : i ≫ q = 0)
    (htotal : p ≫ i + q ≫ j = 𝟙 Z) :
    BinaryBiproductData X Y := by
  let b : BinaryBicone X Y :=
    { pt := Z
      fst := p
      snd := q
      inl := i
      inr := j
      inl_fst := hpi
      inl_snd := hqi
      inr_fst := hpj
      inr_snd := hqj }
  exact { bicone := b, isBilimit := isBinaryBilimitOfTotal b htotal }

theorem direct_sum_bicone_iff_total
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (b : BinaryBicone X Y) :
    Nonempty b.IsBilimit ↔ b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt := by
  constructor
  · rintro ⟨h⟩
    exact IsBilimit.binary_total h
  · intro h
    exact ⟨isBinaryBilimitOfTotal b h⟩

/- The source's uniqueness claims are the standard limit/c limit extensionality
   rules for a binary biproduct. -/

theorem direct_sum_hom_ext_to
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y) :
    f = g ↔ f ≫ biprod.fst = g ≫ biprod.fst ∧
      f ≫ biprod.snd = g ≫ biprod.snd := by
  constructor
  · intro h
    exact ⟨congrArg (fun t => t ≫ biprod.fst) h,
      congrArg (fun t => t ≫ biprod.snd) h⟩
  · rintro ⟨h₁, h₂⟩
    exact biprod.hom_ext f g h₁ h₂

theorem direct_sum_hom_ext_from
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z) :
    f = g ↔ biprod.inl ≫ f = biprod.inl ≫ g ∧
      biprod.inr ≫ f = biprod.inr ≫ g := by
  constructor
  · intro h
    exact ⟨congrArg (fun t => biprod.inl ≫ t) h,
      congrArg (fun t => biprod.inr ≫ t) h⟩
  · rintro ⟨h₁, h₂⟩
    exact biprod.hom_ext' f g h₁ h₂

/- Additive functors preserve the source's direct sums and zero objects. -/

theorem additive_functor_preserves_finite_biproducts
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] :
    PreservesFiniteBiproducts F := by
  infer_instance

theorem additive_functor_preserves_zero_object
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [HasZeroObject C] :
    HasZeroObject D :=
  F.hasZeroObject_of_additive

theorem additive_functor_maps_chosen_zero
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [HasZeroObject C] :
    IsZero (F.obj (0 : C)) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]

/- Mathlib does not package the source's combined notion of an additive
   category as a separate class.  This class records exactly its definition:
   preadditivity together with finite products. -/

class AdditiveCategory (C : Type u) [Category.{v} C]
    extends Preadditive C, HasFiniteProducts C

instance additiveCategory_hasFiniteBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance additiveCategory_hasZeroObject
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasZeroObject C :=
  finite_products_give_zero_object

/-! ## Kernels, cokernels, images, and coimages -/

/- `KernelFork`/`CokernelCofork` and `HasKernel`/`HasCokernel` are Mathlib's
   universal-property forms of the source's kernel and cokernel definitions. -/

theorem kernel_morphism_is_mono
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    Mono (kernel.ι f) := by
  infer_instance

theorem cokernel_morphism_is_epi
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    Epi (cokernel.π f) := by
  infer_instance

/- Mathlib's `CategoryTheory.Abelian` namespace already provides the source's
   kernel/cokernel definitions of image and coimage, together with their
   canonical maps and comparison morphism.  Use those interfaces directly
   instead of introducing chapter-local aliases that would shadow the general
   image API. -/

/- The source's uniqueness-up-to-unique-isomorphism note is already part of
   the `IsLimit`/`IsColimit` APIs (`conePointUniqueUpToIso` and
   `coconePointUniqueUpToIso`), so no parallel kernel or cokernel uniqueness
   construction is needed here. -/

theorem coimage_map_is_epi
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel (kernel.ι f)] :
    Epi (Abelian.coimage.π f) := by
  infer_instance

theorem image_map_is_mono
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasKernel (cokernel.π f)] :
    Mono (Abelian.image.ι f) := by
  infer_instance

theorem coimage_image_factorization
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f]
    [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)] :
    Abelian.coimage.π f ≫ Abelian.coimageImageComparison f ≫ Abelian.image.ι f = f :=
  Abelian.coimage_image_factorisation f

theorem coimage_image_factorization_unique
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f]
    [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)]
    (g : Abelian.coimage f ⟶ Abelian.image f)
    (hg : Abelian.coimage.π f ≫ g ≫ Abelian.image.ι f = f) :
    g = Abelian.coimageImageComparison f := by
  apply (cancel_epi (Abelian.coimage.π f)).1
  apply (cancel_mono (Abelian.image.ι f)).1
  rw [Category.assoc, Category.assoc, hg, Abelian.coimage_image_factorisation]

/- The binary biproduct kernel assertion is already present in Mathlib's
   `BinaryBicone.isLimitSndKernelFork`, with the dual cokernel assertion in
   `BinaryBicone.isColimitInrCokernelCofork`. -/

theorem direct_sum_inl_is_kernel_of_inr
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [HasBinaryBiproduct X Y] :
    Nonempty (IsLimit (BinaryBicone.sndKernelFork (BinaryBiproduct.bicone X Y))) :=
  ⟨BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit X Y)⟩

theorem direct_sum_fst_is_cokernel_of_inr
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [HasBinaryBiproduct X Y] :
    Nonempty (IsColimit (BinaryBicone.inrCokernelCofork (BinaryBiproduct.bicone X Y))) :=
  ⟨BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit X Y)⟩

/-! ## The filtered-vector-space counterexample -/

/- The source points forward to its later definition of filtered objects.  The
   following minimal concrete version is included here so the counterexample
   is usable without importing a later Homology section. -/

structure FilteredVectorSpace (k : Type u) [Field k] where
  underlying : ModuleCat.{u} k
  filtration : ℤ → Submodule k underlying
  decreasing : ∀ i : ℤ, filtration (i + 1) ≤ filtration i

def filtrationPreserving
    {k : Type u} [Field k]
    (V W : FilteredVectorSpace k) :
    AddSubgroup (V.underlying ⟶ W.underlying) where
  carrier := {f | ∀ (i : ℤ) (x : V.underlying),
    x ∈ V.filtration i → f.hom x ∈ W.filtration i}
  zero_mem' := by
    intro i x hx
    simp
  add_mem' := by
    intro f g hf hg i x hx
    simpa using (W.filtration i).add_mem (hf i x hx) (hg i x hx)
  neg_mem' := by
    intro f hf i x hx
    simpa using (W.filtration i).neg_mem (hf i x hx)

abbrev FilteredVectorSpaceHom
    {k : Type u} [Field k]
    (V W : FilteredVectorSpace k) :=
  (filtrationPreserving V W : Type _)

instance filteredVectorSpaceCategory
    (k : Type u) [Field k] : Category (FilteredVectorSpace k) where
  Hom V W := FilteredVectorSpaceHom V W
  id V :=
    ⟨𝟙 V.underlying, by
      intro i x hx
      simpa using hx⟩
  comp f g :=
    ⟨f.1 ≫ g.1, by
      intro i x hx
      simpa using g.2 i (f.1.hom x) (f.2 i x hx)⟩
  id_comp := by
    intro X Y f
    apply Subtype.ext
    simp
  comp_id := by
    intro X Y f
    apply Subtype.ext
    simp
  assoc := by
    intro W X Y Z f g h
    apply Subtype.ext
    simp

instance filteredVectorSpacePreadditive
    (k : Type u) [Field k] : Preadditive (FilteredVectorSpace k) where
  homGroup V W := AddSubgroupClass.toAddCommGroup (filtrationPreserving V W)
  add_comp := by
    intro X Y Z f g h
    apply Subtype.ext
    change (f.1 + g.1) ≫ h.1 = f.1 ≫ h.1 + g.1 ≫ h.1
    exact Preadditive.add_comp _ _ _ f.1 g.1 h.1
  comp_add := by
    intro X Y Z f g h
    apply Subtype.ext
    change f.1 ≫ (g.1 + h.1) = f.1 ≫ g.1 + f.1 ≫ h.1
    exact Preadditive.comp_add _ _ _ f.1 g.1 h.1

def filteredLineV (k : Type u) [Field k] : FilteredVectorSpace k where
  underlying := ModuleCat.of k k
  filtration := fun i => if i < 0 then ⊤ else ⊥
  decreasing := by
    intro i
    by_cases hnext : i + 1 < 0
    · have hcur : i < 0 :=
        lt_trans (Int.lt_add_one_iff.mpr (le_refl i)) hnext
      simp [hnext, hcur]
    · by_cases hcur : i < 0 <;> simp [hnext, hcur]

def filteredLineW (k : Type u) [Field k] : FilteredVectorSpace k where
  underlying := ModuleCat.of k k
  filtration := fun i => if i ≤ 0 then ⊤ else ⊥
  decreasing := by
    intro i
    by_cases hnext : i + 1 ≤ 0
    · have hcur : i ≤ 0 :=
        le_trans (Int.le_add_one (le_refl i)) hnext
      simp [hnext, hcur]
    · by_cases hcur : i ≤ 0 <;> simp [hnext, hcur]

def filteredLineIdentity (k : Type u) [Field k] :
    filteredLineV k ⟶ filteredLineW k := by
  refine ⟨𝟙 _, ?_⟩
  intro i x hx
  change (𝟙 (filteredLineV k).underlying : _ ) x ∈ _
  rw [ModuleCat.id_apply]
  by_cases hi : i < 0
  · have hi' : i ≤ 0 := le_of_lt hi
    change x ∈ (if i ≤ 0 then (⊤ : Submodule k k) else ⊥)
    rw [if_pos hi']
    trivial
  · have hx0 : x = 0 := by
      have hx' : x ∈ (⊥ : Submodule k k) := by
        change x ∈ (if i < 0 then (⊤ : Submodule k k) else ⊥) at hx
        rw [if_neg hi] at hx
        exact hx
      exact (Submodule.mem_bot k).mp hx'
    subst x
    change (0 : k) ∈ (if i ≤ 0 then (⊤ : Submodule k k) else ⊥)
    split <;> exact Submodule.zero_mem _

/- The induced-filtration and quotient-filtration constructions give kernels
   and cokernels in this concrete category.  They are recorded as the natural
   declaration-stage instances so the example can use the canonical objects. -/

theorem filtered_vector_space_has_kernels
    (k : Type u) [Field k] : HasKernels (FilteredVectorSpace k) := by
  let : HasKernels (ModuleCat k) := ModuleCat.hasKernels_moduleCat
  refine ⟨fun {V W} f => ?_⟩
  let K : FilteredVectorSpace k :=
    { underlying := kernel f.1
      filtration := fun i => (V.filtration i).comap (kernel.ι f.1).hom
      decreasing := by
        intro i
        exact Submodule.comap_mono (V.decreasing i) }
  let ι : K ⟶ V :=
    ⟨kernel.ι f.1, by
      intro i x hx
      exact hx⟩
  have hzero : ι ≫ f = 0 := by
    apply Subtype.ext
    exact kernel.condition f.1
  refine HasLimit.mk ⟨_, KernelFork.IsLimit.ofι ι hzero
    (fun {Z} a ha => by
      let ha' : a.1 ≫ f.1 = 0 := congrArg (fun g : Z ⟶ W => g.1) ha
      refine ⟨kernel.lift f.1 a.1 ha', ?_⟩
      intro i z hz
      change (kernel.lift f.1 a.1 ha').hom z ∈
        (V.filtration i).comap (kernel.ι f.1).hom
      change (kernel.ι f.1).hom ((kernel.lift f.1 a.1 ha').hom z) ∈
        V.filtration i
      have hcomp := congrArg
        (fun g : Z.underlying ⟶ V.underlying => g.hom z)
        (kernel.lift_ι f.1 a.1 ha')
      have hcomp' : (kernel.ι f.1).hom
          ((kernel.lift f.1 a.1 ha').hom z) = a.1.hom z := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hcomp
      rw [hcomp']
      exact a.2 i z hz)
    (fun {Z} a ha => by
      let ha' : a.1 ≫ f.1 = 0 := congrArg (fun g : Z ⟶ W => g.1) ha
      apply Subtype.ext
      change kernel.lift f.1 a.1 ha' ≫ kernel.ι f.1 = a.1
      exact kernel.lift_ι f.1 a.1 ha')
    (fun {Z} a ha m hm => by
      let ha' : a.1 ≫ f.1 = 0 := congrArg (fun g : Z ⟶ W => g.1) ha
      apply Subtype.ext
      apply (cancel_mono (kernel.ι f.1)).1
      change m.1 ≫ kernel.ι f.1 =
        kernel.lift f.1 a.1 ha' ≫ kernel.ι f.1
      have hm' : m.1 ≫ kernel.ι f.1 = a.1 :=
        congrArg (fun g : Z ⟶ V => g.1) hm
      rw [hm', kernel.lift_ι])⟩

theorem filtered_vector_space_has_cokernels
    (k : Type u) [Field k] : HasCokernels (FilteredVectorSpace k) := by
  let : HasCokernels (ModuleCat k) := ModuleCat.hasCokernels_moduleCat
  refine ⟨fun {V W} f => ?_⟩
  let Q : FilteredVectorSpace k :=
    { underlying := cokernel f.1
      filtration := fun i =>
        Submodule.map (cokernel.π f.1).hom (W.filtration i)
      decreasing := by
        intro i
        exact Submodule.map_mono (W.decreasing i) }
  let π : W ⟶ Q :=
    ⟨cokernel.π f.1, by
      intro i x hx
      exact ⟨x, hx, rfl⟩⟩
  have hzero : f ≫ π = 0 := by
    apply Subtype.ext
    exact cokernel.condition f.1
  refine HasColimit.mk ⟨_, CokernelCofork.IsColimit.ofπ π hzero
    (fun {Z} a ha => by
      let ha' : f.1 ≫ a.1 = 0 := congrArg (fun g : V ⟶ Z => g.1) ha
      refine ⟨cokernel.desc f.1 a.1 ha', ?_⟩
      intro i x hx
      change x ∈ Submodule.map (cokernel.π f.1).hom (W.filtration i) at hx
      rcases hx with ⟨y, hy, rfl⟩
      have hcomp := congrArg
        (fun g : W.underlying ⟶ Z.underlying => g.hom y)
        (cokernel.π_desc f.1 a.1 ha')
      have hcomp' : (cokernel.desc f.1 a.1 ha').hom
          ((cokernel.π f.1).hom y) = a.1.hom y := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hcomp
      rw [hcomp']
      exact a.2 i y hy)
    (fun {Z} a ha => by
      let ha' : f.1 ≫ a.1 = 0 := congrArg (fun g : V ⟶ Z => g.1) ha
      apply Subtype.ext
      change cokernel.π f.1 ≫ cokernel.desc f.1 a.1 ha' = a.1
      exact cokernel.π_desc f.1 a.1 ha')
    (fun {Z} a ha m hm => by
      let ha' : f.1 ≫ a.1 = 0 := congrArg (fun g : V ⟶ Z => g.1) ha
      apply Subtype.ext
      apply (cancel_epi (cokernel.π f.1)).1
      change cokernel.π f.1 ≫ m.1 =
        cokernel.π f.1 ≫ cokernel.desc f.1 a.1 ha'
      have hm' : cokernel.π f.1 ≫ m.1 = a.1 :=
        congrArg (fun g : W ⟶ Z => g.1) hm
      rw [hm', cokernel.π_desc])⟩

theorem filtered_vector_space_counterexample
    (k : Type u) [Field k] :
    letI : HasKernels (FilteredVectorSpace k) := filtered_vector_space_has_kernels k
    letI : HasCokernels (FilteredVectorSpace k) := filtered_vector_space_has_cokernels k
    IsZero (kernel (filteredLineIdentity k)) ∧
      IsZero (cokernel (filteredLineIdentity k)) ∧
      ¬ IsIso (filteredLineIdentity k) ∧
      Nonempty (Abelian.coimage (filteredLineIdentity k) ≅ filteredLineV k) ∧
      Nonempty (Abelian.image (filteredLineIdentity k) ≅ filteredLineW k) ∧
      ¬ Nonempty (Abelian (FilteredVectorSpace k)) := by
  let : HasKernels (FilteredVectorSpace k) := filtered_vector_space_has_kernels k
  let : HasCokernels (FilteredVectorSpace k) := filtered_vector_space_has_cokernels k
  let F : filteredLineV k ⟶ filteredLineW k := filteredLineIdentity k
  have : Mono F :=
    ⟨fun g h eq => by
      apply Subtype.ext
      have eq' : g.1 ≫ F.1 = h.1 ≫ F.1 := congrArg (fun t => t.1) eq
      simpa only [F, filteredLineIdentity, filteredLineV, filteredLineW,
        Category.comp_id] using eq'⟩
  have : Epi F :=
    ⟨fun g h eq => by
      apply Subtype.ext
      have eq' : F.1 ≫ g.1 = F.1 ≫ h.1 := congrArg (fun t => t.1) eq
      simpa only [F, filteredLineIdentity, filteredLineV, filteredLineW,
        Category.id_comp] using eq'⟩
  have hkzero : IsZero (kernel F) := isZero_kernel_of_mono F
  have hczero : IsZero (cokernel F) := isZero_cokernel_of_epi F
  have hnotiso : ¬ IsIso F := by
    intro hIso
    let : IsIso F := hIso
    let invF : filteredLineW k ⟶ filteredLineV k := inv F
    have hinv : invF.1.hom = LinearMap.id := by
      have h' : invF.1 ≫ F.1 = 𝟙 (filteredLineW k).underlying :=
        congrArg (fun g : filteredLineW k ⟶ filteredLineW k => g.1)
          (IsIso.inv_hom_id F)
      have h'' : invF.1 = 𝟙 (filteredLineW k).underlying := by
        simpa only [F, filteredLineIdentity, filteredLineV, filteredLineW,
          Category.comp_id] using h'
      exact congrArg (fun g => g.hom) h''
    let x : (filteredLineW k).underlying := (1 : k)
    have hmemW : x ∈ (filteredLineW k).filtration 0 := by
      change (1 : k) ∈ if (0 : ℤ) ≤ 0 then (⊤ : Submodule k k) else ⊥
      simp
    have hmemV := invF.2 0 x hmemW
    have hmemBot := hmemV
    change invF.1.hom (1 : k) ∈ (⊥ : Submodule k k) at hmemBot
    rw [hinv] at hmemBot
    have hmemBot' : (1 : k) ∈ (⊥ : Submodule k k) := by
      change (1 : k) ∈ (⊥ : Submodule k k) at hmemBot
      exact hmemBot
    exact (one_ne_zero : (1 : k) ≠ 0) ((Submodule.mem_bot k).mp hmemBot')
  have hkι : kernel.ι F = 0 := hkzero.eq_of_src _ _
  have hcoi : Nonempty
      (Abelian.coimage F ≅ filteredLineV k) := by
    change Nonempty (cokernel (kernel.ι F) ≅ filteredLineV k)
    let hcol : IsColimit (CokernelCofork.ofπ (𝟙 (filteredLineV k)) (by
        rw [hkι, zero_comp]) : CokernelCofork (kernel.ι F)) :=
      CokernelCofork.IsColimit.ofId (kernel.ι F) hkι
    exact ⟨(cokernelIsCokernel (kernel.ι F)).coconePointUniqueUpToIso hcol⟩
  have hπ : cokernel.π F = 0 := hczero.eq_of_tgt _ _
  have himlim : IsLimit (KernelFork.ofι (𝟙 (filteredLineW k)) (by
      rw [hπ, comp_zero]) : KernelFork (cokernel.π F)) := by
    refine KernelFork.IsLimit.ofι (𝟙 (filteredLineW k)) (by
      rw [hπ, comp_zero])
      (fun {_} a ha => a)
      (fun {_} a ha => by simp)
      (fun {_} a ha m hm => by simpa using hm)
  have him : Nonempty
      (Abelian.image F ≅ filteredLineW k) := by
    exact ⟨(kernelIsKernel (cokernel.π F)).conePointUniqueUpToIso himlim⟩
  have hnab : ¬ Nonempty (Abelian (FilteredVectorSpace k)) := by
    rintro ⟨hAb⟩
    let : Abelian (FilteredVectorSpace k) := hAb
    let : Preadditive (FilteredVectorSpace k) := hAb.toPreadditive
    let : IsNormalMonoCategory (FilteredVectorSpace k) := hAb.toIsNormalMonoCategory
    let : NormalMono F := normalMonoOfMono F
    have hnormal : IsIso F :=
      KernelFork.IsLimit.isIso_ι
        (KernelFork.ofι F (NormalMono.w (f := F)))
        (NormalMono.isLimit (f := F))
        (zero_of_epi_comp F (NormalMono.w (f := F)))
    exact hnotiso hnormal
  exact ⟨hkzero, hczero, hnotiso, hcoi, him, hnab⟩

/-! ## Idempotents and split morphisms -/

def idempotentComplement
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) : X ⟶ X :=
  𝟙 X - f

theorem idempotent_complement_relations
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f) :
    f ≫ idempotentComplement f = 0 ∧
      idempotentComplement f ≫ f = 0 ∧
      idempotentComplement f ≫ idempotentComplement f = idempotentComplement f := by
  simp [idempotentComplement, hf]

/- The maps obtained from the four canonical (co)kernels in the source's
   splitting lemma.  Naming them makes the direct-sum structure in the
   decomposition statement explicit rather than merely asserting an
   isomorphism of the underlying objects. -/

def idempotent_kernel_projection
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f) [HasKernel f] :
    X ⟶ kernel f :=
  kernel.lift f (idempotentComplement f)
    (idempotent_complement_relations f hf).2.1

def idempotent_cokernel_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f) [HasCokernel f] :
    cokernel f ⟶ X :=
  cokernel.desc f (idempotentComplement f)
    (idempotent_complement_relations f hf).1

def idempotent_complement_kernel_projection
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel (idempotentComplement f)] :
    X ⟶ kernel (idempotentComplement f) :=
  kernel.lift (idempotentComplement f) f
    (idempotent_complement_relations f hf).1

def idempotent_complement_cokernel_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasCokernel (idempotentComplement f)] :
    cokernel (idempotentComplement f) ⟶ X :=
  cokernel.desc (idempotentComplement f) f
    (idempotent_complement_relations f hf).2.1

/- The four clauses below are source-faithful universal-property interfaces
   for Lemma `lemma-idempotent-kernel-cokernel`.  The existential proof of the
   zero composite keeps the derived condition out of the hypotheses. -/

theorem idempotent_kernel_gives_cokernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X K : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (i : K ⟶ X) (hi : i ≫ f = 0)
    (hker : IsLimit (KernelFork.ofι i hi))
    (p : X ⟶ K)
    (hp : idempotentComplement f = p ≫ i) :
    ∃ hfp : f ≫ p = 0,
      i ≫ p = 𝟙 K ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hfp)) := by
  have hfg : f ≫ idempotentComplement f = 0 := by
    simp [idempotentComplement, hf]
  have hgi : i ≫ idempotentComplement f = i := by
    simp [idempotentComplement, hi]
  have hfp : f ≫ p = 0 := by
    apply Fork.IsLimit.hom_ext hker
    rw [KernelFork.ι_ofι, Category.assoc, ← hp, hfg, zero_comp]
  have hip : i ≫ p = 𝟙 K := by
    apply Fork.IsLimit.hom_ext hker
    rw [KernelFork.ι_ofι, Category.assoc, ← hp, hgi, Category.id_comp]
  refine ⟨hfp, hip, ?_⟩
  refine ⟨CokernelCofork.IsColimit.ofπ p hfp (fun {_} a ha => i ≫ a) ?_ ?_⟩
  · intro Z a ha
    rw [← Category.assoc, ← hp, idempotentComplement, sub_comp, Category.id_comp, ha,
      sub_zero]
  · intro Z a ha m hm
    rw [← Category.id_comp m, ← hip, Category.assoc, hm]

theorem idempotent_cokernel_gives_kernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Q : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (p : X ⟶ Q) (hp : f ≫ p = 0)
    (hcoker : IsColimit (CokernelCofork.ofπ p hp))
    (i : Q ⟶ X)
    (hi : idempotentComplement f = p ≫ i) :
    ∃ hif : i ≫ f = 0,
      i ≫ p = 𝟙 Q ∧ Nonempty (IsLimit (KernelFork.ofι i hif)) := by
  have hgf : idempotentComplement f ≫ f = 0 := by
    simp [idempotentComplement, hf]
  have hif : i ≫ f = 0 := by
    apply Cofork.IsColimit.hom_ext hcoker
    rw [CokernelCofork.π_ofπ, ← Category.assoc, ← hi, hgf, comp_zero]
  have hgp : idempotentComplement f ≫ p = p := by
    simp [idempotentComplement, hp]
  have hip : i ≫ p = 𝟙 Q := by
    apply Cofork.IsColimit.hom_ext hcoker
    rw [CokernelCofork.π_ofπ, ← Category.assoc, ← hi, hgp]
    simp
  refine ⟨hif, hip, ?_⟩
  refine ⟨KernelFork.IsLimit.ofι i hif (fun {_} a ha => a ≫ p) ?_ ?_⟩
  · intro Z a ha
    rw [Category.assoc, ← hi, idempotentComplement, comp_sub, Category.comp_id, ha,
      sub_zero]
  · intro Z a ha m hm
    rw [← Category.comp_id m, ← hip, ← Category.assoc, hm]

theorem complement_kernel_gives_cokernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X K : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (j : K ⟶ X) (hj : j ≫ idempotentComplement f = 0)
    (hker : IsLimit (KernelFork.ofι j hj))
    (q : X ⟶ K)
    (hq : f = q ≫ j) :
    ∃ hqg : idempotentComplement f ≫ q = 0,
      j ≫ q = 𝟙 K ∧
        Nonempty (IsColimit (CokernelCofork.ofπ q hqg)) := by
  have hgf : idempotentComplement f ≫ f = 0 := by
    simp [idempotentComplement, hf]
  have hjf : j ≫ f = j := by
    have h : j - j ≫ f = 0 := by
      simpa [idempotentComplement] using hj
    exact (sub_eq_zero.mp h).symm
  have hqg : idempotentComplement f ≫ q = 0 := by
    apply Fork.IsLimit.hom_ext hker
    rw [KernelFork.ι_ofι, Category.assoc, ← hq, hgf, zero_comp]
  have hjq : j ≫ q = 𝟙 K := by
    apply Fork.IsLimit.hom_ext hker
    rw [KernelFork.ι_ofι, Category.assoc, ← hq, hjf]
    simp
  refine ⟨hqg, hjq, ?_⟩
  refine ⟨CokernelCofork.IsColimit.ofπ q hqg (fun {_} a ha => j ≫ a) ?_ ?_⟩
  · intro Z a ha
    have hfa : f ≫ a = a := by
      have h : a - f ≫ a = 0 := by
        simpa [idempotentComplement] using ha
      exact (sub_eq_zero.mp h).symm
    rw [← Category.assoc, ← hq, hfa]
  · intro Z a ha m hm
    rw [← Category.id_comp m, ← hjq, Category.assoc, hm]

theorem complement_cokernel_gives_kernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Q : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (q : X ⟶ Q) (hq : idempotentComplement f ≫ q = 0)
    (hcoker : IsColimit (CokernelCofork.ofπ q hq))
    (j : Q ⟶ X)
    (hj : f = q ≫ j) :
    ∃ hjf : j ≫ idempotentComplement f = 0,
      j ≫ q = 𝟙 Q ∧ Nonempty (IsLimit (KernelFork.ofι j hjf)) := by
  have hfg : f ≫ idempotentComplement f = 0 := by
    simp [idempotentComplement, hf]
  have hjf : j ≫ idempotentComplement f = 0 := by
    apply Cofork.IsColimit.hom_ext hcoker
    rw [CokernelCofork.π_ofπ, ← Category.assoc, ← hj, hfg, comp_zero]
  have hfq : f ≫ q = q := by
    have h : q - f ≫ q = 0 := by
      simpa [idempotentComplement] using hq
    exact (sub_eq_zero.mp h).symm
  have hjq : j ≫ q = 𝟙 Q := by
    apply Cofork.IsColimit.hom_ext hcoker
    rw [CokernelCofork.π_ofπ, ← Category.assoc, ← hj, hfq]
    simp
  refine ⟨hjf, hjq, ?_⟩
  refine ⟨KernelFork.IsLimit.ofι j hjf (fun {_} a ha => a ≫ q) ?_ ?_⟩
  · intro Z a ha
    have haf : a ≫ f = a := by
      have h : a - a ≫ f = 0 := by
        simpa [idempotentComplement] using ha
      exact (sub_eq_zero.mp h).symm
    rw [Category.assoc, ← hj, haf]
  · intro Z a ha m hm
    rw [← Category.comp_id m, ← hjq, ← Category.assoc, hm]

theorem idempotent_splitting_has_all_kernels_and_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (h : (HasKernel f ∨ HasCokernel f) ∧
      (HasKernel (idempotentComplement f) ∨
        HasCokernel (idempotentComplement f))) :
    HasKernel f ∧ HasCokernel f ∧
      HasKernel (idempotentComplement f) ∧
      HasCokernel (idempotentComplement f) := by
  have kernel_to_cokernel (e : X ⟶ X) (he : e ≫ e = e)
      [HasKernel e] : HasCokernel e := by
    have hfac : idempotentComplement e =
        idempotent_kernel_projection e he ≫ kernel.ι e := by
      exact (kernel.lift_ι e (idempotentComplement e)
        (idempotent_complement_relations e he).2.1).symm
    obtain ⟨hzero, _, hcol⟩ :=
      idempotent_kernel_gives_cokernel e he (kernel.ι e) (kernel.condition e)
        (kernelIsKernel e) (idempotent_kernel_projection e he) hfac
    exact HasColimit.mk ⟨_, hcol.some⟩
  have cokernel_to_kernel (e : X ⟶ X) (he : e ≫ e = e)
      [HasCokernel e] : HasKernel e := by
    have hfac : idempotentComplement e =
        cokernel.π e ≫ idempotent_cokernel_inclusion e he := by
      exact (cokernel.π_desc e (idempotentComplement e)
        (idempotent_complement_relations e he).1).symm
    obtain ⟨hzero, _, hlim⟩ :=
      idempotent_cokernel_gives_kernel e he (cokernel.π e) (cokernel.condition e)
        (cokernelIsCokernel e) (idempotent_cokernel_inclusion e he) hfac
    exact HasLimit.mk ⟨_, hlim.some⟩
  have hfid : f ≫ f = f := hf
  have hgid : idempotentComplement f ≫ idempotentComplement f =
      idempotentComplement f :=
    (idempotent_complement_relations f hf).2.2
  rcases h with ⟨hf', hg'⟩
  have hcf : HasCokernel f :=
    match hf' with
    | Or.inl hfk => @kernel_to_cokernel f hfid hfk
    | Or.inr hfc => hfc
  have hkf : HasKernel f :=
    match hf' with
    | Or.inl hfk => hfk
    | Or.inr hfc => @cokernel_to_kernel f hfid hfc
  have hcg : HasCokernel (idempotentComplement f) :=
    match hg' with
    | Or.inl hkg => @kernel_to_cokernel (idempotentComplement f) hgid hkg
    | Or.inr hgc => hgc
  have hkg : HasKernel (idempotentComplement f) :=
    match hg' with
    | Or.inl hkg => hkg
    | Or.inr hgc => @cokernel_to_kernel (idempotentComplement f) hgid hgc
  exact ⟨hkf, hcf, hkg, hcg⟩

theorem idempotent_splitting_decompositions
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel f] [HasCokernel f]
    [HasKernel (idempotentComplement f)]
    [HasCokernel (idempotentComplement f)] :
    ∃ (b₁ : BinaryBiproductData (kernel f) (kernel (idempotentComplement f)))
      (b₂ : BinaryBiproductData (cokernel f) (kernel (idempotentComplement f)))
      (b₃ : BinaryBiproductData (kernel f) (cokernel (idempotentComplement f)))
      (b₄ : BinaryBiproductData (cokernel f) (cokernel (idempotentComplement f))),
      ∃ (e₁ : X ≅ b₁.bicone.pt) (e₂ : X ≅ b₂.bicone.pt)
        (e₃ : X ≅ b₃.bicone.pt) (e₄ : X ≅ b₄.bicone.pt),
        kernel.ι f ≫ e₁.hom = b₁.bicone.inl ∧
          kernel.ι (idempotentComplement f) ≫ e₁.hom = b₁.bicone.inr ∧
          e₁.hom ≫ b₁.bicone.fst = idempotent_kernel_projection f hf ∧
          e₁.hom ≫ b₁.bicone.snd =
            idempotent_complement_kernel_projection f hf ∧
          idempotent_cokernel_inclusion f hf ≫ e₂.hom = b₂.bicone.inl ∧
          kernel.ι (idempotentComplement f) ≫ e₂.hom = b₂.bicone.inr ∧
          e₂.hom ≫ b₂.bicone.fst = cokernel.π f ∧
          e₂.hom ≫ b₂.bicone.snd =
            idempotent_complement_kernel_projection f hf ∧
          kernel.ι f ≫ e₃.hom = b₃.bicone.inl ∧
          idempotent_complement_cokernel_inclusion f hf ≫ e₃.hom =
            b₃.bicone.inr ∧
          e₃.hom ≫ b₃.bicone.fst = idempotent_kernel_projection f hf ∧
          e₃.hom ≫ b₃.bicone.snd = cokernel.π (idempotentComplement f) ∧
          idempotent_cokernel_inclusion f hf ≫ e₄.hom = b₄.bicone.inl ∧
          idempotent_complement_cokernel_inclusion f hf ≫ e₄.hom =
            b₄.bicone.inr ∧
          e₄.hom ≫ b₄.bicone.fst = cokernel.π f ∧
          e₄.hom ≫ b₄.bicone.snd = cokernel.π (idempotentComplement f) := by
  have hfg : f ≫ idempotentComplement f = 0 :=
    (idempotent_complement_relations f hf).1
  have hgf : idempotentComplement f ≫ f = 0 :=
    (idempotent_complement_relations f hf).2.1
  have hgg : idempotentComplement f ≫ idempotentComplement f =
      idempotentComplement f :=
    (idempotent_complement_relations f hf).2.2
  have hp₁ : idempotentComplement f =
      idempotent_kernel_projection f hf ≫ kernel.ι f := by
    exact (kernel.lift_ι f (idempotentComplement f) hgf).symm
  have hp₂ : f = idempotent_complement_kernel_projection f hf ≫
      kernel.ι (idempotentComplement f) := by
    exact (kernel.lift_ι (idempotentComplement f) f hfg).symm
  have hc₁ : idempotentComplement f = cokernel.π f ≫
      idempotent_cokernel_inclusion f hf := by
    exact (cokernel.π_desc f (idempotentComplement f) hfg).symm
  have hc₂ : f = cokernel.π (idempotentComplement f) ≫
      idempotent_complement_cokernel_inclusion f hf := by
    exact (cokernel.π_desc (idempotentComplement f) f hgf).symm
  have hp₂' : idempotentComplement (idempotentComplement f) =
      idempotent_complement_kernel_projection f hf ≫
        kernel.ι (idempotentComplement f) := by
    simpa [idempotentComplement] using hp₂
  have hc₂' : idempotentComplement (idempotentComplement f) =
      cokernel.π (idempotentComplement f) ≫
        idempotent_complement_cokernel_inclusion f hf := by
    simpa [idempotentComplement] using hc₂
  obtain ⟨_, h₁, _⟩ :=
    idempotent_kernel_gives_cokernel f hf (kernel.ι f) (kernel.condition f)
      (kernelIsKernel f) (idempotent_kernel_projection f hf) hp₁
  obtain ⟨_, h₂, _⟩ :=
    idempotent_kernel_gives_cokernel (idempotentComplement f) hgg
      (kernel.ι (idempotentComplement f)) (kernel.condition (idempotentComplement f))
      (kernelIsKernel (idempotentComplement f))
      (idempotent_complement_kernel_projection f hf) hp₂'
  obtain ⟨h₃f, h₃, _⟩ :=
    idempotent_cokernel_gives_kernel f hf (cokernel.π f) (cokernel.condition f)
      (cokernelIsCokernel f) (idempotent_cokernel_inclusion f hf) hc₁
  obtain ⟨h₄g, h₄, _⟩ :=
    idempotent_cokernel_gives_kernel (idempotentComplement f) hgg
      (cokernel.π (idempotentComplement f))
      (cokernel.condition (idempotentComplement f))
      (cokernelIsCokernel (idempotentComplement f))
      (idempotent_complement_cokernel_inclusion f hf) hc₂'
  have h₁₂ : kernel.ι f ≫ idempotent_complement_kernel_projection f hf = 0 := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel (idempotentComplement f))
    calc
      (kernel.ι f ≫ idempotent_complement_kernel_projection f hf) ≫
          kernel.ι (idempotentComplement f) =
          kernel.ι f ≫
            (idempotent_complement_kernel_projection f hf ≫
              kernel.ι (idempotentComplement f)) := by simp [Category.assoc]
      _ = kernel.ι f ≫ f := by rw [← hp₂]
      _ = 0 := kernel.condition f
      _ = 0 ≫ kernel.ι (idempotentComplement f) := by simp
  have h₂₁ : kernel.ι (idempotentComplement f) ≫
      idempotent_kernel_projection f hf = 0 := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel f)
    calc
      (kernel.ι (idempotentComplement f) ≫ idempotent_kernel_projection f hf) ≫
          kernel.ι f =
          kernel.ι (idempotentComplement f) ≫
            (idempotent_kernel_projection f hf ≫ kernel.ι f) := by
              simp [Category.assoc]
      _ = kernel.ι (idempotentComplement f) ≫ idempotentComplement f := by
        rw [← hp₁]
      _ = 0 := kernel.condition (idempotentComplement f)
      _ = 0 ≫ kernel.ι f := by simp
  have h₃₂ : idempotent_cokernel_inclusion f hf ≫
      idempotent_complement_kernel_projection f hf = 0 := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel (idempotentComplement f))
    calc
      (idempotent_cokernel_inclusion f hf ≫
          idempotent_complement_kernel_projection f hf) ≫
          kernel.ι (idempotentComplement f) =
          idempotent_cokernel_inclusion f hf ≫
            (idempotent_complement_kernel_projection f hf ≫
              kernel.ι (idempotentComplement f)) := by simp [Category.assoc]
      _ = idempotent_cokernel_inclusion f hf ≫ f := by rw [← hp₂]
      _ = 0 := h₃f
      _ = 0 ≫ kernel.ι (idempotentComplement f) := by simp
  have h₂₃ : kernel.ι (idempotentComplement f) ≫ cokernel.π f = 0 := by
    have hzero := kernel.condition (idempotentComplement f)
    change kernel.ι (idempotentComplement f) ≫ (𝟙 X - f) = 0 at hzero
    rw [comp_sub, Category.comp_id] at hzero
    have hi : kernel.ι (idempotentComplement f) ≫ f =
        kernel.ι (idempotentComplement f) := (sub_eq_zero.mp hzero).symm
    rw [← hi, Category.assoc, cokernel.condition, comp_zero]
  have h₁₃ : kernel.ι f ≫ cokernel.π (idempotentComplement f) = 0 := by
    have hzero : kernel.ι f ≫ f = 0 := kernel.condition f
    have hi : kernel.ι f ≫ idempotentComplement f = kernel.ι f := by
      rw [idempotentComplement, comp_sub, Category.comp_id, hzero, sub_zero]
    rw [← hi, Category.assoc, cokernel.condition, comp_zero]
  have h₄₁ : idempotent_complement_cokernel_inclusion f hf ≫
      idempotent_kernel_projection f hf = 0 := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel f)
    calc
      (idempotent_complement_cokernel_inclusion f hf ≫
          idempotent_kernel_projection f hf) ≫ kernel.ι f =
          idempotent_complement_cokernel_inclusion f hf ≫
            (idempotent_kernel_projection f hf ≫ kernel.ι f) := by
              simp [Category.assoc]
      _ = idempotent_complement_cokernel_inclusion f hf ≫ idempotentComplement f := by
        rw [← hp₁]
      _ = 0 := h₄g
      _ = 0 ≫ kernel.ι f := by simp
  have h₃₄ : idempotent_cokernel_inclusion f hf ≫
      cokernel.π (idempotentComplement f) = 0 := by
    have hzero : idempotent_cokernel_inclusion f hf ≫ f = 0 := h₃f
    have hi : idempotent_cokernel_inclusion f hf ≫
        idempotentComplement f = idempotent_cokernel_inclusion f hf := by
      rw [idempotentComplement, comp_sub, Category.comp_id, hzero, sub_zero]
    rw [← hi, Category.assoc, cokernel.condition, comp_zero]
  have h₄₃ : idempotent_complement_cokernel_inclusion f hf ≫
      cokernel.π f = 0 := by
    have hzero : idempotent_complement_cokernel_inclusion f hf ≫
        idempotentComplement f = 0 := h₄g
    have hzero' := hzero
    change idempotent_complement_cokernel_inclusion f hf ≫ (𝟙 X - f) = 0 at hzero'
    rw [comp_sub, Category.comp_id] at hzero'
    have hi : idempotent_complement_cokernel_inclusion f hf ≫ f =
        idempotent_complement_cokernel_inclusion f hf := (sub_eq_zero.mp hzero').symm
    rw [← hi, Category.assoc, cokernel.condition, comp_zero]
  have htotal : idempotent_kernel_projection f hf ≫ kernel.ι f +
      idempotent_complement_kernel_projection f hf ≫
        kernel.ι (idempotentComplement f) = 𝟙 X := by
    calc
      _ = idempotentComplement f + f :=
        congrArg₂ (fun a b : X ⟶ X => a + b) hp₁.symm hp₂.symm
      _ = 𝟙 X := by simp [idempotentComplement]
  have htotal₂ : cokernel.π f ≫ idempotent_cokernel_inclusion f hf +
      idempotent_complement_kernel_projection f hf ≫
        kernel.ι (idempotentComplement f) = 𝟙 X := by
    calc
      _ = idempotentComplement f + f :=
        congrArg₂ (fun a b : X ⟶ X => a + b) hc₁.symm hp₂.symm
      _ = 𝟙 X := by simp [idempotentComplement]
  have htotal₃ : idempotent_kernel_projection f hf ≫ kernel.ι f +
      cokernel.π (idempotentComplement f) ≫
        idempotent_complement_cokernel_inclusion f hf = 𝟙 X := by
    calc
      _ = idempotentComplement f + f :=
        congrArg₂ (fun a b : X ⟶ X => a + b) hp₁.symm hc₂.symm
      _ = 𝟙 X := by simp [idempotentComplement]
  have htotal₄ : cokernel.π f ≫ idempotent_cokernel_inclusion f hf +
      cokernel.π (idempotentComplement f) ≫
        idempotent_complement_cokernel_inclusion f hf = 𝟙 X := by
    calc
      _ = idempotentComplement f + f :=
        congrArg₂ (fun a b : X ⟶ X => a + b) hc₁.symm hc₂.symm
      _ = 𝟙 X := by simp [idempotentComplement]
  let b₁ := direct_sum_data_of_maps
    (kernel.ι f) (kernel.ι (idempotentComplement f))
    (idempotent_kernel_projection f hf)
    (idempotent_complement_kernel_projection f hf)
    h₁ h₂ h₂₁ h₁₂ htotal
  let b₂ := direct_sum_data_of_maps
    (idempotent_cokernel_inclusion f hf) (kernel.ι (idempotentComplement f))
    (cokernel.π f) (idempotent_complement_kernel_projection f hf)
    h₃ h₂ h₂₃ h₃₂ htotal₂
  let b₃ := direct_sum_data_of_maps
    (kernel.ι f) (idempotent_complement_cokernel_inclusion f hf)
    (idempotent_kernel_projection f hf) (cokernel.π (idempotentComplement f))
    h₁ h₄ h₄₁ h₁₃ htotal₃
  let b₄ := direct_sum_data_of_maps
    (idempotent_cokernel_inclusion f hf)
    (idempotent_complement_cokernel_inclusion f hf)
    (cokernel.π f) (cokernel.π (idempotentComplement f))
    h₃ h₄ h₄₃ h₃₄ htotal₄
  refine ⟨b₁, b₂, b₃, b₄, Iso.refl X, Iso.refl X, Iso.refl X, Iso.refl X, ?_⟩
  simp [b₁, b₂, b₃, b₄, direct_sum_data_of_maps]

def splitComplement
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) : X ⟶ X :=
  𝟙 X - q ≫ j

theorem split_morphism_complement_has_kernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y) :
    Nonempty (IsLimit (KernelFork.ofι j (by
      simp only [splitComplement, comp_sub, Category.comp_id, ← Category.assoc, h,
        Category.id_comp, sub_self]) :
      KernelFork (splitComplement j q))) := by
  refine ⟨KernelFork.IsLimit.ofι j (by
    simp only [splitComplement, comp_sub, Category.comp_id, ← Category.assoc, h,
      Category.id_comp, sub_self])
    (fun {_} a ha => a ≫ q)
    (fun {_} a ha => by
      have ha' : a = (a ≫ q) ≫ j :=
        sub_eq_zero.mp (by simpa [splitComplement, Category.assoc] using ha)
      exact ha'.symm)
    (fun {_} a ha m hm => by
      rw [← Category.comp_id m, ← h, ← Category.assoc, hm])⟩

theorem split_morphism_complement_has_cokernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y) :
    Nonempty (IsColimit (CokernelCofork.ofπ q (by
      simp [splitComplement, Category.assoc, h]) : CokernelCofork (splitComplement j q))) := by
  refine ⟨CokernelCofork.IsColimit.ofπ q (by
    rw [splitComplement, sub_comp, Category.id_comp, sub_eq_zero, Category.assoc, h,
      Category.comp_id])
    (fun {_} a ha => j ≫ a)
    (fun {_} a ha => by
      exact (sub_eq_zero.mp (show a - q ≫ j ≫ a = 0 by
        simpa only [splitComplement, sub_comp, Category.id_comp, Category.assoc] using ha)).symm)
    (fun {_} a ha m hm => by
      rw [← Category.id_comp m, ← h, Category.assoc, hm])⟩

theorem split_morphism_has_both_kernels_and_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y)
    (hc : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)) :
    HasKernel (q ≫ j) ∧ HasCokernel (q ≫ j) := by
  have he : (q ≫ j) ≫ (q ≫ j) = q ≫ j := by
    rw [Category.assoc, ← Category.assoc j q j, h, Category.id_comp]
  have hkcomp : HasKernel (splitComplement j q) := by
    exact HasLimit.mk ⟨_, (split_morphism_complement_has_kernel j q h).some⟩
  have hall :=
    idempotent_splitting_has_all_kernels_and_cokernels (q ≫ j) he
      ⟨hc, Or.inl hkcomp⟩
  exact ⟨hall.1, hall.2.1⟩

theorem split_morphism_splitting
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y)
    (hc : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)) :
    ∃ (hk : HasKernel (q ≫ j)) (hck : HasCokernel (q ≫ j)),
      letI : HasKernel (q ≫ j) := hk
      letI : HasCokernel (q ≫ j) := hck
      ∃ (b₁ : BinaryBiproductData (kernel (q ≫ j)) Y)
        (b₂ : BinaryBiproductData (cokernel (q ≫ j)) Y),
        ∃ (e₁ : X ≅ b₁.bicone.pt) (e₂ : X ≅ b₂.bicone.pt),
          kernel.ι (q ≫ j) ≫ e₁.hom = b₁.bicone.inl ∧
            b₁.bicone.inr ≫ e₁.inv = j ∧
            e₁.hom ≫ b₁.bicone.snd = q ∧
            e₂.hom ≫ b₂.bicone.fst = cokernel.π (q ≫ j) ∧
            b₂.bicone.inr ≫ e₂.inv = j ∧
            e₂.hom ≫ b₂.bicone.snd = q := by
  have hb := split_morphism_has_both_kernels_and_cokernels j q h hc
  refine ⟨hb.1, hb.2, ?_⟩
  let : HasKernel (q ≫ j) := hb.1
  let : HasCokernel (q ≫ j) := hb.2
  have : Mono j :=
    ⟨fun a b hab => by
      rw [← Category.comp_id a, ← Category.comp_id b, ← h,
        ← Category.assoc, ← Category.assoc, hab]⟩
  have he : (q ≫ j) ≫ (q ≫ j) = q ≫ j := by
    rw [Category.assoc, ← Category.assoc j q j, h, Category.id_comp]
  have hce : splitComplement j q ≫ (q ≫ j) = 0 := by
    rw [splitComplement, sub_comp, Category.id_comp, he, sub_self]
  have hce' : (q ≫ j) ≫ splitComplement j q = 0 := by
    rw [splitComplement, comp_sub, Category.comp_id, he, sub_self]
  let p₁ : X ⟶ kernel (q ≫ j) :=
    kernel.lift (q ≫ j) (splitComplement j q) hce
  have hp₁ : p₁ ≫ kernel.ι (q ≫ j) = splitComplement j q := by
    exact kernel.lift_ι (q ≫ j) (splitComplement j q) hce
  have hki : kernel.ι (q ≫ j) ≫ splitComplement j q =
      kernel.ι (q ≫ j) := by
    calc
      _ = kernel.ι (q ≫ j) - kernel.ι (q ≫ j) ≫ (q ≫ j) := by
        rw [splitComplement, comp_sub, Category.comp_id]
      _ = kernel.ι (q ≫ j) := by rw [kernel.condition, sub_zero]
  have hpi₁ : kernel.ι (q ≫ j) ≫ p₁ = 𝟙 (kernel (q ≫ j)) := by
    apply Fork.IsLimit.hom_ext (kernelIsKernel (q ≫ j))
    calc
      (kernel.ι (q ≫ j) ≫ p₁) ≫ kernel.ι (q ≫ j) =
          kernel.ι (q ≫ j) ≫
            (p₁ ≫ kernel.ι (q ≫ j)) := by simp [Category.assoc]
      _ = kernel.ι (q ≫ j) ≫ splitComplement j q := by rw [hp₁]
      _ = kernel.ι (q ≫ j) := hki
      _ = (𝟙 (kernel (q ≫ j))) ≫ kernel.ι (q ≫ j) := by simp
  have hji₁ : j ≫ p₁ = 0 := by
    apply (cancel_mono (kernel.ι (q ≫ j))).1
    rw [zero_comp, Category.assoc, hp₁, splitComplement, comp_sub,
      Category.comp_id, ← Category.assoc, h, Category.id_comp, sub_self]
  have hiq : kernel.ι (q ≫ j) ≫ q = 0 := by
    apply (cancel_mono j).1
    calc
      (kernel.ι (q ≫ j) ≫ q) ≫ j =
          kernel.ι (q ≫ j) ≫ (q ≫ j) := by simp [Category.assoc]
      _ = 0 := kernel.condition (q ≫ j)
      _ = 0 ≫ j := by simp
  have htotal₁ : p₁ ≫ kernel.ι (q ≫ j) + q ≫ j = 𝟙 X := by
    rw [hp₁, splitComplement, sub_add_cancel]
  let r₂ : cokernel (q ≫ j) ⟶ X :=
    cokernel.desc (q ≫ j) (splitComplement j q) hce'
  have hπr₂ : cokernel.π (q ≫ j) ≫ r₂ = splitComplement j q := by
    exact cokernel.π_desc (q ≫ j) (splitComplement j q) hce'
  have hrπ₂ : r₂ ≫ cokernel.π (q ≫ j) = 𝟙 (cokernel (q ≫ j)) := by
    apply (cancel_epi (cokernel.π (q ≫ j))).1
    rw [← Category.assoc, hπr₂, splitComplement, sub_comp, Category.id_comp,
      cokernel.condition, sub_zero, Category.comp_id]
  have hjπ₂ : j ≫ cokernel.π (q ≫ j) = 0 := by
    have hje : j = j ≫ (q ≫ j) := by
      rw [← Category.assoc, h, Category.id_comp]
    calc
      j ≫ cokernel.π (q ≫ j) =
          (j ≫ (q ≫ j)) ≫ cokernel.π (q ≫ j) :=
        congrArg (fun a : Y ⟶ X => a ≫ cokernel.π (q ≫ j)) hje
      _ = j ≫ ((q ≫ j) ≫ cokernel.π (q ≫ j)) := by simp [Category.assoc]
      _ = 0 := by rw [cokernel.condition, comp_zero]
  have hrq₂ : r₂ ≫ q = 0 := by
    apply (cancel_epi (cokernel.π (q ≫ j))).1
    rw [← Category.assoc, hπr₂, splitComplement, sub_comp, Category.id_comp,
      Category.assoc, h, Category.comp_id, sub_self, comp_zero]
  have htotal₂ : cokernel.π (q ≫ j) ≫ r₂ + q ≫ j = 𝟙 X := by
    rw [hπr₂, splitComplement, sub_add_cancel]
  let b₁ := direct_sum_data_of_maps
    (kernel.ι (q ≫ j)) j p₁ q hpi₁ h hji₁ hiq htotal₁
  let b₂ := direct_sum_data_of_maps
    r₂ j (cokernel.π (q ≫ j)) q hrπ₂ h hjπ₂ hrq₂ htotal₂
  refine ⟨b₁, b₂, Iso.refl X, Iso.refl X, ?_⟩
  simp [b₁, b₂, direct_sum_data_of_maps]

end Formalization.Books.Homology.Unit03
