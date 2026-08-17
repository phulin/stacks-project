import Mathlib.Algebra.Category.ModuleCat.Basic
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
  sorry

theorem is_zero_iff_initial_and_terminal
    {C : Type u} [Category.{v} C] [Preadditive C] (X : C) :
    IsZero X ↔ Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X) := by
  sorry

theorem factors_through_zero_iff
    {C : Type u} [Category.{v} C] [Preadditive C]
    {Y Z O : C} (hO : IsZero O) (f : Y ⟶ Z) :
    (∃ (a : Y ⟶ O) (b : O ⟶ Z), a ≫ b = f) ↔ f = 0 := by
  sorry

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
    (X Y : C) [HasBinaryProduct X Y] [HasBinaryCoproduct X Y] :
    (X ⨿ Y) ≅ (X ⨯ Y) := by
  letI : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryCoproduct X Y
  exact (biprod.isoCoprod X Y).symm.trans (biprod.isoProd X Y)

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
  sorry

/- Mathlib does not package the source's combined notion of an additive
   category as a separate class.  This class records exactly its definition:
   preadditivity together with finite products. -/

class AdditiveCategory (C : Type u) [Category.{v} C]
    extends Preadditive C, HasFiniteProducts C

instance additiveCategory_hasFiniteBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteProducts

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

/- Mathlib's general image API is deliberately independent of cokernels.  The
   book's image/coimage definitions are therefore exposed by these small
   abbreviations, which use exactly the displayed kernel/cokernel composites. -/

/- The source's uniqueness-up-to-unique-isomorphism note is already part of
   the `IsLimit`/`IsColimit` APIs (`conePointUniqueUpToIso` and
   `coconePointUniqueUpToIso`), so no parallel kernel or cokernel uniqueness
   construction is needed here. -/

abbrev coimage
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel (kernel.ι f)] : C :=
  cokernel (kernel.ι f)

abbrev coimageMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel (kernel.ι f)] :
    X ⟶ coimage f :=
  cokernel.π (kernel.ι f)

abbrev image
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasKernel (cokernel.π f)] : C :=
  kernel (cokernel.π f)

abbrev imageMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasKernel (cokernel.π f)] :
    image f ⟶ Y :=
  kernel.ι (cokernel.π f)

theorem coimage_map_is_epi
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel (kernel.ι f)] :
    Epi (coimageMap f) := by
  infer_instance

theorem image_map_is_mono
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasKernel (cokernel.π f)] :
    Mono (imageMap f) := by
  infer_instance

/- The canonical comparison map is the unique map from the coimage into the
   kernel of the cokernel.  Its body is the universal-property construction;
   the cancellation proof uses that a cokernel map is epi. -/

def coimageImageComparison
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f]
    [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)] :
    coimage f ⟶ image f :=
  kernel.lift (cokernel.π f)
    (cokernel.desc (kernel.ι f) f (kernel.condition f)) (by
      rw [← cancel_epi (cokernel.π (kernel.ι f))]
      simp)

theorem coimage_image_factorization
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f]
    [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)] :
    coimageMap f ≫ coimageImageComparison f ≫ imageMap f = f := by
  simp [coimageImageComparison]

theorem coimage_image_factorization_unique
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasCokernel f]
    [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)]
    (g : coimage f ⟶ image f)
    (hg : coimageMap f ≫ g ≫ imageMap f = f) :
    g = coimageImageComparison f := by
  sorry

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
  sorry

theorem filtered_vector_space_has_cokernels
    (k : Type u) [Field k] : HasCokernels (FilteredVectorSpace k) := by
  sorry

theorem filtered_vector_space_counterexample
    (k : Type u) [Field k] :
    letI : HasKernels (FilteredVectorSpace k) := filtered_vector_space_has_kernels k
    letI : HasCokernels (FilteredVectorSpace k) := filtered_vector_space_has_cokernels k
    IsZero (kernel (filteredLineIdentity k)) ∧
      IsZero (cokernel (filteredLineIdentity k)) ∧
      ¬ IsIso (filteredLineIdentity k) ∧
      Nonempty (coimage (filteredLineIdentity k) ≅ filteredLineV k) ∧
      Nonempty (image (filteredLineIdentity k) ≅ filteredLineW k) ∧
      ¬ Nonempty (Abelian (FilteredVectorSpace k)) := by
  sorry

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
  sorry

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
  sorry

theorem idempotent_cokernel_gives_kernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Q : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (p : X ⟶ Q) (hp : f ≫ p = 0)
    (hcoker : IsColimit (CokernelCofork.ofπ p hp))
    (i : Q ⟶ X)
    (hi : idempotentComplement f = p ≫ i) :
    ∃ hif : i ≫ f = 0,
      i ≫ p = 𝟙 Q ∧ Nonempty (IsLimit (KernelFork.ofι i hif)) := by
  sorry

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
  sorry

theorem complement_cokernel_gives_kernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Q : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (q : X ⟶ Q) (hq : idempotentComplement f ≫ q = 0)
    (hcoker : IsColimit (CokernelCofork.ofπ q hq))
    (j : Q ⟶ X)
    (hj : f = q ≫ j) :
    ∃ hjf : j ≫ idempotentComplement f = 0,
      j ≫ q = 𝟙 Q ∧ Nonempty (IsLimit (KernelFork.ofι j hjf)) := by
  sorry

theorem idempotent_splitting_has_all_kernels_and_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    (h : (HasKernel f ∨ HasCokernel f) ∧
      (HasKernel (idempotentComplement f) ∨
        HasCokernel (idempotentComplement f))) :
    HasKernel f ∧ HasCokernel f ∧
      HasKernel (idempotentComplement f) ∧
      HasCokernel (idempotentComplement f) := by
  sorry

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
      Nonempty (X ≅ b₁.bicone.pt) ∧
        Nonempty (X ≅ b₂.bicone.pt) ∧
        Nonempty (X ≅ b₃.bicone.pt) ∧
        Nonempty (X ≅ b₄.bicone.pt) := by
  sorry

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
  sorry

theorem split_morphism_complement_has_cokernel
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y) :
    Nonempty (IsColimit (CokernelCofork.ofπ q (by
      simp [splitComplement, Category.assoc, h]) : CokernelCofork (splitComplement j q))) := by
  sorry

theorem split_morphism_has_both_kernels_and_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y)
    (hc : HasKernel (j ≫ q) ∨ HasCokernel (j ≫ q)) :
    HasKernel (j ≫ q) ∧ HasCokernel (j ≫ q) := by
  sorry

theorem split_morphism_splitting
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y) (h : j ≫ q = 𝟙 Y)
    (hc : HasKernel (j ≫ q) ∨ HasCokernel (j ≫ q)) :
    ∃ (hk : HasKernel (j ≫ q)) (hck : HasCokernel (j ≫ q)),
      letI : HasKernel (j ≫ q) := hk
      letI : HasCokernel (j ≫ q) := hck
      ∃ (b₁ : BinaryBiproductData (kernel (j ≫ q)) Y)
        (b₂ : BinaryBiproductData (cokernel (j ≫ q)) Y),
        Nonempty (X ≅ b₁.bicone.pt) ∧ Nonempty (X ≅ b₂.bicone.pt) := by
  sorry

end Formalization.Books.Homology.Unit03
