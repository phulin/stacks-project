import Formalization.Books.Sdga.Unit01.Core

/-! # 26. The derived category -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure CohomologyFunctorData {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  cohomology : ℤ → DGModule S A → Prop
  homological : Prop
  acyclic_kernel : Prop

structure DerivedLocalizationStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  localized : DerivedCategoryData S A
  quasi_isomorphisms_inverted : Prop
  acyclic_kernel : Prop
  kernel_identification : Prop

structure DerivedHomData {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M N : DGModule S A) where
  injective_resolution : DGModule S A
  resolution_map : DGModuleHom N injective_resolution
  resolution_is_quasi_isomorphism : IsQuasiIsomorphism resolution_map
  hom_comparison : Prop

structure DerivedProductsData {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  direct_sums : Prop
  products : Prop
  products_of_K_injectives : Prop

def derivedCategory {S : RingedSite.{u,v} R} (A : DGAlgebra S) :=
  DerivedCategoryData S A

structure DerivedCategoryProperties {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  localization : Prop
  kernel : Prop
  H0_description : Prop
  derived_hom : Prop
  products : Prop

theorem lemma_cohomology_homological {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (CohomologyFunctorData A) := by
  sorry

theorem lemma_acyclics {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (DerivedLocalizationStatement A) := by
  sorry

theorem lemma_qis {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f : DGModuleHom M N) :
    IsQuasiIsomorphism f ↔ Nonempty (QuasiIsomorphismWitness f) := by
  rfl

theorem lemma_kernel_localization {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (DerivedLocalizationStatement A) := by
  sorry

theorem lemma_H0_over_D {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (DerivedCategoryProperties A) := by
  sorry

theorem lemma_hom_derived {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (DerivedCategoryProperties A) := by
  sorry

theorem lemma_derived_products {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (DerivedProductsData A) := by
  sorry

theorem definition_derived_category {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    derivedCategory A = DerivedCategoryData S A := by
  rfl

end Sdga
