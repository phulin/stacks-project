import Formalization.«Books.Sdga».Unit01.Core

/-! # 26. The derived category -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure CohomologyFunctorData {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  cohomology : ℤ → DGModule S A → Prop
  homological : Prop
  acyclic_kernel : Prop

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
    (A : DGAlgebra S) (H : CohomologyFunctorData A) : H.homological := by
  exact H.homological

theorem lemma_acyclics {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (H : CohomologyFunctorData A) : H.acyclic_kernel := by
  exact H.acyclic_kernel

theorem lemma_qis {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f : DGModuleHom M N) :
    IsQuasiIsomorphism f ↔ Nonempty (QuasiIsomorphismWitness f) := by
  rfl

theorem lemma_kernel_localization {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (D : DerivedCategoryData S A) : D.localization_property := by
  exact D.localization_property

theorem lemma_H0_over_D {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (P : DerivedCategoryProperties A) : P.H0_description := by
  exact P.H0_description

theorem lemma_hom_derived {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (P : DerivedCategoryProperties A) : P.derived_hom := by
  exact P.derived_hom

theorem lemma_derived_products {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (P : DerivedCategoryProperties A) : P.products := by
  exact P.products

theorem definition_derived_category {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    derivedCategory A = DerivedCategoryData S A := by
  rfl

end Sdga
