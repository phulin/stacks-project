import Formalization.«Books.Sdga».Unit01.Core

/-! # 25. K-injective differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop := IsGradedInjective I

def KInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop := IsKInjective I

structure SmallAcyclicFamily {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  family : Type (max u v)
  object : family → DGModule S A
  acyclic : ∀ s, IsAcyclic (object s)
  detects_nonzero_acyclics : Prop

structure SetOfMonomorphisms {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  index : Type (max u v)
  source : index → DGModule S A
  target : index → DGModule S A
  mono : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (mono r)
  acyclic : Prop
  generates_injectives : Prop

structure GradedInjectiveTestFamily {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  index : Type (max u v)
  source : index → GradedModule S A
  target : index → GradedModule S A
  map : ∀ r, GradedModuleHom (source r) (target r)
  injective : ∀ r, GradedModuleHom.IsInjective (map r)
  characterizes_injectives : Prop

structure ProductGradedInjectiveData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A) where
  product : DGModule S A
  product_property : Prop

structure ProductKInjectiveData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A) where
  product : DGModule S A
  product_property : Prop

structure GradedInjectiveConsequence {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) where
  Hom_exactness : Prop

structure KInjectiveTestFamily {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  family : Type (max u v)
  source : family → DGModule S A
  target : family → DGModule S A
  map : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (map r)
  acyclic : Prop
  characterizes_K_injectives : Prop

structure BetterMonomorphismFamily {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  family : Type (max u v)
  source : family → DGModule S A
  target : family → DGModule S A
  map : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (map r)
  acyclic : Prop
  characterizes_K_injectives : Prop

structure FunctorialInjectiveStep {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  map : DGModule S A → DGModule S A
  natural_transformation : Prop
  injective_quasi_isomorphism : Prop
  factors_test_maps : Prop

structure DGInjectiveResolutionStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (M : DGModule S A) where
  I : DGModule S A
  map : DGModuleHom M I
  graded_injective : IsGradedInjective I
  K_injective : IsKInjective I
  quasi_isomorphism : IsQuasiIsomorphism map

theorem lemma_characterize_injectives {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) :
    Nonempty (GradedInjectiveTestFamily A) := by
  sorry

theorem remark_why_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) (hI : gradedInjective I) :
    Nonempty (GradedInjectiveConsequence I) := by
  sorry

theorem lemma_product_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A)
    (hI : ∀ i, gradedInjective (family i)) :
    Nonempty (ProductGradedInjectiveData family) := by
  sorry

theorem lemma_characterize_graded_injectives_in_dg
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (KInjectiveTestFamily A) := by
  sorry

theorem lemma_small_acyclics {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (SmallAcyclicFamily A) := by
  sorry

theorem lemma_product_K_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A)
    (hI : ∀ i, KInjective (family i)) :
    Nonempty (ProductKInjectiveData family) := by
  sorry

theorem lemma_first_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A)
    (hI : KInjective I ∧ gradedInjective I)
    {M M' : DGModule S A} (b : DGModuleHom M M')
    (b_injective : DGModuleHom.IsInjective b)
    (hM : IsAcyclic M) (a : DGModuleHom M I) :
    ∃ h : DGModuleHom M' I,
      ∀ n U x, h.app n U (b.app n U x) = a.app n U x := by
  sorry

theorem lemma_second_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A)
    (hI : KInjective I ∧ gradedInjective I)
    {M M' : DGModule S A} (b : DGModuleHom M M')
    (hb : IsQuasiIsomorphism b) (a : DGModuleHom M I) :
    Nonempty (GradedInjectiveConsequence I) := by
  sorry

theorem lemma_better_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (BetterMonomorphismFamily A) := by
  sorry

theorem lemma_functor_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (F : BetterMonomorphismFamily A) :
    Nonempty (FunctorialInjectiveStep A) := by
  sorry

theorem theorem_qis_into_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (M : DGModule S A) :
    Nonempty (DGInjectiveResolutionStatement A M) := by
  sorry

end Sdga
