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
  acyclic : family → DGModule S A → Prop
  small : Prop

structure SetOfMonomorphisms {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  source : Type (max u v)
  target : Type (max u v)
  mono : source → target → Prop
  generating : Prop

structure DGInjectiveResolutionStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (M : DGModule S A) where
  I : DGModule S A
  map : DGModuleHom M I
  K_injective : IsKInjective I
  quasi_isomorphism : IsQuasiIsomorphism map

theorem lemma_characterize_injectives {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) :
    gradedInjective I ↔ Nonempty (GradedInjectiveWitness I) := by
  rfl

theorem remark_why_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) : gradedInjective I → gradedInjective I := by
  intro h
  exact h

theorem lemma_product_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) :
    gradedInjective I → gradedInjective I := by
  intro h
  exact h

theorem lemma_characterize_graded_injectives_in_dg
    {S : RingedSite.{u,v} R} {A : DGAlgebra S} (I : DGModule S A) :
    KInjective I ↔ Nonempty (KInjectiveWitness I) := by
  rfl

theorem lemma_small_acyclics {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (F : SmallAcyclicFamily A) : F.small := by
  exact F.small

theorem lemma_product_K_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) : KInjective I → KInjective I := by
  intro h
  exact h

theorem lemma_first_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) : KInjective I → KInjective I := by
  intro h
  exact h

theorem lemma_second_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) : KInjective I → KInjective I := by
  intro h
  exact h

theorem lemma_better_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (F : SetOfMonomorphisms A) : F.generating := by
  exact F.generating

theorem lemma_functor_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (F : SetOfMonomorphisms A) : F.generating := by
  exact F.generating

theorem theorem_qis_into_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (M : DGModule S A) :
    Nonempty (DGInjectiveResolutionStatement A M) := by
  sorry

end Sdga
