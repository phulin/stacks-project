import Formalization.Books.Sdga.Unit01.Core

/-! # 18. Pull and push for sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure DGPullPushData {S T : RingedSite.{u,v} R}
    (A : DGAlgebra S) (B : DGAlgebra T) where
  site_map : RingedSiteMorphism S T
  algebra_map : Prop
  functors : PullPushFunctorData A B
  homogeneous_functoriality : Prop

def dgPull {S T : RingedSite.{u,v} R} {A : DGAlgebra S} {B : DGAlgebra T}
    (F : DGPullPushData A B) := F.functors.pull

def dgPush {S T : RingedSite.{u,v} R} {A : DGAlgebra S} {B : DGAlgebra T}
    (F : DGPullPushData A B) := F.functors.push

def dgPullPreservesHomogeneousMaps {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (F : DGPullPushData A B) : Prop := F.homogeneous_functoriality

def dgPushAdjunction {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (F : DGPullPushData A B) : Prop := F.functors.adjunction

theorem lemma_adjunction_push_pull_dg_functorial
    {S T : RingedSite.{u,v} R} {A : DGAlgebra S} {B : DGAlgebra T}
    (F : DGPullPushData A B) : F.functors.adjunction := by
  sorry

end Sdga
