import Formalization.«Books.Sdga».Unit01.Core

/-! # 9. Pull and push for sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure GradedPullPushData {S T : RingedSite.{u,v} R}
    (A : GradedAlgebra S) (B : GradedAlgebra T) where
  site_map : RingedSiteMorphism S T
  algebra_map : Prop
  pull : GradedModule T B → GradedModule S A
  push : GradedModule S A → GradedModule T B
  pull_on_homogeneous_maps : Prop
  push_on_homogeneous_maps : Prop
  adjunction : Prop

def gradedPull {S T : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {B : GradedAlgebra T} (F : GradedPullPushData A B) := F.pull

def gradedPush {S T : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {B : GradedAlgebra T} (F : GradedPullPushData A B) := F.push

theorem lemma_adjunction_push_pull_gr_functorial
    {S T : RingedSite.{u,v} R} {A : GradedAlgebra S} {B : GradedAlgebra T}
    (F : GradedPullPushData A B) : F.adjunction := by
  sorry

end Sdga
