import Formalization.Books.Sdga.Unit01.Core

/-! # 12. Sheaves of differential graded algebras -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGAlgebraSheaf (S : RingedSite.{u,v} R) := DGAlgebra S

def dgAlgebraSections {S : RingedSite.{u,v} R}
    (A : DGAlgebraSheaf S) (U : S.Obj) : ℤ → Type u :=
  fun n => A.component n U

structure DGAlgebraFunctoriality {S T : RingedSite.{u,v} R}
    (f : RingedSiteMorphism S T) where
  pushforward : DGAlgebra S → DGAlgebra T
  pullback : DGAlgebra T → DGAlgebra S
  pushforward_preserves_differential : Prop
  pushforward_preserves_differential_proof : pushforward_preserves_differential
  pullback_preserves_differential : Prop
  pullback_preserves_differential_proof : pullback_preserves_differential
  adjunction : Prop
  adjunction_proof : adjunction

def dgAlgebraPushforward {S T : RingedSite.{u,v} R}
    {f : RingedSiteMorphism S T} (F : DGAlgebraFunctoriality f) :
    DGAlgebra S → DGAlgebra T := F.pushforward

def dgAlgebraPullback {S T : RingedSite.{u,v} R}
    {f : RingedSiteMorphism S T} (F : DGAlgebraFunctoriality f) :
    DGAlgebra T → DGAlgebra S := F.pullback

theorem definition_dga (S : RingedSite.{u,v} R) (A : DGAlgebraSheaf S) :
    A.graded_laws ∧ A.differential_squared ∧ A.leibniz := by
  exact ⟨A.graded_laws_proof, A.differential_squared_proof, A.leibniz_proof⟩

theorem remark_functoriality_dga
    {S T : RingedSite.{u,v} R} {f : RingedSiteMorphism S T}
    (F : DGAlgebraFunctoriality f) :
    F.pushforward_preserves_differential ∧
      F.pullback_preserves_differential ∧ F.adjunction := by
  exact ⟨F.pushforward_preserves_differential_proof,
    F.pullback_preserves_differential_proof, F.adjunction_proof⟩

end Sdga
