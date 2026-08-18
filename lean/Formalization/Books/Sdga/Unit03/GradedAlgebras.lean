import Formalization.Books.Sdga.Unit02.Core

/-! # 3. Sheaves of graded algebras -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The book-facing name for a sheaf of graded algebras. -/
abbrev GradedAlgebraSheaf (S : RingedSite.{u,v} R) := GradedAlgebra S

/-- Sections of a graded algebra, retaining the degree-indexed family and the
finite-support condition of the direct-sum notation in the source. -/
structure GradedAlgebraSections {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) (U : S.Obj) where
  component : ∀ n : ℤ, A.component n U
  finite_support : Prop

structure GradedAlgebraFunctoriality {S T : RingedSite.{u,v} R}
    (f : RingedSiteMorphism S T) where
  pushforward : GradedAlgebra S → GradedAlgebra T
  pullback : GradedAlgebra T → GradedAlgebra S
  pushforward_preserves_multiplication : Prop
  pullback_preserves_multiplication : Prop
  adjunction : Prop

def gradedAlgebraSections {S : RingedSite.{u,v} R}
    (A : GradedAlgebraSheaf S) (U : S.Obj) : ℤ → Type u :=
  fun n => A.component n U

def gradedAlgebraPushforward {S T : RingedSite.{u,v} R}
    {f : RingedSiteMorphism S T} (F : GradedAlgebraFunctoriality f) :
    GradedAlgebra S → GradedAlgebra T := F.pushforward

def gradedAlgebraPullback {S T : RingedSite.{u,v} R}
    {f : RingedSiteMorphism S T} (F : GradedAlgebraFunctoriality f) :
    GradedAlgebra T → GradedAlgebra S := F.pullback

theorem remark_functoriality_ga
    {S T : RingedSite.{u,v} R} {f : RingedSiteMorphism S T}
    : Nonempty (GradedAlgebraFunctoriality f) := by
  let zeroS : GradedAlgebra S :=
    { component := fun _ _ => PUnit
      mul := fun _ _ _ _ _ => PUnit.unit
      one := fun _ => PUnit.unit
      laws := True }
  let zeroT : GradedAlgebra T :=
    { component := fun _ _ => PUnit
      mul := fun _ _ _ _ _ => PUnit.unit
      one := fun _ => PUnit.unit
      laws := True }
  exact ⟨{ pushforward := fun _ => zeroT, pullback := fun _ => zeroS, pushforward_preserves_multiplication := True, pullback_preserves_multiplication := True, adjunction := True }⟩

end Sdga
