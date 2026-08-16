import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Pro-étale Cohomology, Chapter 1: Introduction

The introductory section is mostly expository: it states the chapter's
goals, records historical context for ℓ-adic étale cohomology, and explains
the cost of allowing non-Noetherian schemes.  Its substantive mathematical
roadmap assertion is that the small pro-étale site has enough quasi-compact
weakly contractible objects.
-/

universe u v

open CategoryTheory CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace Formalization.Books.Proetale.Unit01

/--
An object of a site is weakly contractible when sections over it lift along
every locally-surjective morphism of sheaves of sets.

`Sheaf.IsLocallySurjective` is Mathlib's canonical formulation of a
surjective morphism of sheaves for this purpose.
-/
def IsWeaklyContractible {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ {F G : Sheaf J (Type (max u v))} (f : F ⟶ G),
    Sheaf.IsLocallySurjective f →
      Function.Surjective (f.hom.app (op U))

/--
The small pro-étale site of `S` has enough quasi-compact weakly contractible
objects when every object admits a covering family whose members are
quasi-compact and weakly contractible.
-/
def HasEnoughQuasiCompactWeaklyContractibleObjects (S : Scheme.{u}) : Prop :=
  ∀ U : S.ProEt,
    ∃ (ι : Type (u + 1)) (V : ι → S.ProEt) (f : ∀ i, V i ⟶ U),
        Sieve.ofArrows V f ∈ ProEt.topology S U ∧
        ∀ i, CompactSpace (V i).left ∧
          IsWeaklyContractible (ProEt.topology S) (V i)

/--
The small pro-étale site of every scheme has enough quasi-compact weakly
contractible objects.  The construction proving this assertion belongs to
the later sections of the book.
-/
theorem smallProEtale_hasEnoughQuasiCompactWeaklyContractibleObjects
    (S : Scheme.{u}) : HasEnoughQuasiCompactWeaklyContractibleObjects S := by
  sorry

end Formalization.Books.Proetale.Unit01
