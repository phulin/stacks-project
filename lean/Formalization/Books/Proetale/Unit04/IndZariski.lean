import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Formalization.Books.Proetale.Unit03.LocalIsomorphisms

/-!
# Pro-étale Cohomology, Chapter 4: Ind-Zariski algebra

The source defines ind-Zariski maps as filtered colimits of local
isomorphisms.  The local-isomorphism stages below use Mathlib's canonical
`Algebra.IsLocalIso` class, and the filtered colimit is recorded in the
category of `A`-algebras so that the structure maps and the target
identification are part of the presentation.
-/

namespace Formalization.Books.Proetale.Unit04

open CategoryTheory CategoryTheory.Limits

universe u

/-! ## Filtered colimit presentations -/

/-- A filtered colimit presentation of an `A`-algebra whose stages are local
isomorphisms over `A`.

The diagram lives in `Under (CommRingCat.of A)`, so every stage already
contains its structure map from `A`.  The final isomorphism is likewise in
that category and therefore identifies the induced map on the colimit with
the specified ring map `f`.
-/
structure IndZariskiPresentation
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    extends Formalization.Books.Algebra.Unit154.FilteredColimitData f where
  stagesLocalIsomorphism : ∀ i,
    Formalization.Books.Proetale.Unit03.IsLocalIsomorphism
      (diagram.obj i).hom.hom

/-- A ring map is ind-Zariski when its target is a filtered colimit of
`A`-algebras whose structure maps are local isomorphisms.
-/
def IsIndZariski {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Nonempty (IndZariskiPresentation f)

/-! ## Ind-Zariski maps -/

/-- Localization is the basic example of an ind-Zariski map.

The source points to the standard filtered-colimit presentation of a
localization; its proof is deferred to the proof stage.
-/
theorem localization_isIndZariski
    {A : Type u} [CommRing A] (S : Submonoid A) :
    IsIndZariski (algebraMap A (Localization S)) := by
  sorry

/-- Ind-Zariski maps are stable under base change. -/
theorem isIndZariski_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A')
    (hf : IsIndZariski f) :
    IsIndZariski (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

/-- Ind-Zariski maps are stable under composition. -/
theorem isIndZariski_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsIndZariski f) (hg : IsIndZariski g) :
    IsIndZariski (g.comp f) := by
  sorry

/-- The permanence property: among `A`-algebras, an ind-Zariski map between
two ind-Zariski algebras is again ind-Zariski. -/
theorem isIndZariski_of_algebraHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (h : B →ₐ[A] C)
    (hB : IsIndZariski (algebraMap A B))
    (hC : IsIndZariski (algebraMap A C)) :
    IsIndZariski h.toRingHom := by
  sorry

/-- A filtered colimit of ind-Zariski `A`-algebras is ind-Zariski over `A`.

The cocone and its colimit witness are explicit, as is the isomorphism of
the cocone point with the target ring map.
-/
theorem isIndZariski_filteredColimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A))
    (hF : ∀ j, IsIndZariski (F.obj j).hom.hom)
    (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Formalization.Books.Algebra.Unit127.underRingHom f) :
    IsIndZariski f := by
  sorry

/-- An ind-Zariski map identifies the local rings at corresponding primes. -/
theorem isIndZariski_identifiesLocalRings
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : IsIndZariski f) :
    Formalization.Books.Proetale.Unit03.IdentifiesLocalRings f := by
  sorry

end Formalization.Books.Proetale.Unit04
