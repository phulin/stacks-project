import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Fields, Chapter 4: Vector spaces

The source identifies modules over a field with vector spaces.  We use
Mathlib's `Module` and `Module.Free` interfaces directly.  The source's
statement about exact sequences is represented by Mathlib's categorical
`ShortExact` and `ShortComplex.Splitting` interfaces.
-/

namespace Formalization.Books.Fields.Unit04

universe u v

/-! ## Vector spaces are free -/

/- Mathlib's `Module.Free.of_divisionRing` is the basis theorem used in the
   source proof, specialized here from division rings to fields. -/
/-- A module over a field is a free module. -/
theorem every_field_module_is_free (k V : Type*) [Field k]
    [AddCommGroup V] [Module k V] :
    Module.Free k V :=
  inferInstance

/-! ## Splitting exact sequences -/

/- A field module is free, hence projective; Mathlib's canonical splitting
   construction then splits every short exact sequence in the module category. -/
/-- Every short exact sequence of modules over a field splits. -/
theorem field_module_short_exact_splits (k : Type u) [Field k]
    (S : CategoryTheory.ShortComplex (ModuleCat.{v} k))
    (hS : S.ShortExact) :
    Nonempty S.Splitting := by
  exact ⟨hS.splittingOfProjective⟩

/-! ## The categorical formulation -/

/- Exactness is arrow-theoretic in the source.  The category of modules over a
   field is Mathlib's abelian category of modules. -/
/-- The category of modules over a field is abelian. -/
@[instance_reducible]
def field_module_category_is_abelian (k : Type u) [Field k] :
    CategoryTheory.Abelian (ModuleCat.{v} k) :=
  inferInstance

end Formalization.Books.Fields.Unit04
