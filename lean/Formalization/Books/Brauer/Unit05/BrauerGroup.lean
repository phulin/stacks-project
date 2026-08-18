import Formalization.Books.Brauer.Unit04.AlgebraLemmas
import Formalization.Books.Brauer.Unit05.Foundation

/-!
# Brauer groups, Chapter 5: The Brauer group of a field

The source's finite central simple algebras and similarity relation are
already represented by Mathlib's `CSA` and `IsBrauerEquivalent`.  The
source-facing group, base-change, division-representative, algebraically
closed, and dimension interfaces were established in the earlier Brauer
formalization and are re-exported here in the order in which the source uses
them.
-/

namespace Formalization.Books.Brauer.Unit05

open Formalization.Books.Brauer
open scoped TensorProduct

/-! ## Similarity -/

/- The textbook's similarity relation is exactly Mathlib's canonical
   `IsBrauerEquivalent`; this alias supplies the chapter terminology without
   introducing a parallel relation. -/
alias similarity := IsBrauerEquivalent

alias similarity_is_equivalence :=
  Formalization.Books.Brauer.similarity_is_equivalence

alias similarity_has_unique_division_representative :=
  Formalization.Books.Brauer.similarity_has_unique_division_representative

alias matrix_division_similarity_iff :=
  Formalization.Books.Brauer.matrix_division_similarity_iff

/-! ## The Brauer group -/

/- `BrauerGroup k` is Mathlib's quotient of `CSA k` by `IsBrauerEquivalent`.
   The following interfaces record the tensor-product operation, its
   identity and inverse, and the resulting abelian-group structure. -/
alias brauer_group_is_abelian :=
  Formalization.Books.Brauer.brauer_group_is_abelian

alias brauer_group_tensor_operation_interface :=
  Formalization.Books.Brauer.brauer_group_tensor_operation_interface

/- Base change is represented by a group homomorphism together with the
   canonical right-hand tensor-product representative. -/
alias brauer_group_base_change_interface :=
  Formalization.Books.Brauer.brauer_group_base_change_interface

alias brauer_group_zero_iff :=
  Formalization.Books.Brauer.brauer_group_zero_iff

alias brauer_group_algebraically_closed :=
  Formalization.Books.Brauer.brauer_group_algebraically_closed

alias finite_central_simple_dimension_square :=
  Formalization.Books.Brauer.finite_central_simple_dimension_square

end Formalization.Books.Brauer.Unit05
