import Formalization.Books.Brauer.Unit01.SplittingFields

/-!
# Brauer groups, Chapter 8: Splitting fields

The splitting-field constructions and their interfaces were established in
the earlier Brauer API.  This file exposes those declarations in the
chapter-specific namespace, preserving the canonical Mathlib representations
of tensor-product base change, Brauer similarity, separability, and Galois
extensions.
-/

namespace Formalization.Books.Brauer.Unit08

open Formalization.Books.Brauer
open scoped TensorProduct

/-! ## Splitting fields -/

alias IsMaximalCommutativeSubalgebra :=
  Formalization.Books.Brauer.IsMaximalCommutativeSubalgebra

alias SplitsInDegree := Formalization.Books.Brauer.SplitsInDegree

alias Splits := Formalization.Books.Brauer.Splits

alias splits_iff_exists_matrix_degree :=
  Formalization.Books.Brauer.splits_iff_exists_matrix_degree

alias splits_iff_base_change_class_eq_one :=
  Formalization.Books.Brauer.splits_iff_base_change_class_eq_one

alias splitting_iff_similar_embedded_subfield :=
  Formalization.Books.Brauer.splitting_iff_similar_embedded_subfield

alias maximal_subfield_splits :=
  Formalization.Books.Brauer.maximal_subfield_splits

alias splitting_field_degree_dvd :=
  Formalization.Books.Brauer.splitting_field_degree_dvd

alias SeparableMaximalSubfield :=
  Formalization.Books.Brauer.SeparableMaximalSubfield

alias exists_separable_maximal_subfield :=
  Formalization.Books.Brauer.exists_separable_maximal_subfield

alias FiniteSeparableSplittingField :=
  Formalization.Books.Brauer.FiniteSeparableSplittingField

alias brauer_class_has_finite_separable_splitting_field :=
  Formalization.Books.Brauer.brauer_class_has_finite_separable_splitting_field

alias FiniteGaloisSplittingField :=
  Formalization.Books.Brauer.FiniteGaloisSplittingField

alias MatrixDivisionPresentation :=
  Formalization.Books.Brauer.MatrixDivisionPresentation

alias finite_central_simple_tfae :=
  Formalization.Books.Brauer.finite_central_simple_tfae

alias finite_central_simple_degree_is_unique :=
  Formalization.Books.Brauer.finite_central_simple_degree_is_unique

end Formalization.Books.Brauer.Unit08
