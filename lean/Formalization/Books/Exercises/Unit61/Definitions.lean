import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Length
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules

/-!
# Exercises, Chapter 61: Definitions

The source asks for the standard definitions of constructible subsets,
localization at a prime, module length, projective modules, and
Cohen--Macaulay modules.  These are already provided by the canonical
Mathlib and earlier-project interfaces listed below, so this file deliberately
does not introduce duplicate aliases.
-/

/-!
The five requested notions are represented by:

* `Topology.IsConstructible` for constructible subsets;
* `LocalizedModule.AtPrime` for localization of a module at a prime;
* `Module.length` for module length;
* `Module.Projective` for projective modules; and
* `Formalization.Books.Algebra.Unit103.IsCohenMacaulay`, with depth supplied
  by `Formalization.Books.Algebra.Unit72.localDepth`, for Cohen--Macaulay
  modules over Noetherian local rings.

These canonical declarations preserve the hypotheses and conventions of the
project's existing algebra formalization.
-/
