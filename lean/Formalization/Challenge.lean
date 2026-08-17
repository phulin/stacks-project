import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Substantive algebraic-geometry challenges

This file records theorem-shaped benchmarks whose statements use Mathlib's
public algebraic-geometry API while their proofs require substantial portions
of the Stacks Project formalization.

The declarations deliberately package existential conclusions as structures.
This makes the target API stable and lets downstream comparator files inspect
the complete witness rather than merely checking a weakened proposition.

The first benchmark is Stacks tag `0F41`.  The second is the geometric content
of Stacks tag `03H2`; the source theorem additionally identifies the middle
scheme with the relative spectrum of `f_* O_X`.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Challenge

/-- A compactification of `f : X ⟶ S`: a quasi-compact open immersion into
a scheme proper over `S`. -/
structure Compactification {X S : Scheme.{u}} (f : X ⟶ S) where
  space : Scheme.{u}
  openImmersion : X ⟶ space
  properMap : space ⟶ S
  openImmersion_isOpen : IsOpenImmersion openImmersion
  openImmersion_quasiCompact : QuasiCompact openImmersion
  properMap_isProper : IsProper properMap
  fac : openImmersion ≫ properMap = f

/-- **Nagata compactification**, Stacks tag `0F41`.

Every separated finite-type morphism to a quasi-compact and quasi-separated
scheme admits a compactification. -/
theorem nagataCompactification {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (Compactification f) := by
  sorry

/-- The property-only data of a Stein factorization.  The map with
geometrically connected fibres remains proper, and the second map is
integral. -/
structure SteinFactorization {X S : Scheme.{u}} (f : X ⟶ S) where
  middle : Scheme.{u}
  connectedMap : X ⟶ middle
  integralMap : middle ⟶ S
  connectedMap_isProper : IsProper connectedMap
  connectedMap_geometricallyConnected : GeometricallyConnected connectedMap
  integralMap_isIntegral : IsIntegralHom integralMap
  fac : connectedMap ≫ integralMap = f

/-- **Stein factorization**, Stacks tag `03H2`, in its statement-light
geometric form.

The stronger source-facing version should later refine this witness by
identifying `middle` with the relative spectrum of `f_* O_X`. -/
theorem steinFactorization {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    Nonempty (SteinFactorization f) := by
  sorry

end Challenge
