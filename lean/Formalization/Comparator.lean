import Formalization.Challenge

/-!
# Comparator for the substantive geometry challenges

This file duplicates the expected witness records and checks both directions
of their public interfaces. It also assigns each challenge theorem to an
explicit expected signature, catching added hypotheses or weaker conclusions.

Run this file with `lake env lean Comparator.lean`.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Comparator

structure ExpectedCompactification {X S : Scheme.{u}} (f : X ⟶ S) where
  space : Scheme.{u}
  openImmersion : X ⟶ space
  properMap : space ⟶ S
  openImmersion_isOpen : IsOpenImmersion openImmersion
  openImmersion_quasiCompact : QuasiCompact openImmersion
  properMap_isProper : IsProper properMap
  fac : openImmersion ≫ properMap = f

def compactificationToExpected {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Challenge.Compactification f) : ExpectedCompactification f where
  space := c.space
  openImmersion := c.openImmersion
  properMap := c.properMap
  openImmersion_isOpen := c.openImmersion_isOpen
  openImmersion_quasiCompact := c.openImmersion_quasiCompact
  properMap_isProper := c.properMap_isProper
  fac := c.fac

def compactificationFromExpected {X S : Scheme.{u}} {f : X ⟶ S}
    (c : ExpectedCompactification f) : Challenge.Compactification f where
  space := c.space
  openImmersion := c.openImmersion
  properMap := c.properMap
  openImmersion_isOpen := c.openImmersion_isOpen
  openImmersion_quasiCompact := c.openImmersion_quasiCompact
  properMap_isProper := c.properMap_isProper
  fac := c.fac

/-- The expected public signature of Stacks tag `0F41`. -/
def ExpectedNagataSignature : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    CompactSpace S → QuasiSeparatedSpace S →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    Nonempty (ExpectedCompactification f)

theorem challenge_nagata_matches : ExpectedNagataSignature := by
  intro X S f hqc hqs hsep hft hqcf
  let _ := hqc
  let _ := hqs
  let _ := hsep
  let _ := hft
  let _ := hqcf
  exact (Challenge.nagataCompactification f).map compactificationToExpected

structure ExpectedSteinFactorization {X S : Scheme.{u}} (f : X ⟶ S) where
  middle : Scheme.{u}
  connectedMap : X ⟶ middle
  integralMap : middle ⟶ S
  connectedMap_isProper : IsProper connectedMap
  connectedMap_geometricallyConnected : GeometricallyConnected connectedMap
  integralMap_isIntegral : IsIntegralHom integralMap
  fac : connectedMap ≫ integralMap = f

def steinToExpected {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Challenge.SteinFactorization f) : ExpectedSteinFactorization f where
  middle := c.middle
  connectedMap := c.connectedMap
  integralMap := c.integralMap
  connectedMap_isProper := c.connectedMap_isProper
  connectedMap_geometricallyConnected := c.connectedMap_geometricallyConnected
  integralMap_isIntegral := c.integralMap_isIntegral
  fac := c.fac

def steinFromExpected {X S : Scheme.{u}} {f : X ⟶ S}
    (c : ExpectedSteinFactorization f) : Challenge.SteinFactorization f where
  middle := c.middle
  connectedMap := c.connectedMap
  integralMap := c.integralMap
  connectedMap_isProper := c.connectedMap_isProper
  connectedMap_geometricallyConnected := c.connectedMap_geometricallyConnected
  integralMap_isIntegral := c.integralMap_isIntegral
  fac := c.fac

/-- The expected public signature of the geometric part of Stacks tag `03H2`. -/
def ExpectedSteinSignature : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    IsProper f → Nonempty (ExpectedSteinFactorization f)

theorem challenge_stein_matches : ExpectedSteinSignature := by
  intro X S f hproper
  let _ := hproper
  exact (Challenge.steinFactorization f).map steinToExpected

end Comparator
