import Formalization.Books.Algebra.Unit99.CriteriaForFlatness

/-!
# Commutative Algebra, Chapter 100: Base change and flatness

The commutative squares in the source are expressed by four ring homomorphisms
and an equality of their composites.  The localization hypothesis and the
base-changed module use the canonical interfaces from Chapter 99.
-/

namespace Formalization.Books.Algebra.Unit100

open Formalization.Books.Algebra.Unit99

universe u

noncomputable section

/-! ## Base change and flatness -/

/--
Flatness moves up and down a local square whose upper-right corner is a
localization of the tensor product.  The two conjuncts are the source's
items (1) and (2).
-/
theorem base_change_flat_up_down
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (M : ModuleCat.{u} S) :
    (Module.Flat R ((ModuleCat.restrictScalars f).obj M) →
        Module.Flat R' (squareBaseChangedModule h k M)) ∧
      (Module.Flat R' (squareBaseChangedModule h k M) →
        RingHom.Flat g →
          Module.Flat R ((ModuleCat.restrictScalars f).obj M)) := by
  sorry

/-- The source's item (3): flatness of the upper horizontal map ascends. -/
theorem flat_ring_hom_base_change
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat) :
    RingHom.Flat f → RingHom.Flat k := by
  sorry

/-- The source's item (4): flatness of the two right-hand maps descends. -/
theorem flat_ring_hom_base_change_down
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat) :
    RingHom.Flat k → RingHom.Flat g → RingHom.Flat f := by
  sorry

/-!
## Another local criterion for flatness

The module in the conclusion is `squareBaseChangedModule h k M`, namely the
canonical `M ⊗_S S'` viewed as an `R'`-module.
-/

/--
The finite-module local criterion after a flat base change.  The equality of
ideals records the source's hypothesis
`\mathfrak m_R R' = \mathfrak m_{R'}`.
-/
theorem yet_another_variant_local_criterion_flatness
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R'] [IsNoetherianRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (hflat_top : RingHom.Flat h) (hflat_bottom : RingHom.Flat g)
    (M : ModuleCat.{u} S) (hfinite : Module.Finite S M)
    (hmax : Ideal.map g (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal R')
    (hflat : Module.Flat R ((ModuleCat.restrictScalars f).obj M)) :
    Module.Flat R' (squareBaseChangedModule h k M) := by
  sorry

end

end Formalization.Books.Algebra.Unit100
