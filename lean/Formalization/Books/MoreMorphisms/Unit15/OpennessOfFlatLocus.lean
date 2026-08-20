import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# More on Morphisms, §15: Openness of the flat locus

This section records the openness of the flat locus for a locally finitely
presented morphism and module, together with its stalkwise base-change
criterion.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/- The local-ring formulation is the canonical stalkwise meaning of a
   morphism being flat at a point. -/
def FlatAt (f : X ⟶ Y) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat

end Scheme.Hom

namespace Scheme.Modules

variable {X Y : Scheme.{u}}

/-
Mathlib's `IsFinitePresentation` for a sheaf of modules is the established
quasi-coherent, locally finite-presentation interface used below.  The
stalkwise module structure is provided by `ModuleCat.Stalk`, and the
`Module.compHom` makes it a module over the base stalk.
-/
def FlatAt (M : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
    let N : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
    change Module (X.presheaf.stalk x)
      (@TopCat.Presheaf.stalk (AddCommGrpCat.{u}) _ _ (X : TopCat.{u}) N.presheaf x)
    infer_instance
  letI := Module.compHom (M.presheaf.stalk x) (f.stalkMap x).hom
  Module.Flat (Y.presheaf.stalk (f x)) (M.presheaf.stalk x)

/-- The set of points where `M` is flat over the base of `f`. -/
def flatLocus (M : X.Modules) (f : X ⟶ Y) : Set X :=
  {x | M.FlatAt f x}

/-
Proof roadmap (`isOpen_flatLocus`; the statement and hypotheses match the source theorem).

1. Work pointwise with `X.isBasis_affineOpens.exists_subset_of_mem_open`: first choose an affine
   `U : Y.Opens` through `f x`, then refine the finite-presentation cover carried by
   `SheafOfModules.IsFinitePresentation.exists_quasicoherentData M` to an affine
   `V : X.Opens` through `x` with `V ≤ f ⁻¹ᵁ U`.  On this chart use
   `f.finitePresentation_appLE hU hV hVU` from
   `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean` for the ring map
   `(f.appLE U V hVU).hom : Γ(Y, U) →+* Γ(X, V)`.
2. The missing input is the affine finite-presentation/sheaf comparison.  A finite variant of
   `Scheme.Modules.exists_affineOpenCover_presentation` should retain
   `SheafOfModules.Presentation.IsFinite` after restriction; the existing declaration in
   `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` deliberately retains only `Presentation`.
   On each resulting affine scheme `V`, prove that `Γ(N, ⊤)` is
   `Module.FinitePresentation Γ(V, ⊤)`, and identify `N.FlatAt` with
   `Formalization.Books.Algebra.Unit129.flatAtPrimeOverBaseRingHom` after transporting points
   through the affine `isoSpec`.  This result is not currently provided by either
   `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` (which only supplies finite local
   sheaf presentations) or `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.
3. In that affine comparison, reuse
   `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, `Scheme.Modules.restrictAppIso`, and
   `Scheme.Modules.tilde.toStalk` from `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` to compare
   the sheaf stalk with the localization of `Γ(N, ⊤)`.  The finite local presentation must be
   transported to global sections before invoking
   `Formalization.Books.Algebra.Unit129.openness_flatness` from
   `Formalization/Books/Algebra/Unit129/OpennessFlatLocus.lean` with
   `R := Γ(Y, U)`, `S := Γ(X, V)`, and `M := Γ(M, V)`.
4. Pull the resulting open subset of `V` back along the open immersion `V.ι`, prove that it is
   exactly `M.flatLocus f ∩ V`, and use the affine neighbourhoods from step 1 to conclude that
   every point of `M.flatLocus f` has an open neighbourhood contained in the locus.

Dead end to avoid: unfolding `SheafOfModules.IsFinitePresentation` only exposes a finite
presentation on a site cover; there is presently no theorem turning it into the
`Module.FinitePresentation` hypothesis required by `Unit129.openness_flatness`.
-/
theorem isOpen_flatLocus (M : X.Modules) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [M.IsFinitePresentation] :
    IsOpen (M.flatLocus f) := by
  sorry

end Scheme.Modules

section BaseChange

variable {X X' Y Y' : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-!
The following two declarations are the two assertions in the source lemma,
with `IsPullback g' f' f g` expressing its cartesian square and
`Scheme.Modules.pullback g'` expressing `(g')^*`.
-/

lemma flatAt_pullback (h : IsPullback g' f' f g) (M : X.Modules) [M.IsQuasicoherent]
    (x' : X')
    (hx : M.FlatAt f (g' x')) :
    ((Scheme.Modules.pullback g').obj M).FlatAt f' x' := by
  /-
  Proof roadmap (the statement is sound; the required stalk comparison is missing).

  1. Put `R := Y.presheaf.stalk (f (g' x'))`, `S := X.presheaf.stalk (g' x')`,
     `R' := Y'.presheaf.stalk (f' x')`, and `S' := X'.presheaf.stalk x'`.  Use
     `h.w`, `Scheme.Hom.stalkMap_comp`, and `Scheme.Hom.stalkMap_congr_hom` to normalize the
     four stalk maps to a commutative square `rf : R →+* S`, `rg : R →+* R'`,
     `rh : S →+* S'`, `rk : R' →+* S'`.
  2. Supply the missing geometric base-change API: the normalized stalk square must give
     `IsTensorProductLocalization rf rg rh rk compat`, and quasicoherence of `M` must give an
     `R'`-linear equivalence
     `((pullback g').obj M).presheaf.stalk x' ≃ₗ[R']
       squareBaseChangedModule rh rk (ModuleCat.of S (M.presheaf.stalk (g' x')))`,
     where the module on the left uses scalar restriction along `rk`.  The linearity over `R'`
     is essential: an additive stalk isomorphism cannot transport `Module.Flat`.
  3. All four rings above live in `Type u`, so instantiate the algebra theorem with
     `ModuleCat.{u}`.  After installing the canonical stalk modules, `change` `hx` into flatness of
     `(ModuleCat.restrictScalars rf).obj
       (ModuleCat.of S (M.presheaf.stalk (g' x')))` over `R`.
  4. Apply the forward implication of
     `Formalization.Books.Algebra.Unit100.base_change_flat_up_down` from
     `Formalization/Books/Algebra/Unit100/BaseChangeAndFlatness.lean`, then transport its
     `Module.Flat R' (squareBaseChangedModule rh rk ...)` conclusion across the equivalence in
     step 2 with `Module.Flat.of_linearEquiv` from `Mathlib/RingTheory/Flat/Basic.lean`.

  Dead end to avoid: `SheafOfModules.pullbackIso` in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` only describes pullback as
  presheaf pullback followed by sheafification; it does not yield the needed module-linear stalk
  tensor equivalence or its scalar compatibility.
  -/
  sorry

lemma flatAt_of_flatAt_pullback (h : IsPullback g' f' f g) (M : X.Modules) [M.IsQuasicoherent]
    (x' : X')
    (hg : g.FlatAt (f' x'))
    (hx' : ((Scheme.Modules.pullback g').obj M).FlatAt f' x') :
    M.FlatAt f (g' x') := by
  /-
  Proof roadmap (reuse exactly the normalized square and stalk equivalence described for
  `flatAt_pullback`).

  1. Instantiate `R`, `S`, `R'`, `S'`, `rf`, `rg`, `rh`, `rk`, and `compat` in universe `u` as
     above, and obtain
     both `IsTensorProductLocalization rf rg rh rk compat` and the `R'`-linear pullback-stalk
     equivalence.  Transport `hx'` across its inverse with `Module.Flat.of_linearEquiv` to get
     `Module.Flat R' (squareBaseChangedModule rh rk
       (ModuleCat.of S (M.presheaf.stalk (g' x'))))`; use `ModuleCat.{u}` throughout.
  2. Normalize `hg` to `RingHom.Flat rg`; no global `Flat g` instance is needed here.  All four
     stalk maps are local homomorphisms by the locally-ringed-space stalk API, so they provide the
     remaining instances expected by `Unit100.base_change_flat_up_down`.
  3. Apply the reverse implication
     `(Formalization.Books.Algebra.Unit100.base_change_flat_up_down
       rf rg rh rk compat hlocal (ModuleCat.of S _)).2` to the two flatness hypotheses.
     `change` its conclusion back to `M.FlatAt f (g' x')`.

  This direction must not be replaced by a bare faithfully-flat tensor descent: the target stalk
  is a localization of the tensor-product square, and `Unit100.base_change_flat_up_down` is the
  existing theorem that packages precisely that local up/down argument.
  -/
  sorry

/-!
When the base change is globally flat, the two stalkwise implications give
the source's statement that the flat-locus open subset commutes with base
change.
-/
theorem flatLocus_pullback_eq_preimage (h : IsPullback g' f' f g) (M : X.Modules)
    [Flat g] [LocallyOfFinitePresentation f] [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback g').obj M).flatLocus f' = g' ⁻¹' M.flatLocus f := by
  /-
  Proof roadmap (this is only set extensionality once the two pointwise lemmas are available).

  1. Install the quasicoherence proof explicitly before extensionality:
     `let _ : M.IsQuasicoherent := by constructor; exact Nonempty.intro
       (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose`.
     Although `Quasicoherent.lean` declares the intended instance, direct instance synthesis from
     this theorem's universe-polymorphic finite-presentation binder is currently stuck; the
     explicit construction has been checked against this declaration.
  2. Use `Set.ext x'`, then `change` the membership goal to
     `((pullback g').obj M).FlatAt f' x' ↔ M.FlatAt f (g' x')`.
  3. The left-to-right implication is
     `flatAt_of_flatAt_pullback h M x' (Flat.stalkMap g (f' x'))`, and the right-to-left
     implication is `flatAt_pullback h M x'`.  Finish with `constructor` rather than unfolding
     either stalkwise proof.

  `LocallyOfFinitePresentation f` is intentionally retained although set extensionality does not
  consume it: together with `M.IsFinitePresentation` it is the source lemma's hypothesis that the
  loci in this equality are the open subsets supplied by `isOpen_flatLocus`.
  -/
  sorry

end BaseChange
