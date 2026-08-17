import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.OpenCover

/-!
# Exercises, Chapter 23: Glueing

This file records the module-locality exercise and the intervening remark.
The source's `D(f)` is represented by Mathlib's canonical
`PrimeSpectrum.basicOpen`, and `M_f` by `LocalizedModule.Away f M`.
-/

namespace Formalization.Books.Exercises.Unit23

universe u v w

noncomputable section

/-! ## Exercise `cover` -/

/-!
The source's equality `Spec(A) = ⋃ D(f_i)` is represented by the canonical
`TopologicalSpace.IsOpenCover` predicate applied to the basic opens.
-/

/-- Finiteness of a module can be checked on a basic-open cover of the spectrum. -/
theorem finite_module_of_basicOpenCover
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A)
    (hcover : TopologicalSpace.IsOpenCover
      (fun i : ι => PrimeSpectrum.basicOpen (f i)))
    (hlocal : ∀ i : ι,
      Module.Finite (Localization.Away (f i))
        (LocalizedModule.Away (f i) M)) :
    Module.Finite A M := by
  sorry

/-- Flatness of a module can be checked on a basic-open cover of the spectrum. -/
theorem flat_module_of_basicOpenCover
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A)
    (hcover : TopologicalSpace.IsOpenCover
      (fun i : ι => PrimeSpectrum.basicOpen (f i)))
    (hlocal : ∀ i : ι,
      Module.Flat (Localization.Away (f i))
        (LocalizedModule.Away (f i) M)) :
    Module.Flat A M := by
  sorry

/-!
The source remark says that finite generation and flatness are local in this
sense, and that finite presentation is local as well.  The first two facts
are the preceding declarations; the additional precise assertion is recorded
below.
-/

/-- Finite presentation of a module can be checked on a basic-open cover. -/
theorem finitePresentation_module_of_basicOpenCover
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A)
    (hcover : TopologicalSpace.IsOpenCover
      (fun i : ι => PrimeSpectrum.basicOpen (f i)))
    (hlocal : ∀ i : ι,
      Module.FinitePresentation (Localization.Away (f i))
        (LocalizedModule.Away (f i) M)) :
    Module.FinitePresentation A M := by
  sorry

end

end Formalization.Books.Exercises.Unit23
