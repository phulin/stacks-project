import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Formalization.Books.Algebra.Unit166.GeometricallyRegular
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.Flat

/-!
# More Algebra, Chapter 41: Regular ring maps

The source's regular maps use flatness together with geometrically regular
Noetherian fibres.  Fibres are represented by Mathlib's canonical
`Ideal.Fiber` and geometric regularity by the earlier Algebra chapter's
`IsGeometricallyRegular` predicate.
-/

namespace Formalization.Books.MoreAlgebra.Unit41

open scoped TensorProduct

noncomputable section

universe u v

/-! ## Geometrically regular fibres -/

/- The source calls an algebra geometrically regular when all finite purely
   inseparable field base changes are regular.  The canonical Algebra API
   also records the equivalent finitely generated field-extension test. -/
theorem geometricallyRegular_iff_finitePurelyInseparable
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A] :
    (∀ (k' : Type u) [Field k'] [Algebra k k']
        [Algebra.FiniteType k k'],
      IsRegularRing (k' ⊗[k] A)) ↔
      Formalization.Books.Algebra.Unit166.IsGeometricallyRegular k A :=
  Formalization.Books.Algebra.Unit166.isRegular_tensorProduct_iff_finitePurelyInseparable

theorem isRegularRing_tensorProduct_of_geometricallyRegular
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A]
    (hA : Formalization.Books.Algebra.Unit166.IsGeometricallyRegular k A)
    {k' : Type u} [Field k'] [Algebra k k']
    [Algebra.FiniteType k k'] :
    IsRegularRing (k' ⊗[k] A) :=
  (geometricallyRegular_iff_finitePurelyInseparable (k := k) (A := A)).mpr hA k'

/-! ## The definition -/

/-- A Noetherian algebra over a field with geometrically regular fibres.

The existentially packaged Noetherian instance lets this predicate be used
without requiring a global typeclass on the fibre before the predicate is
introduced. -/
def IsNoetherianGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] : Prop :=
  ∃ hA : IsNoetherianRing A,
    letI : IsNoetherianRing A := hA
    Formalization.Books.Algebra.Unit166.IsGeometricallyRegular k A

/-- The canonical fibre of `f` at `p`, with its residue-field algebra. -/
abbrev regularFiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Type u :=
  p.asIdeal.Fiber S

/-- Noetherianity of all canonical fibres of a ring map. -/
def HasNoetherianFibres
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S)

/-- A ring map is regular when it is flat and every fibre is Noetherian and
geometrically regular over the corresponding residue field. -/
def IsRegularRingMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  RingHom.Flat f ∧
    ∀ p : PrimeSpectrum R,
      letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.leftAlgebra
      IsNoetherianGeometricallyRegular p.asIdeal.ResidueField
        (p.asIdeal.Fiber S)

/-- The quotient model for a canonical fibre is Mathlib's
`Ideal.Fiber.algEquivQuotient`, corresponding to
`S_p / p S_p` in the source. -/
noncomputable def regularFiberQuotientEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI Rp := Localization.AtPrime p.asIdeal
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.asIdeal.Fiber S ≃ₐ[S] Sp ⧸ pSp := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  exact Ideal.Fiber.algEquivQuotient (R := R) (S := S) p.asIdeal

/-- The map between the localizations at a prime and a prime above it. -/
noncomputable def localizedPrimeRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/-- If the target is Noetherian, all fibres of a ring map are Noetherian. -/
theorem hasNoetherianFibres_of_isNoetherian
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing S] :
    HasNoetherianFibres f := by
  sorry

/-! ## Locality -/

/-- Regularity is equivalent to regularity after localizing at every prime,
or only at maximal ideals of the source and target. -/
theorem regular_iff_localizations_iff_maximalLocalizations
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing S] :
    List.TFAE
      [ IsRegularRingMap f,
        ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S),
          ∀ (hq : PrimeSpectrum.comap f q = p),
            IsRegularRingMap (localizedPrimeRingHom f p q hq),
        ∀ (m : MaximalSpectrum R) (n : MaximalSpectrum S)
          (hn : PrimeSpectrum.comap f (MaximalSpectrum.toPrimeSpectrum n) =
            MaximalSpectrum.toPrimeSpectrum m),
              IsRegularRingMap
                (localizedPrimeRingHom f
                  (MaximalSpectrum.toPrimeSpectrum m)
                  (MaximalSpectrum.toPrimeSpectrum n) hn) ] := by
  sorry

/-! ## Base change -/

/-- The fibre identity used in base change: the fibre after base change is
the corresponding fibre tensor the residue-field extension. -/
theorem regularFiber_baseChange_equiv
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (p' : PrimeSpectrum R') :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R' (S ⊗[R] R') :=
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
    let p := PrimeSpectrum.comap g p'
    letI : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
      (Ideal.ResidueField.map p.asIdeal p'.asIdeal g (by
        simpa [p, PrimeSpectrum.comap_asIdeal])).toAlgebra
    letI : Algebra p'.asIdeal.ResidueField
        (p'.asIdeal.Fiber (S ⊗[R] R')) :=
      Algebra.TensorProduct.leftAlgebra
    letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.leftAlgebra
    letI : Algebra p'.asIdeal.ResidueField
        (p.asIdeal.Fiber S ⊗[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      (p'.asIdeal.Fiber (S ⊗[R] R') ≃ₐ[p'.asIdeal.ResidueField]
        (p.asIdeal.Fiber S ⊗[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField)) := by
  sorry

/-- Regular maps remain regular after finite-type base change. -/
theorem regular_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hfinite : RingHom.FiniteType g)
    (hf : IsRegularRingMap f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsRegularRingMap
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  sorry

/-! ## Composition and filtered colimits -/

/-- The composite of regular maps is regular when its fibres are Noetherian. -/
theorem regular_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsRegularRingMap f) (hg : IsRegularRingMap g)
    (hfinite : HasNoetherianFibres (g.comp f)) :
    IsRegularRingMap (g.comp f) := by
  sorry

/-- A directed colimit of smooth algebras with Noetherian fibres is regular.
The directed system is represented by the canonical earlier-chapter
`DirectedAlgebraColimit` interface. -/
theorem regular_of_directedColimit_smooth
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit f)
    (hsmooth : ∀ i, letI : Preorder D.index := D.indexPreorder
      letI : Algebra R (D.diagram.obj i).right :=
        (D.diagram.obj i).hom.hom.toAlgebra
      Algebra.Smooth R (D.diagram.obj i).right)
    (hfinite : HasNoetherianFibres f) :
    IsRegularRingMap f := by
  sorry

/-! ## Field extensions -/

/-- A field extension defines a regular map exactly when it is separable. -/
theorem regular_fieldExtension_iff_separable
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    IsRegularRingMap (algebraMap k K) ↔
      ∀ (L : IntermediateField k K),
        Algebra.EssFiniteType k L →
          ∃ (ι : Type u) (x : ι → L),
            IsTranscendenceBasis k x ∧
              Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L := by
  sorry

/-! ## Permanence -/

/-- If `A → C` is regular and `B → C` is flat and surjective on spectra,
then `A → B` is regular. -/
theorem regular_of_comp_of_flat_of_surjectiveOnSpectrum
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hregular : IsRegularRingMap (g.comp f))
    (hflat : RingHom.Flat g)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap g)) :
    IsRegularRingMap f := by
  sorry

end
end Formalization.Books.MoreAlgebra.Unit41
