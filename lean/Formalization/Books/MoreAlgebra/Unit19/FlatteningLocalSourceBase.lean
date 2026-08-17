import Formalization.Books.MoreAlgebra.Unit18.FlatteningLocalBase

/-!
# More on Algebra, Chapter 19: Flattening over closed subsets of source and base

The source's base-changed rings and modules use the canonical extension-of-
scalars constructions from Chapter 14.  The stalkwise flatness predicate is
the localized-module predicate from Chapter 99, and the directed-colimit
data is the interface established in Chapter 18.
-/

namespace Formalization.Books.MoreAlgebra.Unit19

open scoped TensorProduct

universe u

noncomputable section

/-! ## Flattening over a closed subset of source and base -/

/- The source's situation consists of a ring map `R → S`, an ideal `J` of `S`,
   and an `S`-module `M`; these are the parameters of the declarations below. -/

/-- The source's condition that the base change of `M` is flat over `R'` at
every prime containing the extensions of `I'` and `J`.

The base-changed ring is `S ⊗[R] R'`, the ideal `I' S'` is represented by
`Ideal.map` along the right-hand tensor inclusion, and `J S'` by `Ideal.map`
along the left-hand tensor inclusion.  The localized module is expressed by
the canonical `flatAtPrimeOverBase` predicate. -/
def flatAtPrimesOverSource
    {R S M R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (J : Ideal S) (g : R →+* R') (I' : Ideal R') : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R' (S ⊗[R] R') :=
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
  letI : Module R'
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g) :=
    Module.compHom
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
  letI : IsScalarTower R' (S ⊗[R] R')
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g) :=
    SMul.comp.isScalarTower
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
  ∀ q' : PrimeSpectrum (S ⊗[R] R'),
    I'.map (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) +
        J.map (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) ≤
      q'.asIdeal →
      Formalization.Books.Algebra.Unit99.flatAtPrimeOverBase
        (R := R') (S := S ⊗[R] R')
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule
          (M := M) f g) q'

/-- The same flatness-along-closed-subsets condition at the original base
ring.  This is the source's condition for `(R, I)`, written using the
canonical localized module over a prime of `S`. -/
def flatAtPrimesOverSourceAtBase
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (J : Ideal S) (I : Ideal R) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  ∀ q : PrimeSpectrum S, J + I.map f ≤ q.asIdeal →
    Formalization.Books.Algebra.Unit99.flatAtPrimeOverBase
      (R := R) (S := S) (M := M) q

/-! ## Base change and descent -/

/-- Flatness along the intersection of the source and base closed subsets is
preserved by an `R`-algebra base change.  The equation `compat` expresses that
the ring map `h` from `R'` to `R''` is over `R`. -/
theorem flatAtPrimesOverSource_baseChange
    {R S R' R'' M : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing R'']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (J : Ideal S)
    (g' : R →+* R') (g'' : R →+* R'') (h : R' →+* R'')
    (compat : h.comp g' = g'')
    (I' : Ideal R') (I'' : Ideal R'')
    (hI : I'.map h ≤ I'')
    (hflat : flatAtPrimesOverSource (M := M) f J g' I') :
    flatAtPrimesOverSource (M := M) f J g'' I'' := by
  sorry

/-- Flatness along the intersection descends from an `R`-algebra base change
when the relevant closed subset maps surjectively and the localized target
ring is flat over the source ring. -/
theorem flatAtPrimesOverSource_descent
    {R S R' R'' M : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing R'']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (J : Ideal S)
    (g' : R →+* R') (g'' : R →+* R'') (h : R' →+* R'')
    (compat : h.comp g' = g'')
    (I' : Ideal R') (I'' : Ideal R'')
    (hI : I'.map h ≤ I'')
    (hsurj : ∀ p' : PrimeSpectrum R', I' ≤ p'.asIdeal →
      ∃ p'' : PrimeSpectrum R'', I'' ≤ p''.asIdeal ∧
        PrimeSpectrum.comap h p'' = p')
    (hflatLocal : ∀ p'' : PrimeSpectrum R'', I'' ≤ p''.asIdeal →
      RingHom.Flat
        ((algebraMap R'' (Localization.AtPrime p''.asIdeal)).comp h))
    (hflat : flatAtPrimesOverSource (M := M) f J g'' I'') :
    flatAtPrimesOverSource (M := M) f J g' I' := by
  sorry

/-! ## Directed colimits -/

/-- Flatness along the source and base closed subsets descends to a sufficiently
large stage of a directed colimit when the original algebra map and module are
finitely presented.  `DirectedIdealColimit` records both compatibility of the
stage ideals and their represented colimit ideal. -/
theorem flatAtPrimesOverSource_limit
    {R S R' M : Type u}
    [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : RingHom.EssFinitePresentation f)
    (hM : Module.FinitePresentation S M)
    (J : Ideal S) (g : R →+* R')
    (D : Formalization.Books.Algebra.Unit127.DirectedAlgebraColimit g)
    (I : ∀ i : D.index,
      Ideal (Formalization.Books.Algebra.Unit127.directedAlgebraStageRing D i))
    (I' : Ideal R')
    (hI : Formalization.Books.MoreAlgebra.Unit18.DirectedIdealColimit D I I')
    (hflat : flatAtPrimesOverSource (M := M) f J g I') :
    ∃ i : D.index,
      flatAtPrimesOverSource (M := M) f J
        (Formalization.Books.MoreAlgebra.Unit18.directedAlgebraStageMap D i)
        (I i) := by
  sorry

/-! ## The Noetherian powers criterion -/

/-- Flatness of the localized quotient by `I ^ n` over `R / I ^ n`.

The source writes this as `(M / I ^ n M)_(q)`.  The canonical localized-module
presentation used here first localizes `M` at `q` and then takes the quotient
by the localized `I ^ n`-multiple; the standard localization/quotient
equivalence identifies the two presentations. -/
noncomputable def flatPowerQuotientAtPrime
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (I : Ideal R) (n : ℕ) (q : PrimeSpectrum S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  letI : Module R (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.compHom _ (algebraMap R (Localization.AtPrime q.asIdeal))
  Module.Flat (R ⧸ (I ^ n))
    ((LocalizedModule q.asIdeal.primeCompl M) ⧸
      (I ^ n •
        (⊤ : Submodule R (LocalizedModule q.asIdeal.primeCompl M))))

/-- If every localized power quotient is flat over the corresponding quotient
of a Noetherian base, then `M` is flat over `R` at every prime containing
`J + IS`. -/
theorem flatAtPrimesOverSource_powers
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (f : R →+* S) (J : Ideal S) (I : Ideal R)
    (hflat : ∀ n : ℕ, 0 < n →
      ∀ q : PrimeSpectrum S, J + I.map f ≤ q.asIdeal →
        flatPowerQuotientAtPrime (M := M) f I n q) :
    flatAtPrimesOverSourceAtBase (M := M) f J I := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit19
