/-!
# Sheaves on Algebraic Stacks, Chapter 1: Introduction

The source section describes the scope of the chapter: sheaves on algebraic
stacks, constructible étale sheaves, and derived categories of complexes of
`𝒪`-modules with quasi-coherent cohomology.  It contains no standalone
definition, theorem, identity, diagram, exact sequence, or example to state
in Lean.

The section does make one mathematically meaningful methodological warning:
a morphism of algebraic stacks does not induce a morphism of
lisse-étale topoi.  It recommends replacing arguments that use that site by
Čech-covering arguments in the site `𝓧_smooth` introduced later.  The source
does not define the lisse-étale topoi, the relevant morphism, or
`𝓧_smooth` in this section, so this warning is recorded here as documentation
rather than as an underspecified Lean proposition.

The remaining remarks concern the chapter's chosen foundations, the amount
of work deferred to later chapters, and intentionally nonstandard notation
and terminology.  They are expository rather than standalone mathematical
assertions.
-/
