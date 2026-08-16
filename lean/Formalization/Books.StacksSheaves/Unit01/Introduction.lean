/-!
# Sheaves on Algebraic Stacks, Chapter 1: Introduction

The source span `books/stacks-sheaves.tex:17-56` is introductory prose.  It
announces the chapter's approach to sheaves on algebraic stacks and the scope
of the later discussion of constructible etale sheaves and derived categories
of complexes of O-modules with quasi-coherent cohomology.  Those are scope
statements, not standalone definitions, hypotheses, identities, diagrams,
exact sequences, examples, or theorem interfaces.

The span contains one substantive methodological warning:

* "a morphism of algebraic stacks does not induce a morphism of lisse-etale
  topoi"; arguments traditionally made on that site are to be replaced by
  Cech-covering arguments in the later-defined site `X_smooth`.

This warning is explicitly accounted for here rather than stated as a Lean
proposition.  Neither lisse-etale topoi, the relevant induced-morphism
construction, nor `X_smooth` is defined in this source section or in the
available Mathlib and earlier-chapter APIs.  Introducing an abstract
proposition would leave its mathematical terms unconstrained and would not be
an accurate, usable formalization.  The remaining comments in the span
concern foundations, deferred work, notation, terminology, and references;
they are expository rather than mathematical assertions.
-/
