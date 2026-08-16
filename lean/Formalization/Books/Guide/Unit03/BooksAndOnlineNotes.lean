/-!
# A Guide to the Literature, Chapter 3: Books and online notes

The source span `books/guide.tex` from the numbered section
`Books and online notes` through the next top-level section is a bibliography
with annotations.  It contains five references:

* Laumon--Moret-Bailly, *Champs Algébriques*;
* the Stacks Project;
* Geraschenko's lecture notes for Martin Olsson's class on stacks;
* the online notes *Algebraic stacks* by Behrend, Conrad, Edidin, Fantechi,
  Fulton, Göttsche, and Kresch; and
* Olsson, *Algebraic spaces and stacks*.

The descriptions of the books and the statements about what they cover are
reading guidance and scope descriptions, not definitions, hypotheses,
identities, diagrams, exact sequences, examples, or theorem assertions in
the source chapter.  In particular, the sentence saying that the lecture
notes cover the equivalence between being Deligne--Mumford and having
unramified diagonal describes a topic of the notes; it does not state the
theorem in a formal ambient category.

The available project APIs do not provide a native category of algebraic
stacks together with predicates for Deligne--Mumford stacks and unramified
diagonals.  The existing stack and gerbe interfaces are useful for later
formalizations, but they do not determine those missing notions.  Adding
unconstrained predicates merely to state the bibliographic topic would not
be an accurate or usable declaration, so this source-level coverage is
recorded here instead.

The section also reports a historical warning about an error in the
functoriality of the lisse--étale site in chapter 12 of *Champs Algébriques*,
and says that Martin Olsson patched it.  This is a bibliographic warning,
not a mathematical proposition in this section; neither the lisse--étale
site nor the cited patch is defined here, so no Lean declaration is added.
The mentions of quasi-coherent sheaves, the Keel--Mori theorem,
cohomological descent, gerbes, and the Brauer group likewise identify topics
covered by the lecture notes rather than source assertions to formalize here.
-/
