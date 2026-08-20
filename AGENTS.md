This is an ambitious, massive project to formalize the Stacks algebraic geometry textbook.
* Commit as you go. Use Conventional Commits-ish style.
* Codex: use timeouts of at least 30 minutes for `wait`, `wait_agent`, and `write_stdin`.
* DO NOT restart the PAF orchestrator unless EXPLICITLY instructed to.

## Lean guidelines

1. **Keep declarations small.** Break long proofs into helper lemmas with explicit statements. This gives Lean smaller elaboration problems and avoids repeatedly re-inferring large intermediate terms.
2. **Add type annotations to important intermediate terms.** Prefer `have h : T := ...` over `have h := ...` when `T` is nontrivial. Explicit types reduce metavariable creation and constrain elaboration early.
3. **Do not rely on expensive definitional equality.** If two complicated expressions are mathematically the same but only become identical after unfolding, use an explicit lemma or rewrite to connect them instead of making Lean discover this automatically.
4. **Avoid unfolding large definitions in downstream proofs.** Prove simple API lemmas about a definition once—e.g. application, membership, equality, map, or simp lemmas—and reason through those instead of repeatedly using `simp [BigDefinition]` or `unfold BigDefinition`.
5. **Control `simp` on large expressions.** If a proof is slow, prefer `simp only [lemma1, lemma2, ...]` or perform the key rewrite explicitly before simplifying. Broad `simp` can repeatedly traverse and rewrite very large terms.
6. **Avoid repeated typeclass search.** If Lean repeatedly needs the same complicated instance, construct or select it once with `letI`/`haveI` and reuse it. Failed or ambiguous instance searches can be especially expensive.
7. **Name large repeated expressions.** If the same large sum, map, subtype, structure expression, etc. appears repeatedly, bind it with `let`, `set`, or a helper definition rather than elaborating and comparing the full expression everywhere.
8. **Do not fix slow proofs by increasing `maxHeartbeats`.** A declaration taking seconds usually indicates excessive inference, unfolding, simplification, or automation. Change the proof structure instead of merely allowing more work.
9. **Treat unexpectedly slow declarations as bugs.** Ordinary lemmas should generally elaborate in well under a second; investigate multi-second declarations before building more code on top of them.
