What should be in the paper:
- Introduction: motivate adding state to ILC.
- Define usage scenario (for instance, specify whether we take one or more changes…)
- Introduce static caching’s core idea: lambda-lift programs, associate a derivative to each function, and make each function produce a “cache” tuple of intermediate results, for use in the derivative. Show examples; use a variant that communicate the idea most clearly. (The early examples might be for an untyped higher-order calculus).
- Introduce variants that are powerful enough to convince reviewers they’re not oversimplified. Present a formalization.
- Argue/evaluate/proof correctness of the transformation.
- Have performance evaluation showing speedups from incrementalization.
- Klaus argues that, together the performance evaluation, we need (at least) either a formalization (and proofs) on a toy variant, or an implementation of the transformation. It’s certainly acceptable that we formalize a small language and use a bigger one (with boring extensions) in the evaluation. He claims that doing the transformation by hand should be acceptable.
- A contribution I’d love is showing that (reusing compiler optimizations) we can optimize programs to reduce what is stored in the cache. That certainly reduces memory consumption and GC pressure (so has an indirect effect on performance), but I have an (unfounded?) hope that it improves time performance beyond those effects (by reducing the overhead of copying those cached values).

Some action items (to refine):
- start sketching a paper
- define contributions
- figure out evaluation benchmarks
- figure out change structures needed for them
- sketch evaluation in pseudocode, refining it further
- continue exploring convenient encodings
- figure out which encoding to use

Open questions:
- in my encoding prototypes, I’m (implicitly) often assuming that some arguments are *not* going to change.
Acar does that as well all the time, but it does *not* fit our story so well. We handled this problem somehow in the PLDI’14 paper, we hinted at an optimization to figure out statically when a change is going to be nil. We could argue that we could use the same optimization; we could add a default handling for when more stuff changes than usual; or we could try to extend our language to allow marking some arguments as not-accepting incremental changes. I think the problem is out of scope for our main contribution, but we still need our claim to fit what we do somehow.
