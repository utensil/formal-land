I've been reading (and trying out the exercises in)  many tutorials for Lean. The knowledge absorbed from scattered sources is becoming a memory  burden and I have at least the personal need to create a cheat sheet that has high information density and is well organized for quick reference.

Apparently, I would not be the first to need such a cheat sheet, so I searched Zulip to see if there're already such cheat sheets. But I could not find one that's ideal.

There're:

- @**Kevin Buzzard** 's cheat sheets [1](https://gist.github.com/utensil/dc635f2991255f76d8da797efdabbf15#file-kbuzzard-lean-tactic-guide-md) and [2](https://gist.github.com/utensil/dc635f2991255f76d8da797efdabbf15#file-kbuzzard-lean-tactics-md)
- @**Patrick Massot|110031** 's cheat sheet mentioned [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/the.20complex.20number.20game/near/198480780) which is [in French](https://www.imo.universite-paris-saclay.fr/~pmassot/enseignement/math114/tactiques.pdf), translated into English [here](https://gist.github.com/utensil/dc635f2991255f76d8da797efdabbf15#file-pmassot-lean-tactics-md)
- https://github.com/jldodds/coq-lean-cheatsheet which is a little dated and not so complete, there're better ones in Coq world such as
  - http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf
  - https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html

What I have in mind is something as rich as https://cheats.rs/ ( it's a long page, please have a quick scroll-down ), it covers all most every aspect of the language and the ecosystem in a concise manner with links to the original sources (there're many open books/tutorials in Rust world too), incorporating something like in [here](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html) for tactics, perhaps start with something even shorter like https://cljs.info/cheatsheet/ .

Its structuring of contents and its tech stack (see [its source](https://github.com/ralfbiedert/cheats.rs/)) are mostly reusable for Lean. I'm motivated to create a prototype and a skeleton for Lean based on it, at least cover the part I know of, distilling information from the books/tutorials that I've read. Just post here (before I even start doing so) to see if anyone has some plans/needs similar in mind.

@_**Bryan Gin-ge Chen|123965** [said](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.20Cheat.20Sheet/near/200923247):
```quote
Any suggestions for improvements to the current [tactic docs](https://leanprover-community.github.io/mathlib_docs/tactics.html) are welcome too.
```

As a beginner, I have a not so great first impression of the current tactic docs, I only understand the doc of a tactic after I have a concept about what the tactic does. I'm constantly confused about:

- Direction: what does the tactic applies to? the goal, the hypotheses, or both? Which tactic should I use if I need to do the same to the opposite direction? (backward proof v.s. forward proof)
- Scenario: under what specific circumstances should I think about using the tactic?
- Scope: what family does the tactic belong to? what scope of the problem does the family solve? (This is partially addressed by the tags, I'll get back to its issues later)
- What: what does the tactics do?
- Variants: are there slightly modified versions to also do xxx, yyy?
- What else: what else can I try in a similar circumstance? (it's like an ordered tactic chain, such as `ac_refl`, `cc`, `abel` etc., one stronger than the other)
- Style: which tactics to use if I want to do the same in another proof style? 
- Reduce: what if I want to have more control on a tactics that's too smart? (such as from `simp` to `squeeze_simp`, `simp_only`, `rw` etc.)
- Simplify:  how can I simplify a series of steps( which seem to have a pattern ) to just one or few tactics?
- Partners: which tactics should I use together with this tactic?
- Parameters: what parameters can I pass to the tactics? what do they control? can I just copy-paste a part of the expression? why sometimes copy-paste doesn't work? when can Lean infer them for me?
- Equivalents: in informal mathematical proofs, in Coq etc. 

These questions are usually addressed by searching mathlib source for examples and searching Zulip for Q&A, and most tutorials answered some of them.

The above has been posted as an issue at https://github.com/leanprover-community/mathlib/issues/3088 .

There're some initial efforts on this at https://github.com/utensil/lean-cheatsheet .
