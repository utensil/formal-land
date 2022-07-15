Chris M:
> **Some questions**:
> * **Is there broadly one correct (i.e. with good style) way to formalize groups, rings, abelian groups, in Lean?** Are there good guidelines somewhere?
> * **What's the best way to get started on internalizing the best practices around formalizing groups, abelian groups, etc?** I've read that we should define Group as a type class, not as a type, but other than that, I'm not sure how to do it. Would I get the knowledge required to formalize these things by going through the following tutorial? https://leanprover-community.github.io/mathematics_in_lean/
> * My plan is to *redo* basic formalizations on groups and rings and compare it with the existing library. **Is this a good idea or is there a better approach?**

To answer your Q1, 

- [The Lean Mathematical Library paper](https://arxiv.org/abs/1910.09336) is probably the best document on the design of the algebra library, particularly "4 Type Classes" and "5 Linear Algebra", they explained the design rationale and how it leverages the features available in Lean.
- I also like "3 Lean and its Mathematical Library" in the paper [Formalising perfectoid spaces](https://arxiv.org/abs/1910.12320), the introduction is concise and exactly for the purpose of explaining the infrastructure to formalize a theory. You'll probably found some other interesting introduction on this in other formalizing papers, that's one good thing that a paper is mandatory to explain some backgrounds, you get a dedicated crash course usually more suited for the preparation to doing something than a general textbook or reference. 
- "2. The Lean interactive theorem prover" and "3. The Lean mathematical library" in  [Diagram Chasing in Interactive Theorem Proving](https://pp.ipd.kit.edu/uploads/publikationen/himmel20bachelorarbeit.pdf) is my favorite just found very lately, it has really thorough explanation on developing a theory and proving things about it, it also completely weaves the Lean code with the usual math natural language expression together.

There're usually more than one way to formalize a piece of mathematics and you would not truly know the limitation of an approach until you hit a hard roadblock later when trying to prove something or state something in a natural way. So there would be quite some trial and error involved in the process. I recall an old Zulip chat said that you can only know how to do it right unless you have done it wrong many times. (And internalize such best practices or some intuition during the process)

Because a good definition can only be learned by bad proofs, it's important to sharpen the proving skill first (or at the some time) when you try to state some definitions and theorems for some mathematics. As a practice, groups etc. are good because they are well known and just abstract enough, but I would recommend something that's not in mathlib yet, such as the todo ones in https://leanprover-community.github.io/overview.html and try to do them in a similar way as the adjacent mathematical structures that's already in mathlib.

If you're particularly interested in group theory etc. , you might want to try and improve the https://github.com/ImperialCollegeLondon/group-theory-game . But in general, #mil is a really good practice which is quite even for different areas of (elementary) mathematics so you'll get a hang of anything you might be interested to do very quickly. And to answer your Q2, I guess not, #mil emphasizes tactics for proving and not how to develop a theory (but I also don't know a general good guideline for that except reading the docs of existing formalized math).

And the last two paragraphs might have partially answered your Q3.

Scott Morrison:

> It turns out that writing "library quality" definitions is much more subtle than just writing definitions, and requires some experience that you don't automatically have even if you know maths+programming. So it's probably a good idea, while learning, to pick projects that don't involve lots of interacting definitions, and instead look for topics where the definitions are either already set up for you, or are very straightforward, and concentrate on learning to steer Lean by writing proofs, first.

> (Just as examples as issues that you'll end up knowing about by the time you're writing "library quality definitions":
>
> - bundling/unbundling
> - how/why/what for typeclasses
> - old/new structures
> - diamond inheritance
> - definitional equality
> - reducibility
> - simp normal forms...
>
> None of which you need to have your head around, or have informed opinions about, to write proofs. :-)
