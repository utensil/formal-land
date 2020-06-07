> chakravala: Saw @Hugo Hadfield is looking at agda, which is also a language i am interested in, it has dependent inductive types, which is cool

I've also spent some time on Agda, but have chosen Lean as the target language. Lean also has dependent inductive types and so many amazing features and it’s rapidly evolving. It’s written in C++ and Lean 4 will be written mostly in itself and compiles natively(almost completely compatible with Lean 3). It has a large and sophisticated mathematical library designed and backed by a community that has many pure mathematicians.
I particularly enjoy its free and readable syntax friendly to mathematicians, the 5 combinable proof paradigms it supports, the smooth and informative experience of interactive proving, the power and efficiency of its type class system for abstraction, its meta programming framework for developing automatic tactics,  its ability to integrate with other ATP tools such as Vampire, Sledgehammer and ML algorithms , its warm-hearted community on Zulip. It truly unleashes full spectrum of possibilities of formalization, a dream language.

Its mathematical library `mathlib` is already well equipped, but there’re also many areas to fill in. Formalizing GA in Lean would have a significant contribution back to mathlib, just like previous and ongoing formalization projects.

> Brombo: Do you have a link to "lean" for us?

I have lots of links about it at https://github.com/pygae/lean-ga/blob/master/docs/misc/related.md (not well organized yet).
If I were to choose one link it would be the the community homepage  https://leanprover-community.github.io instead of the old official homepage. And one more would be the manifest page https://lean-forward.github.io/ .
To name one or a few papers, that would be https://arxiv.org/abs/1910.09336 ,  https://arxiv.org/abs/1910.12320 , and the work-in-progress The sphere eversion project https://leanprover-community.github.io/sphere-eversion/blueprint/sect0001.html .
A great game (like @enki ‘s wedge game) for someone who never had contact with formalization is https://github.com/ImperialCollegeLondon/natural_number_game and many games such as https://github.com/ImperialCollegeLondon/group-theory-game . The most recommended tutorial is https://leanprover.github.io/theorem_proving_in_lean/ . But I also like https://github.com/blanchette/logical_verification_2020/raw/master/hitchhikers_guide.pdf , https://leanprover.github.io/logic_and_proof/ , https://github.com/leanprover-community/tutorials for they are demonstrating different aspects of the language. 

There's also a great overview slide for mathlib in Lean https://lean-forward.github.io/lean-together/2019/slides/hoelzl.pdf , to feel how the mathematical objects and theorems are represented. Lean makes heavy use of unicode characters to make it more accessible to people who have little CS background but some familiarity with mathematical notations.

Just found a cool proof in mathlib demonstrating 4 proof paradigms combined together, I’m pretty sure everyone could have a general idea about what this proof is talking about.

```lean
class has_dist (α : Type*) := (dist : α → α → ℝ)

instance has_dist_metric_quot {α : Type u} [premetric_space α] : has_dist (metric_quot α) :=
{
  dist := quotient.lift₂ (λp q : α, dist p q)
  begin
    assume x y x' y' hxx' hyy',
    have Hxx' : dist x  x' = 0 := hxx',
    have Hyy' : dist y  y' = 0 := hyy',
    have A    : dist x  y  ≤ dist x' y' := calc
                dist x  y  ≤ dist x  x' + dist x' y  : premetric_space.dist_triangle _ _ _
                       ... = dist x' y               : by simp [Hxx']
                       ... ≤ dist x' y' + dist y' y  : premetric_space.dist_triangle _ _ _
                       ... = dist x' y'              : by simp [premetric_space.dist_comm, Hyy'],
    have B    : dist x' y' ≤ dist x  y   := calc
                dist x' y' ≤ dist x' x + dist x y'   : premetric_space.dist_triangle _ _ _
                       ... = dist x  y'              : by simp [premetric_space.dist_comm, Hxx']
                       ... ≤ dist x  y + dist y y'   : premetric_space.dist_triangle _ _ _
                       ... = dist x  y               : by simp [Hyy'],
    exact le_antisymm A B
  end
}
```

