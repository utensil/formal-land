I, very new to [Lean](https://leanprover-community.github.io/) and [its Zulip Chat Community](https://leanprover.zulipchat.com/), would like to share my experience with Lean prover on trying to prove a trivial proposition in four proof styles supported by Lean. It's gonna feel verbose(for describing the intuition I established during the interactions with Lean), for that, I apologize in advance.

The proposition is from [3.3.3. Negation and Falsity, Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html#negation-and-falsity) (which is where I'm at in the walkthrough of TPIL:

For any two propositions `p` and `q`,  assuming `p → q` and `¬q`, Then `¬p`.

TPIL expresses the proposition like this:

```lean
constants p q: Prop
example (hpq : p → q) (hnq : ¬q) : ¬p := sorry
```

As a beginner in Lean, I find it particularly important to be able to move things around and transform between different appearances of the same thing in one's mind, since the expressive Lean gives us too much liberty at how to express the same idea. Just move them around in the code editor (for me that's VSCode with Lean extension installed) and check the result against Lean. From these muscle memories (of success or errors),  a mental model grows out naturally.

Since `example` is just a nameless  `theorem/lemma`, we can rewrite the above to the following by naming it `play`:

```lean
lemma play (hpq : p → q) (hnq : ¬q) : ¬p := sorry
```

Benefit from [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), `theorem/lemma` shares the same basic grammar structure as `def`, i.e. `def name : type := value`, so the above is no different from:

```lean
-- Play with `hpq` and `hnq` directly
def play₁ (hpq : p → q) (hnq : ¬q) : ¬p := play hpq hnq
```

Also, "parameters" are just syntax sugar in Lean, so the above is also the same as:

```lean
-- Need Lambda to introduce binding names with the type
def play₂ : (p → q) → (¬q) → ¬p :=  λ hpq, λ hnq, play hpq hnq
```

## Structural Proof

OK, now we can move types, parameters around, let's go back to the original proposition, TPIL demonstrates a structural proof for it:

```lean
example (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p,
show false, from hnq (hpq hp)
```

I failed to wrap my head around it until I read it carefully again and noticed `¬p` is equivalent to `p → false`, so the idea is to assume p and prove false. This is accomplished by applying `p → q` and then `q → false`(`¬q`).

## Tactic Mode proof

Next thing I try is to convert it to a Tactic Mode proof(which is best supported by the VS Code extension but hard to read without it), starting with:

```lean
example (hpq : p → q) (hnq : ¬q) : ¬p :=
begin
sorry
end
```

The goal (when the cursor is after `begin`) is

```
p q : Prop,
hpq : p → q,
hnq : ¬q
⊢ ¬p
```

By realizing `intro` will convert a goal like `⊢ a → b` to `ha : a ⊢ b` and again `¬p` is equivalent to `p → false`,  inputting `intro hp,` we have the following goal(when the cursor is after the comma):

```
p q : Prop,
hpq : p → q,
hnq : ¬q,
hp : p
⊢ false
```

`apply` is the opposite of `intro` (in a way), it can turn a goal like`b` into `a` by a hypothesis `a → b`. Basically, it's just a function application(applying a function of the type `a → b`), while `intro` is actually a lambda that creates such a function. That's why I accepted the commas (instead of semicolons or nothing) at the end of each line of a proof, it's the same as the one in `λ a : ℕ, a + 1`.

So assuming we have  `a → b`, when we want to leave `b` as our goal, we use `intro`, when we want to leave `a` as our goal, we use `apply`. A pretty straight forward, left-hand-or-right-hand choice.

So we work our way backwards: apply `q → false` to get `q`, apply `p → q` to get `p`, then we have the proof as:

```lean
example (hpq : p → q) (hnq : ¬q) : ¬p :=
begin
intro hp,
apply hnq,
apply hpq,
sorry
end
```

and the goal (before `sorry`) as:

```
p q : Prop,
hpq : p → q,
hnq : ¬q,
hp : p
⊢ p
```

And this goal is `exact`ly our initial assumption `hp : p` so we finish the proof by `exact hp`.

A Tactic Mode proof is really relying on the interactive hints of the current goals. While the writing process is enjoyable, the written code is hard to read. By narrowing my mind to the current goal during writing, I can't tell what's going on if I step back and look at the whole proof:

```lean
example (hpq : p → q) (hnq : ¬q) : ¬p :=
begin
intro hp,
apply hnq,
apply hpq,
exact hp
end
```

## Term Mode proof

To truly understand the whole Tactic Mode proof, we must completely forget tactics and focus on the commas and replace all `intro` with a `λ`,  replace all `apply`s as function calls while the `exact` is the ultimate parameter so we see a Term Mode proof:

```
example (hpq : p → q) (hnq : q → false) : p → false :=
λ hp, hnq (hpq hp)
```

Writing a Term Mode proof can use a similar degree of help in VS Code, by prompting types instead of prompting goals:

When we write `λ hp, ` and type a random identifier such as `p`, Lean will complain about "type mismatch" and we'll know the right type and simply call a function with the expected type (recall that `p → q` is a hypothesis and also a function that eats something with type `p` and emits something with type `q`). Now the game switched from fulfilling goals to filling parameters of functions, type theory in action is fun!

## Calc Mode proof

Finally, to my favourite Calc mode. I like it very much since it resembles the experience of pen and paper calculation/proof. Not completely, since we can't do something to both the left-hand side and right-hand side.

To use the Calc Mode proof, we need something like an equation. `¬p` is not one but `p → false` is:

```
example (hpq : p → q) (hnq : q → false) : p → false := sorry
```

I'm a bit nervous when I typed `calc` and see nothing back from Lean. But then I try to forget the computer and start writing on the imaginary paper:

```lean
example (hpq : p → q) (hnq : q → false) : p → false :=
calc p → q       : sorry
...    → false   : sorry
```

Now my brain is doing all the thinking and I only have to find the computer excuse names back to replace the `sorry`s. It's surprisingly easy:

```lean
example (hpq : p → q) (hnq : q → false) : p → false :=
calc p → q       : hpq
...    → false   : hnq
```

The excuse names(hypothesis) themselves are pretty dumb and you only feel like applying rewrite rules when your cursor is on a hypothesis and Lean shows you its type. To entertain myself a bit, I rewrite the above to:

```lean
example (p_to_q : p → q) (q_to_false : q → false) : p → false :=
calc p → q       : p_to_q
...    → false   : q_to_false
```

## Back to Structural Proof

When I first see the structural proof, I thought it means to prove `¬p`, simply assume p and it leads to a contradiction, but it's not the logic of that proof, so with a little search, I wrote:

```lean
example (hpq : p → q) (hnq : ¬q) : ¬p :=
by_contradiction
(assume hnnp : ¬¬p,
have hp : p, from sorry,
have hq : q, from sorry,
show false, from sorry)
```

Writing a structural proof is a bit like writing a Calc Mode proof, we do it by first `assume`, then write down the intermediate steps using `have`s and end it with a final `show` of the final target. Then we work out things after `, from`, just like how we work out what's after the colons in a Calc Mode proof:

```lean
open classical

example (hpq : p → q) (hnq : ¬q) : ¬p :=
by_contradiction
(assume hnnp : ¬¬p,
have hp : p, from by_contradiction hnnp,
have hq : q, from hpq hp,
show false, from hnq hq)
```

## Conclusion

It's really a trivial proposition and only very elementary keywords are involved in the proofs, but I'm so excited about being able to write all four styles of proofs and finding out how I feel about each of them. Open questions are:

* Am I missing something or there's little pedagogical material on writing non-trivial proofs using all four styles?
* Are there automatic tools to convert the four styles to each other? ( Is it always possible?)
* Is there on-going efforts to resemble more of the pen-and-paper experience(e.g. manipulate both sides of an equation)?
