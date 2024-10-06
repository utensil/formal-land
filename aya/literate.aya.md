# Literate Programming in Aya

This is based on (outdated) [Introduction to literate Aya](https://blog.kiva.moe/posts/intro-literate-aya.html) and code snippets from `haskeller-tutorial.aya`.

## Defining a type

```aya
open inductive Nat | zero | suc Nat
```

## Defining an operation

```aya
example def infixl <+> Nat Nat : Nat
| 0, n ⇒ n
| suc m, n ⇒ suc (m <+> n)

overlap def infixl <+> Nat Nat : Nat
| 0, n => n
| n, 0 => n
| suc m, n => suc (m <+> n)
```

## Meta-variables

```aya
example def infixl [+] (a n : Nat) : Nat elim a
| 0 ⇒ n
| suc m ⇒ suc {??}
```

## Compilation errors

```aya
def foo =>
```

## Math formulas

$$
\begin{align*}
\Gamma,\Delta,\Theta ::=  & \quad \varnothing      \\[-0.3em]
                     \mid & \quad \Gamma , x : A   \\[-0.3em]
\Sigma         ::=  & \quad \varnothing            \\[-0.3em]
               \mid & \quad \Sigma,\mathrm{decl}   \\[-0.3em]
\end{align*}
$$

