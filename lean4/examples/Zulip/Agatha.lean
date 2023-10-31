-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/'Who.20Killed.20Aunt.20Agatha'.20puzzle
-- https://gist.github.com/utensil/17159725e5335f6a9688b7443fe0b3aa
import Std.Logic
import Std.Tactic.RCases
-- import Mathlib.Tactic

variable (u : Type)
variable (lives : u → Prop)
variable (killed hates richer : u → u → Prop)
variable (agatha butler charles : u)

variable (pel55_1 : ∃ x : u, lives x ∧ killed x agatha)
variable (pel55_2_1 : lives agatha)
variable (pel55_2_2 : lives butler)
variable (pel55_2_3 : lives charles)
variable (pel55_3 : ∀ x, lives x → x = agatha ∨ x = butler ∨ x = charles)
variable (pel55_4 : ∀ x y, killed x y → hates x y)
variable (pel55_5 : ∀ x y, killed x y → ¬ richer x y)
variable (pel55_6 : ∀ x, hates agatha x → ¬ hates charles x)

variable (pel55_7 : ∀ x, x ≠ butler → hates agatha x)
variable (pel55_8 : ∀ x, ¬ richer x agatha → hates butler x)
variable (pel55_9 : ∀ x, hates agatha x → hates butler x)

variable (pel55_10 : ∀ x, ∃ y, lives y ∧ ¬ hates x y)
variable (pel55_11 : agatha ≠ butler)
variable (pel55_12 : agatha ≠ charles)
variable (pel55_13 : charles ≠ butler)

theorem result : killed agatha agatha := by
  have ⟨n, ln, kna⟩ := pel55_1
  clear pel55_2_1 pel55_2_2 pel55_2_3
  have labc := pel55_3 n ln
  rcases labc with la | lb | lc
  . rw [la] at kna
    exact kna
  . rw [lb] at kna
    have nrba : ¬richer butler agatha := pel55_5 butler agatha kna
    have hbb : hates butler butler := pel55_8 butler nrba
    have haa : hates agatha agatha := pel55_7 agatha pel55_11
    have hba : hates butler agatha := pel55_9 agatha haa
    have hac : hates agatha charles := pel55_7 charles pel55_13
    have hbc : hates butler charles := pel55_9 charles hac
    have hbe : ¬∃ y, lives y ∧ ¬hates butler y := by
      apply imp_false.mp
      intro he
      rcases he with ⟨e, lnhbe⟩
      have labc := pel55_3 e
      have ⟨le, nhbe⟩ := lnhbe
      have hl := labc le
      rcases hl with ha | hb | hc
      . rw [ha] at nhbe
        contradiction
      . rw [hb] at nhbe
        contradiction
      . rw [hc] at nhbe
        contradiction
    have nhbe : ∃ y, lives y ∧ ¬hates butler y := pel55_10 butler
    contradiction
  . have hca := pel55_4 n agatha kna
    rw [lc] at hca
    have haa := pel55_7 agatha pel55_11
    have nhca := pel55_6 agatha haa
    contradiction
  done