/-
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Types.20that.20should.20be.20equal
https://gist.github.com/adamtopaz/84315ae5b11319013707b2d0804fb37e
-/

import ring_theory.algebra
import linear_algebra

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]

inductive pre
| of : M → pre
| zero : pre
| one : pre
| mul : pre → pre → pre
| add : pre → pre → pre
| smul : R → pre → pre

namespace tensoralg
def lift_fun {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] A) : pre R M → A := 
  λ t, pre.rec_on t f 0 1 (λ _ _, (*)) (λ _ _, (+)) (λ x _ a, x • a)

def rel : (pre R M) → (pre R M) → Prop := λ x y,
  ∀ (A : Type*) (h1 : ring A), by letI := h1; exact
  ∀ (h2 : algebra R A), by letI := h2; exact 
  ∀ (f : M →ₗ[R] A), 
  (lift_fun R M f) x = (lift_fun R M f) y

def setoid : setoid (pre R M) := ⟨rel R M,
begin
  refine ⟨_,_,_⟩,  
  { intros x _ _ _ _ _ _ , refl, },
  { intros x y h _ _ _ _  _ _, symmetry, apply h, },
  { intros x y z h1 h2 _ _ _ _ _ _, rw [h1,h2], },
end⟩
end tensoralg

def tensoralg := quotient (tensoralg.setoid R M) -- the tensor algebra.

namespace tensoralg
instance : ring (tensoralg R M) := 
{ zero := quotient.mk' pre.zero, 
  one := quotient.mk' pre.one,
  add := λ x y, quotient.lift_on₂' x y 
  (λ a b, quotient.mk' $ pre.add a b) 
  begin
    intros a1 a2 b1 b2 h1 h2,
    dsimp only [],
    apply quotient.sound',
    intros B _ _ _ _ g, 
    letI := h1_1,
    change (lift_fun R M g) a1 + (lift_fun R M g) a2 = (lift_fun R M g) b1 + (lift_fun R M g) b2,
    specialize h1 B _ _ g,
    specialize h2 B _ _ g,
    rw [h1, h2],
  end,
  mul := λ x y, quotient.lift_on₂' x y 
  (λ a b, quotient.mk' $ pre.mul a b) 
  begin
    intros a1 a2 b1 b2 h1 h2,
    dsimp only [],
    apply quotient.sound',
    intros B _ _ _ _ g, 
    letI := h1_1,
    change (lift_fun R M g) a1 * (lift_fun R M g) a2 = (lift_fun R M g) b1 * (lift_fun R M g) b2,
    specialize h1 B _ _ g,
    specialize h2 B _ _ g,
    rw [h1, h2],
  end,
  neg := λ x, quotient.lift_on' x 
  (λ a, quotient.mk' $ pre.smul (-1 : R) a) 
  begin
    intros a b h,
    dsimp only [],
    apply quotient.sound',
    intros B _ _ _ _ g, 
    letI := h2,
    change (-1 : R) • ((lift_fun R M g) a) = (-1 : R) • ((lift_fun R M g) b),
    specialize h B _ _ g,
    rw h,
  end,
  add_assoc :=
  begin
    intros a b c,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a + G b + G c = G a + (G b + G c),
    rw add_assoc,
  end,
  zero_add := 
  begin
    intros a,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change 0 + G a = G a,
    rw zero_add,
  end,
  add_zero := 
  begin
    intros a,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a + 0 = G a,
    rw add_zero,
  end,
  add_left_neg := 
  begin
    intros a,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change (-1 : R) • G a + G a = 0,
    simp,
  end,
  add_comm := 
  begin
    intros a b,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a + G b = G b + G a, rw add_comm,
  end,
  mul_assoc := 
  begin
    intros a b c,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a * G b * G c = G a * (G b * G c),
    rw mul_assoc,
  end,
  one_mul := 
  begin
    intros a,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change 1 * G a = G a,
    rw one_mul,
  end,
  mul_one := 
  begin
    intros a,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a * 1 = G a,
    rw mul_one,
  end,
  left_distrib := 
  begin
    intros a b c,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change G a * (G b + G c) = _,
    rw left_distrib, refl,
  end,
  right_distrib := 
  begin
    intros a b c,  
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change (G a + G b) * G c = _,
    rw right_distrib, refl, 
  end, }

instance : has_scalar R (tensoralg R M) := ⟨λ x y, quotient.lift_on' y 
  (λ a, quotient.mk' $ pre.smul x a) 
  begin
    intros a b h, 
    dsimp only [],
    apply quotient.sound',
    intros B _ _ _ _ g, 
    letI := h2,
    change x • ((lift_fun R M g) a) = x • ((lift_fun R M g) b),
    specialize h B _ _ g,
    rw h,
  end⟩

instance : algebra R (tensoralg R M) := 
{ to_fun := λ r, r • 1,
  map_one' := 
  begin
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change (1 : R) • (G pre.one) = G pre.one,
    rw one_smul,
  end,
  map_mul' := 
  begin
    intros x y, 
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change (x * y) • (1 : B) = (x • 1) * (y • 1),
    simp [mul_smul],
  end,
  map_zero' := 
  begin
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change (0 : R) • (1 : B) = 0,
    rw zero_smul,
  end,
  map_add' := 
  begin
    intros x y, 
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change (x + y) • (1 : B) = (x • 1) + (y • 1),
    rw add_smul,
  end,
  commutes' := 
  begin
    intros r x, 
    dsimp only [],
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change r • (1 : B) * G x = G x * (r • 1),
    simp,
  end,
  smul_def' := 
  begin
    intros r x,  
    dsimp only [],
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    letI := h1,
    change r • G x = (r • 1) * G x,
    simp,
  end,
  ..show has_scalar R (tensoralg R M), by apply_instance }

def lift {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] A) : tensoralg R M →ₐ[R] A := 
{ to_fun := λ a, quotient.lift_on' a (lift_fun _ _ f) 
  begin
    intros a b h,  
    apply h,
  end,
  map_one' := rfl,
  map_mul' := 
  begin
    intros x y, 
    letI := tensoralg.setoid R M,
    rcases quotient.exists_rep x with ⟨x,rfl⟩,
    rcases quotient.exists_rep y with ⟨y,rfl⟩,
    change quotient.lift_on _ _ _ = quotient.lift_on _ _ _ * quotient.lift_on _ _ _,
    simp_rw quotient.lift_on_beta,
    refl,
  end,
  map_zero' := rfl,
  map_add' := 
  begin
    intros x y, 
    letI := tensoralg.setoid R M,
    rcases quotient.exists_rep x with ⟨x,rfl⟩,
    rcases quotient.exists_rep y with ⟨y,rfl⟩,
    change quotient.lift_on _ _ _ = quotient.lift_on _ _ _ + quotient.lift_on _ _ _,
    simp_rw quotient.lift_on_beta,
    refl,
  end,
  commutes' := 
  begin
    intros r, 
    letI := tensoralg.setoid R M,
    change quotient.lift_on (r • 1) _ _ = _,
    change r • ((lift_fun R M f) pre.one) = _,
    have : (algebra_map R A) r = r • 1, by refine algebra.algebra_map_eq_smul_one r,
    rw this, clear this,
    refl,
  end }

def univ : M →ₗ[R] (tensoralg R M) := 
{ to_fun := λ m, quotient.mk' $ pre.of m,
  map_add' := 
  begin
    intros x y, 
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change g (x + y) = g x + g y,
    refine is_add_hom.map_add ⇑g x y,
  end,
  map_smul' := 
  begin
    intros x y, 
    apply quotient.sound',
    intros B _ _ _ _ g,
    letI := h2,
    let G := lift_fun R M g,
    change g (x • y) = x • g y,
    refine linear_map.map_smul g x y,
  end }

theorem univ_comp_lift {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] A) : 
  (lift R M f) ∘ (univ R M) = f := rfl

theorem lift_unique {A : Type*} [ring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensoralg R M →ₐ[R] A) : g ∘ (univ R M) = f → g = lift R M f := 
begin
  intro hyp,
  ext, 
  letI := tensoralg.setoid R M,
  rcases quotient.exists_rep x with ⟨x,rfl⟩,
  let G := lift_fun R M f,
  induction x,
  { change (g ∘ (univ R M)) _ = _,
    rw hyp,
    refl },
  { change g 0 = 0,
    exact alg_hom.map_zero g },
  { change g 1 = 1,
    exact alg_hom.map_one g },
  { change g (⟦x_a⟧ * ⟦x_a_1⟧) = _, 
    rw alg_hom.map_mul,
    rw x_ih_a, rw x_ih_a_1,
    refl },
  { change g (⟦x_a⟧ + ⟦x_a_1⟧) = _,
    rw alg_hom.map_add,
    rw x_ih_a, rw x_ih_a_1,
    refl },
  { change g (x_a • ⟦x_a_1⟧) = _,
    rw alg_hom.map_smul,
    rw x_ih, refl },
end

end tensoralg