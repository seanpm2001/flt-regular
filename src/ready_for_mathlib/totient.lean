import algebra.big_operators.basic
import data.nat.totient
import tactic.ring_exp
import algebra.gcd_monoid.basic

open finset
open_locale big_operators

variables {A : Type*} [has_mul A] {B : Type*} [has_mul B] [has_le B]


namespace function

/-- We say that a function `f` is `super_multipicative` if
  `∀ (a b : A), f (a) * f(b) ≤ f(a * b)`. -/
def super_multiplicative (f : A → B) : Prop := ∀ (a b : A), f (a) * f(b) ≤ f(a * b)

end function

namespace nat

open nat

localized "notation `φ` := nat.totient" in nat

lemma gcd_self_pow (p n m : ℕ) : (p^n).gcd (p^m) = p^(min n m) :=
begin
apply dvd_antisymm,

sorry,
rw dvd_gcd_iff,
split,
apply pow_dvd_pow,
simp,
apply pow_dvd_pow,
simp,
end

lemma totient_pow_mul_self (p n m : ℕ) (h : prime p)  :
   φ ((p^n).gcd (p^m)) * φ (p^n * p^m) = φ (p^n) * φ (p^m) * (p^n).gcd (p^m) :=
begin

  by_cases h0: 0 < n,
  by_cases h00: 0 < m,
  have hp := totient_prime_pow h h0,
  have hpp := totient_prime_pow h h00,
  rw hp,
  rw hpp,
  have h20 :  0 < n + m , by {linarith,},
  have hp2 := totient_prime_pow h h20,
  rw pow_add at hp2,
  rw hp2,
  have  hpg := gcd_self_pow p n m,
  rw hpg,
  have hmin : 0 < min n m, by {exact lt_min h0 h00,},
  simp_rw (totient_prime_pow h hmin),
  ring_exp,
  simp_rw ← mul_assoc,
  simp only [succ_pos', tsub_eq_zero_iff_le, mul_eq_mul_right_iff, pow_eq_zero_iff],
  have hh :  ¬ p ≤ 1, by {simp only [h.one_lt, not_le],},
  simp only [hh, or_false],
  simp_rw ← pow_add,
  apply congr_arg (λ (b : ℕ), p ^ b),
  linarith,
  simp only [not_lt, nonpos_iff_eq_zero] at *,
  rw h00 at *,
  simp only [mul_one, one_mul, gcd_one_right, totient_one, pow_zero] at *,
  simp only [not_lt, nonpos_iff_eq_zero] at h0,
  rw h0,
  simp only [gcd_one_left, mul_one, one_mul, pow_zero],
end

theorem mul_ind {P : ℕ → ℕ → Prop}
  (H0 : ∀ (n : ℕ), P 0 n)
  (H1 : ∀ (n m : ℕ), (m.coprime n) → P m  n)
  (H2 : ∀ (p n m: ℕ), (prime p) →  P (p^n) (p^m)) :
  ∀ n m,   P n m :=
begin
sorry,
end

/-- We say that a function `f` satisfies `is_pseudo_mult` if
  `∀ (a b: ℕ), f ( a.gcd b ) * f (a * b) = f (a) * f (b) * (a.gcd b)`. -/
def is_pseudo_mult (f : ℕ → ℕ) : Prop :=
  ∀ (a b: ℕ), f ( a.gcd b ) * f (a * b) = f (a) * f (b) * (a.gcd b)


lemma totient_mul_gen : is_pseudo_mult φ :=

begin
apply mul_ind,
intro n,
simp,
intros n m hnm,
have := totient_mul hnm,
rw coprime at hnm,
rw hnm,
simp [this],
intros p n m hp,
apply totient_pow_mul_self p n m hp,

  /-
 by_cases a.coprime b ,
 have : d = 1, by {simp [coprime] at h, rw h at hab, exact hab,},
 rw this,
 simp,
 apply totient_mul h,
 have hd : 0 < d, by {sorry,},
 rw hab at hd,
 have := exists_coprime hd,
 obtain ⟨n,m, hnm, hn, hm⟩ := this,
 simp_rw ← hab at *,
 rw [hn, hm],
 simp [← mul_assoc],
 by_cases hnd: n.coprime d,
 by_cases hmd: m.coprime d,
 rw totient_mul hnd,
rw totient_mul hmd,
have eq1: ( n*d*m*d = (n* m) * d^2), by {sorry,},
rw eq1,
have hnmd: (n*m).coprime (d^2), by {sorry,},
rw totient_mul hnmd,
rw totient_mul hnm,
simp_rw ← mul_assoc,
have HH := totient_mul_self d,
-/

--rw totient_mul hnd,

end

lemma totient_is_super_multiplicative :  function.super_multiplicative φ :=
begin
  rw function.super_multiplicative,
  intros a b,
  let d:= a.gcd b,
  by_cases d ≠  0,
  {have := totient_mul_gen a b,
  simp at *,
  have hd: 0 < d.totient,  by {apply totient_pos, exact pos_iff_ne_zero.mpr h, },
  by_cases HA : a ≠ 0,
  by_cases HB : b ≠ 0,
  have ha: 0 < a.totient,
    by {apply totient_pos, by_contra H, simp at *, rw H at HA, simp at HA, exact HA,},
  have hb: 0 < b.totient,
    by {apply totient_pos, by_contra H, simp at *, rw H at HB, simp at HB, exact HB},
  have hdd: φ( d ) ≤ d, by {apply totient_le,},
  have hr :  φ (d) * (φ (a) * φ (b)) ≤ φ (d) * φ (a * b) ↔ (φ (a) * φ (b)) ≤ φ (a * b) ,
  by {apply mul_le_mul_left hd,},
  simp_rw ← hr,
  rw this,
  rw mul_comm,
  exact mul_le_mul_left' hdd (φ a * φ b),
  simp at HB,
  rw HB,
  simp,
  simp at HA,
  rw HA,
  simp,
  },
  simp at h,
  simp_rw d at h,
  rw gcd_eq_zero_iff at h,
  simp [h.1],
end



end nat
