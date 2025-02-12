import field_theory.galois
import linear_algebra.determinant
import data.polynomial.derivative
import data.matrix.notation
import data.multiset.basic
import algebra.module.basic
section resultant
variables {R : Type*}
open matrix polynomial
open_locale polynomial
-- TODO redefine this in terms of a matrix.from_column_blocks, or maybe dont as types of
-- indices will be weird
noncomputable theory
/-- The Sylvester matrix of two polynomials -/
def sylvester_matrix [semiring R] (p q : polynomial R) :
  matrix (fin $ p.nat_degree + q.nat_degree) (fin $ p.nat_degree + q.nat_degree) R :=
λ i j, if (i : ℕ) < q.nat_degree
       then (p * X ^ (i : ℕ)).coeff j
       else (q * X ^ (i - q.nat_degree : ℕ)).coeff j
-- example : sylvester_matrix (X : polynomial ℕ) X = ![![0, 0], ![1,1]] :=
-- begin
--   norm_num [sylvester_matrix],
--   ext,
--   simp,
--   intros a h hh, fin_cases h,
--   norm_num [hh],
--   rw hh,
--   admit,
--   admit,
-- end

example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1, by simp⟩ ⟨1, by simp⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1, by simp⟩ ⟨0, by simp⟩ = 0:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0, by simp⟩ ⟨1, by simp⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0, by simp⟩ ⟨0, by simp⟩ = 0:=
by norm_num [sylvester_matrix]

/-- The resultant of two polynomials -/
def resultant [comm_ring R] (p q : polynomial R) : R := det (sylvester_matrix p q)
-- include (-1)^(n(n-1)/2)/a_n part by updating sylvester first col
/-- The discriminant of a polynomial defined as the resultant of p and its derivative -/
def discriminant' [comm_ring R] (p : polynomial R) : R := resultant p p.derivative

-- translation invariance
-- scaling by a^n(n-1)
-- reversal invariance
-- degree preserving ring maps
-- disc prod is prod discs times resultant square

lemma discriminant'_C_mul_X_add_C [comm_ring R] {b c : R} (h : b ≠ 0) :
  discriminant' (C b * X + C c) = b := --big note: this used to be `discriminat' = 1`!!
begin
  have : (C b * X + C c).nat_degree = 1,
  { apply nat_degree_eq_of_degree_eq_some,
    simp only [degree_add_C, degree_C_mul_X h, ←with_bot.coe_zero,
               ←with_bot.coe_one, with_bot.coe_lt_coe, zero_lt_one] },
  -- I'm squeezing the simps to make working on the file faster, if later someone wants to put
  -- back the original one: `simp only [discriminant', resultant, sylvester_matrix]`.
  simp only [discriminant', resultant, sylvester_matrix, tsub_zero, add_zero, derivative_X,
             mul_one, derivative_add, derivative_mul, coeff_C_mul, zero_mul, if_false,
             nat_degree_C, zero_add, derivative_C, not_lt_zero'],
  convert_to det (λ (i j : fin 1), b * (X ^ ↑i).coeff ↑j) = b,
  { congr, any_goals { rw [this, nat_degree_C, add_zero] } },
  norm_num
end
-- does this work without taking n ≥ 2? be careful with signs
-- Eric: doesn't work for n=0 or n=1:
/-
  (with n = 0 substituted)
  simp only [mul_one, nat.cast_zero, add_left_neg, pow_zero],
  rw [add_right_comm, ←C_add, add_comm, discriminant'_C_mul_X_add_C]

  (with n=1 substituted)
  simp only [neg_mul_eq_neg_mul_symm, one_mul, pow_one, nat.cast_one, pow_zero],
  rw [←add_mul, ←C_add, discriminant'_C_mul_X_add_C]
-/
lemma discriminant'_mul_X_pow_add_C_mul_X_add_C [comm_ring R] {a b c : R}
  (ha : a ≠ 0) : ∀ {n : ℕ}, 2 ≤ n → discriminant' (C a * (X : polynomial R)^n + C b * X + C c) =
    -(n - 1)^(n-1) * b^n + n^n * a^(n-1) * (-c)^(n-1)
| 0     hn := (hn.not_lt zero_lt_two).rec _
| 1     hn := (hn.not_lt one_lt_two).rec _
| (n+2) _ := begin
  sorry
end

-- this should give quadratic as b^2 - 4ac and depressed cubic as
-- -4ac^3 - 27 a^2d^2 = -(n-1)^(n-1)a c ^n - n^n a^(n-1) b^(n-1)

-- example of computing this thing
example : discriminant' ((X : ℚ[X]) ^ 5 + -X + -1) = 3381 :=
begin
  have := @discriminant'_mul_X_pow_add_C_mul_X_add_C _ _ (1 : ℚ) (-1) (-1) one_ne_zero 5,
  norm_num at this,
  exact this,
end
end resultant
