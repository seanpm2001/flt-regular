/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.polynomial.field_division
import number_theory.number_field

import number_theory.cyclotomic.field.basic

noncomputable theory
open number_field cyclotomic_field polynomial

namespace cyclotomic_field

section
variables (p : ℕ) [hn : fact (0 < p)] (K : Type*) [field K] [char_zero K] [is_cyclotomic_field p ℚ K]

def zeta' : K :=
classical.some (exists_root_of_splits (algebra_map ℚ K) (is_splitting_field.splits _ _)
  (degree_cyclotomic_pos p ℚ hn.out).ne.symm)

@[simp]
lemma zeta'_spec :
  eval₂ (algebra_map ℚ K) (zeta' p _) (cyclotomic p ℚ) = 0 :=
classical.some_spec (exists_root_of_splits _
  (polynomial.is_splitting_field.splits K (@cyclotomic p ℚ _))
  (degree_cyclotomic_pos p ℚ hn.out).ne.symm)

include hn

lemma zeta'_spec' :
  is_root (map (algebra_map ℚ K) (cyclotomic p ℚ)) (zeta' p _) :=
begin
  simp only [is_root.def, map_cyclotomic],
  convert zeta'_spec p K,
  rw eval₂_eq_eval_map _,
  simp [-zeta'_spec],
end

@[simp]
lemma zeta'_pow_prime : (zeta' p K) ^ p = 1 :=
begin
  suffices : is_root (X ^ p - 1) (zeta' p K),
  { simpa [sub_eq_zero], },
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn.out, is_root.def, eval_prod, finset.prod_eq_zero_iff],
  use p,
  simp only [(fact.out (0 < p)).ne.symm, true_and, nat.mem_divisors, ne.def, not_false_iff,
    dvd_refl],
  have := zeta'_spec p K,
  rw eval₂_eq_eval_map at this,
  convert this,
  rw map_cyclotomic,
end


lemma is_root_cyclotomic_iff {K : Type*} [field K] {μ : K}
  (h : ∃ ζ : K, is_primitive_root ζ p) : is_primitive_root μ p ↔ is_root (cyclotomic p K) μ :=
begin
  obtain ⟨ζ, hζ⟩ := h,
  rw [← mem_roots (cyclotomic_ne_zero p K), cyclotomic_eq_prod_X_sub_primitive_roots hζ,
    roots_prod_X_sub_C, ← finset.mem_def, ← mem_primitive_roots hn.out],
end
-- TODO make a constructor assuming prime, but don't need it here

lemma zeta'_primitive_root : is_primitive_root (zeta' p K) p :=
{ pow_eq_one := zeta'_pow_prime p K,
  dvd_of_pow_eq_one := sorry }


-- TODO use the fact that a primitive root is a unit.
-- TODO prove in general that is_primitive root is integral,
-- this exists as is_primitive_root.is_integral so use

lemma zeta'_integral : zeta' p (cyclotomic_field p) ∈ ring_of_integers (cyclotomic_field p) :=
begin
  show is_integral ℤ (zeta' p _),
  use [cyclotomic p ℤ, cyclotomic.monic p ℤ],
  rw [← zeta'_spec _ _],
  simp [eval₂_eq_eval_map],
end


def zeta : units (ring_of_integers (cyclotomic_field p)) :=
units.mk_of_mul_eq_one
  (⟨zeta' p _, zeta'_integral p⟩)
  (⟨zeta' p _, zeta'_integral p⟩ ^ (p - 1))
  begin
    ext,
    simp [← pow_succ, nat.sub_add_cancel hn.out],
  end

lemma zeta_primitive_root : is_primitive_root (zeta p : ring_of_integers (cyclotomic_field p)) p :=
{ pow_eq_one := sorry,
  dvd_of_pow_eq_one := sorry }
-- is_primitive_root.of
end

end cyclotomic_field

open cyclotomic_field
section pos

variables {n : ℕ} [fact (0 < n)]
open_locale big_operators
open finset

lemma zeta_pow_eq_one : (zeta n) ^ n = 1 :=
begin
  ext,
  rw zeta,
  simp,
end

def aux (r n : ℕ) : ℕ := ((r.gcd_a n) % n).nat_abs
lemma aux_spec {r n : ℕ} (h : r.coprime n) : r * aux r n ≡ 1 [MOD n] :=
begin
  sorry,
end

def cyclotomic_unit {r s : ℕ} (hr : r.coprime n) (hs : s.gcd n = 1) :
  units (ring_of_integers (cyclotomic_field n)) :=
units.mk_of_mul_eq_one
  (geom_sum (zeta n ^ s) (r * aux r n))
  -- (∑ t in range r, zeta hn ^ (s * t))
  --(( zeta n ^r - 1) * ((zeta n)^s - 1)⁻¹)
  (geom_sum (zeta n ^ r) (s * aux r n))
  -- (∑ t in range s,  zeta hn ^ (t * r))
  begin
    sorry;
    { simp,
    rw sum_mul,
    simp [mul_sum],
    norm_cast,
    simp only [← pow_add],
    simp,
    sorry, },
  end

open_locale non_zero_divisors
local notation `RR` := ring_of_integers (cyclotomic_field n)
local notation `K` := cyclotomic_field n
lemma cyclotomic_unit_mul_denom {r s : ℕ} (hr : r.coprime n) (hs : s.coprime n) :
  (cyclotomic_unit hr hs : RR) * (zeta n ^ s - 1) = zeta n ^ r - 1 :=
sorry

open units fractional_ideal

-- TODO redefine span_singleton as a monoid hom so we get this for free?
@[simp]
lemma span_singleton_pow {R : Type*} {P : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (x : P) : ∀ (n : ℕ),
  span_singleton S (x ^ n) = span_singleton S x ^ n
| 0 := by simp
| (n + 1) := by simp [pow_succ, ← span_singleton_pow n]


open submodule
-- pretty sure there is an easier proof of this
lemma submodule.span_singleton_eq_span_singleton {R : Type*} {M : Type*} [ring R] [add_comm_group M]
  [module R M] [no_zero_smul_divisors R M] (x y : M) :
  span R ({x} : set M) = span R ({y} : set M) ↔ ∃ u : units R, u • x = y :=
begin
  by_cases hy : y = 0,
  { subst hy,
    simp,
    split; intro h,
    { subst h,
      use 1,
      simp, },
    { cases h,
      simpa [smul_eq_zero_iff_eq] using h_h, -- TODO this lemma should be simp
      }, },
  by_cases hx : x = 0,
  { subst hx,
    simp [eq_comm], },  -- TODO LOL why is this case so much easier
  rw [le_antisymm_iff, and_comm, submodule.le_span_singleton_iff, submodule.le_span_singleton_iff],
  split; intro h,
  { rcases h with ⟨h_left, h_right⟩,
    obtain ⟨u, hu⟩ := h_left y (mem_span_singleton_self y),
    obtain ⟨v, hv⟩ := h_right x (mem_span_singleton_self x),
    use [u, v],
    { rw [← hv, ← mul_smul, ← sub_eq_zero] at hu,
      rw ← one_smul R y at hu {occs := occurrences.pos [2]},
      rw [← sub_smul, smul_eq_zero, sub_eq_zero] at hu,
      tauto, },
    { rw [← hu, ← mul_smul, ← sub_eq_zero] at hv,
      rw ← one_smul R x at hv {occs := occurrences.pos [2]},
      rw [← sub_smul, smul_eq_zero, sub_eq_zero] at hv,
      tauto, },
    exact hu, },
  { rcases h with ⟨h, rfl⟩,
    simp [submodule.mem_span_singleton],
    split; intro a,
    { use [a * h],
      simp [mul_smul];
      refl, },
    { use [a * (h⁻¹ : units R)],
      rw mul_smul,
      congr,
      rw [smul_def h x, ← mul_smul],
      simp only [one_smul, inv_mul], }, },
end

lemma exists_unit_mul_primitive_root_one_sub_zeta  (z : RR)
  (hz : is_primitive_root z n) :
  ∃ u : units RR, ↑u * (1 - z : RR) = 1 - zeta n :=
begin
  -- have := zeta_primitive_root n,
  rw is_primitive_root.is_primitive_root_iff (zeta_primitive_root n) (fact.out _ : 0 < n) at hz,
  obtain ⟨i, hip, hin, hi⟩ := hz,
  rw ← hi,
  refine ⟨(cyclotomic_unit (nat.gcd_one_left _) hin), _⟩,
  rw ← neg_sub,
  rw mul_neg_eq_neg_mul_symm,
  simp [cyclotomic_unit_mul_denom (nat.gcd_one_left _) hin],
end


open polynomial




open nat

end pos
open units fractional_ideal submodule polynomial
variables (n : ℕ)
local notation `RR` := ring_of_integers (cyclotomic_field n)
local notation `K` := cyclotomic_field n
open_locale non_zero_divisors

lemma prime_ideal_eq_pow_cyclotomic [hn : fact (n.prime)] :
  (span_singleton _ (n : K) : fractional_ideal RR⁰ K) =
  (span_singleton _ (1 - zeta n)^(n - 1) : fractional_ideal RR⁰ K) :=
  --(mk0 (p : cyclotomic_field p) (by norm_num [hn.ne_zero]))
begin
  rw ← span_singleton_pow,
  apply coe_to_submodule_injective,
  simp only [coe_span_singleton, coe_coe],
  -- rw ideal.span_singleton_eq_span_singleton,
  simp only [submodule.span_singleton_eq_span_singleton],
  rw ← eval_one_cyclotomic_prime,
  --rw calc
  --  eval 1 (cyclotomic n (cyclotomic_field n)) = _ : by simp_rw
  --    cyclotomic_eq_prod_X_sub_primitive_roots (zeta'_primitive_root n _)
  --                      ... = _ : by simp only [polynomial.eval_sub, polynomial.eval_C,
  --                                  polynomial.eval_prod, polynomial.eval_X],

  -- apply span_singleton_eq_span_singleton_,
  sorry,
end
