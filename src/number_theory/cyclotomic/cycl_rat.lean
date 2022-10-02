import ring_theory.polynomial.eisenstein
import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.rat

import ready_for_mathlib.basis
import ready_for_mathlib.roots_of_unity
import ready_for_mathlib.is_cyclotomic_extension

universes u

open finite_dimensional polynomial algebra nat finset fintype

variables (p : ℕ+) (L : Type u) [field L] [char_zero L] [is_cyclotomic_extension {p} ℚ L]

section int_facts

noncomputable theory

open_locale number_field big_operators

--A.K.A theorem:FLT_facts 3
-- Eric: is this superseded by `exists_int_sub_pow_prime_dvd`?
lemma flt_fact_3 [fact (p : ℕ).prime] (a : 𝓞 L) :
  ∃ (m : ℤ), (a ^ (p : ℕ) - m) ∈ ideal.span ({p} : set (𝓞 L)) := by admit

open ideal is_cyclotomic_extension

-- TODO refactor add_pow_char_of_commute to use this instead of its own (basically the same) proof
-- TODO is the fact assumption necessary what if p is a prime power?
-- TODO other versions, e.g. one for sub and one for p^n with the
theorem add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute {R : Type*} [semiring R] (p : ℕ)
  [fact p.prime] (x y : R) (h : commute x y) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
begin
  have : p = p - 1 + 1 := (nat.succ_pred_prime (fact.out _)).symm,
  rw [commute.add_pow h, finset.sum_range_succ_comm, tsub_self, pow_zero, nat.choose_self,
    nat.cast_one, mul_one, mul_one, this, finset.sum_range_succ'],
  simp only [this.symm, tsub_zero, mul_one, one_mul, nat.choose_zero_right, nat.cast_one, pow_zero],
  rw add_comm _ (y ^ p),
  simp_rw add_assoc,
  use (finset.range (p - 1)).sum
    (λ (x_1 : ℕ), x ^ (x_1 + 1) * y ^ (p - (x_1 + 1)) * ↑(p.choose (x_1 + 1) / p)),
  rw finset.mul_sum,
  congr' 2,
  apply finset.sum_congr rfl,
  intros i hi,
  rw [finset.mem_range] at hi,
  rw [nat.cast_comm, mul_assoc, mul_assoc, mul_assoc],
  congr,
  norm_cast,
  rw nat.div_mul_cancel,
  exact nat.prime.dvd_choose_self (nat.succ_pos _) (lt_tsub_iff_right.mp hi) (fact.out _),
end

theorem add_pow_prime_eq_pow_add_pow_add_prime_mul {R : Type*} [comm_semiring R] (p : ℕ)
  [fact p.prime] (x y : R) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute _ _ _ (commute.all _ _)

-- TODO can we make a relative version of this with another base ring instead of ℤ ?
-- A version of flt_facts_3 indep of the ring
lemma exists_int_sub_pow_prime_dvd {A : Type*} [comm_ring A] [is_cyclotomic_extension {p} ℤ A]
  [fact (p : ℕ).prime] (a : A) : ∃ (m : ℤ), (a ^ (p : ℕ) - m) ∈ span ({p} : set A) :=
begin
  have : a ∈ algebra.adjoin ℤ _ := @adjoin_roots {p} ℤ A _ _ _ _ a,
  apply algebra.adjoin_induction this,
  { intros x hx,
    rcases hx with ⟨hx_w, hx_m, hx_p⟩,
    simp only [set.mem_singleton_iff] at hx_m,
    rw [hx_m] at hx_p,
    simp only [hx_p, coe_coe],
    use 1,
    simp, },
  { intros r,
    use r ^ (p : ℕ),
    simp, },
  { rintros x y ⟨b, hb⟩ ⟨c, hc⟩,
    obtain ⟨r, hr⟩ := add_pow_prime_eq_pow_add_pow_add_prime_mul p x y,
    rw [hr],
    use c + b,
    push_cast,
    rw [sub_add_eq_sub_sub, sub_eq_add_neg, sub_eq_add_neg, add_comm _ (↑↑p * r),
        add_assoc, add_assoc],
    apply' ideal.add_mem _ _,
    { convert ideal.add_mem _ hb hc using 1,
      ring },
    { rw [mem_span_singleton, coe_coe],
      exact dvd_mul_right _ _ } },
  { rintros x y ⟨b, hb⟩ ⟨c, hc⟩,
    rw mul_pow,
    use b * c,
    have := ideal.mul_mem_left _ (x ^ (p : ℕ)) hc,
    rw [mul_sub] at this,
    rw [←ideal.quotient.eq_zero_iff_mem, map_sub] at this ⊢ hb,
    convert this using 2,
    rw [int.cast_mul, _root_.map_mul, _root_.map_mul],
    congr' 1,
    exact (sub_eq_zero.mp hb).symm }
end

instance aaaa [fact ((p : ℕ).prime)] : is_cyclotomic_extension {p} ℤ (𝓞 L) :=
let _ := (zeta_spec p ℚ L).adjoin_is_cyclotomic_extension ℤ in
  by exactI is_cyclotomic_extension.equiv {p} (zeta_spec p ℚ L).adjoin_equiv_ring_of_integers'

local notation `RR` := 𝓞 (cyclotomic_field p ℚ)

local attribute [instance] algebra_rat_subsingleton

--This is still annoying
instance [hp : fact ((p : ℕ).prime)] : is_cyclotomic_extension {p} ℤ ↥(𝓞 (cyclotomic_field p ℚ)) :=
@aaaa p (cyclotomic_field p ℚ) _ _
  (by { convert cyclotomic_field.is_cyclotomic_extension p ℚ, exact subsingleton.elim _ _ }) _

-- TODO I (alex) am not sure whether this is better as ideal span,
-- or fractional_ideal.span_singleton
/-- The principal ideal generated by `x + y ζ^i` for integer `x` and `y` -/
def flt_ideals [fact ((p : ℕ).prime)] (x y i : ℤ) : ideal RR :=
  ideal.span ({ x + y * ((zeta_runity p ℤ RR) ^ i : RRˣ) } : set RR)

variable {p} -- why does this not update (n : ℕ+)?

lemma mem_flt_ideals [fact ((p : ℕ).prime)] {x y i : ℤ} :
  (x : RR) + y * ((zeta_runity p ℤ RR) ^ i : RRˣ) ∈ flt_ideals p x y i :=
mem_span_singleton.mpr dvd_rfl

section to_move

variables {R : Type*} [semiring R] {s t : ideal R}

lemma ideal.add_left_subset  : s ≤ s + t := le_sup_left
lemma ideal.add_right_subset : t ≤ s + t := le_sup_right

variables {K : Type*} [semiring K]

lemma add_eq_mul_one_add_div {a : Kˣ} {b : K} : ↑a + b = a * (1 + ↑a⁻¹ * b) :=
by rwa [mul_add, mul_one, ← mul_assoc, units.mul_inv, one_mul]

end to_move

lemma flt_ideals_coprime [fact (p : ℕ).prime] (ph : 5 ≤ p) {x y : ℤ} {i j : ℤ} (h : i ≠ j)
  (hp : is_coprime x y) : flt_ideals p x y i + flt_ideals p x y j = ⊤ :=
begin
  let I := flt_ideals p x y i + flt_ideals p x y j,
  have : ∃ v : RRˣ, (v : RR) * y * (1 - (zeta_runity p ℤ RR)) ∈ I,
  { have := I.add_mem (ideal.add_left_subset $ mem_flt_ideals)
                      (ideal.mul_mem_left _ (-1) $ ideal.add_right_subset $ mem_flt_ideals),
    simp only [neg_mul, one_mul, neg_add_rev] at this,
    rw [neg_mul_eq_mul_neg, add_comm] at this,
    simp only [← add_assoc] at this,
    rw [add_assoc _ (-_) _, neg_add_self, add_zero, ←mul_add, add_comm, add_eq_mul_one_add_div,
        ←zpow_neg] at this,
    sorry
    -- I cannot get the tactic state to work here :/
  }, sorry,
end

variable {L}

lemma dvd_last_coeff_cycl_integer [hp : fact (p : ℕ).prime] {ζ : L} (hζ : is_primitive_root ζ p)
  {f : fin p → ℤ} {i : fin p} (hf : f i = 0) {m : ℤ}
  (hdiv : ↑m ∣ ∑ j, f j • (⟨ζ, hζ.is_integral p.pos⟩ : 𝓞 L) ^ (j : ℕ)) :
  m ∣ f ⟨(p : ℕ).pred, pred_lt hp.out.ne_zero⟩ :=
begin
  have hlast : (fin.cast (succ_pred_prime hp.out)) (fin.last (p : ℕ).pred) =
    ⟨(p : ℕ).pred, pred_lt hp.out.ne_zero⟩ := fin.ext rfl,
  have h : ∀ x, (fin.cast (succ_pred_prime hp.out)) (fin.cast_succ x) =
    ⟨x, lt_trans x.2 (pred_lt hp.out.ne_zero)⟩ := λ x, fin.ext rfl,
  have hζ' : is_primitive_root (⟨ζ, hζ.is_integral p.pos⟩ : 𝓞 L) p :=
    is_primitive_root.coe_submonoid_class_iff.1 hζ,
  set b := hζ.integral_power_basis' with hb,
  have hdim : b.dim = (p : ℕ).pred,
  { rw [hζ.power_basis_int'_dim, totient_prime hp.out, pred_eq_sub_one] },

  by_cases H : i = ⟨(p : ℕ).pred, pred_lt hp.out.ne_zero⟩,
  { simp [H.symm, hf] },
  have hi : ↑i < (p : ℕ).pred,
  { by_contra' habs,
    simpa [le_antisymm habs (le_pred_of_lt (fin.is_lt i))] using H },
  obtain ⟨y, hy⟩ := hdiv,
  rw [← equiv.sum_comp (fin.cast (succ_pred_prime hp.out)).to_equiv, fin.sum_univ_cast_succ] at hy,
  simp only [hlast, h, rel_iso.coe_fn_to_equiv, fin.coe_mk] at hy,
  rw [hζ'.pow_sub_one_eq hp.out.one_lt, ← sum_neg_distrib, smul_sum, sum_range, ← sum_add_distrib,
    ← (fin.cast hdim).to_equiv.sum_comp] at hy,
  simp only [rel_iso.coe_fn_to_equiv, fin.coe_cast, mul_neg] at hy,
  conv_lhs at hy { congr, skip, funext,
    rw [add_comm, smul_neg, ← sub_eq_neg_add, ← sub_smul, ← hζ.integral_power_basis'_gen,
      ← hb, ← show ∀ x, _ = _, from λ x, congr_fun b.coe_basis x] },
  replace hy := congr_arg (b.basis.coord ((fin.cast hdim.symm) ⟨i, hi⟩)) hy,
  rw [← b.basis.equiv_fun_symm_apply, b.basis.coord_equiv_fun_symm] at hy,
  simp only [hf, fin.coe_cast, smul_eq_mul, mul_boole, sum_ite_eq', mem_univ, fin.coe_mk,
    fin.eta, zero_sub, if_true] at hy,
  rw [← smul_eq_mul, ← zsmul_eq_smul_cast, neg_eq_iff_neg_eq] at hy,
  obtain ⟨n, hn⟩ := b.basis.coord_dvd_of_dvd ((fin.cast hdim.symm) ⟨i, hi⟩) y m,
  rw [hn] at hy,
  simp [← hy, dvd_neg]
end

lemma dvd_coeff_cycl_integer [hp : fact (p : ℕ).prime] {ζ : L} (hζ : is_primitive_root ζ p)
  {f : fin p → ℤ} {i : fin p} (hf : f i = 0) {m : ℤ}
  (hdiv : ↑m ∣ ∑ j, f j • (⟨ζ, hζ.is_integral p.pos⟩ : 𝓞 L) ^ (j : ℕ)) : ∀ j, m ∣ f j :=
begin
  have hlast : (fin.cast (succ_pred_prime hp.out)) (fin.last (p : ℕ).pred) =
    ⟨(p : ℕ).pred, pred_lt hp.out.ne_zero⟩ := fin.ext rfl,
  have h : ∀ x, (fin.cast (succ_pred_prime hp.out)) (fin.cast_succ x) =
    ⟨x, lt_trans x.2 (pred_lt hp.out.ne_zero)⟩ := λ x, fin.ext rfl,
  have hζ' : is_primitive_root (⟨ζ, hζ.is_integral p.pos⟩ : 𝓞 L) p :=
    is_primitive_root.coe_submonoid_class_iff.1 hζ,
  set b := hζ.integral_power_basis' with hb,
  have hdim : b.dim = (p : ℕ).pred,
  { rw [hζ.power_basis_int'_dim, totient_prime hp.out, pred_eq_sub_one] },
  have last_dvd := dvd_last_coeff_cycl_integer hζ hf hdiv,

  intro j,
  by_cases H : j = ⟨(p : ℕ).pred, pred_lt hp.out.ne_zero⟩,
  { simpa [H] using last_dvd },
  have hj : ↑j < (p : ℕ).pred,
  { by_contra' habs,
    simpa [le_antisymm habs (le_pred_of_lt (fin.is_lt j))] using H },
  obtain ⟨y, hy⟩ := hdiv,
  rw [← equiv.sum_comp (fin.cast (succ_pred_prime hp.out)).to_equiv, fin.sum_univ_cast_succ] at hy,
  simp only [hlast, h, rel_iso.coe_fn_to_equiv, fin.coe_mk] at hy,
  rw [hζ'.pow_sub_one_eq hp.out.one_lt, ← sum_neg_distrib, smul_sum, sum_range, ← sum_add_distrib,
    ← (fin.cast hdim).to_equiv.sum_comp] at hy,
  simp only [rel_iso.coe_fn_to_equiv, fin.coe_cast, mul_neg] at hy,
  conv_lhs at hy { congr, skip, funext,
    rw [add_comm, smul_neg, ← sub_eq_neg_add, ← sub_smul, ← hζ.integral_power_basis'_gen,
      ← hb, ← show ∀ x, _ = _, from λ x, congr_fun b.coe_basis x] },
  replace hy := congr_arg (b.basis.coord ((fin.cast hdim.symm) ⟨j, hj⟩)) hy,
  rw [← b.basis.equiv_fun_symm_apply, b.basis.coord_equiv_fun_symm] at hy,
  simp only [fin.cast_mk, fin.coe_mk, fin.eta, basis.coord_apply, sub_eq_iff_eq_add] at hy,
  obtain ⟨n, hn⟩ := b.basis.coord_dvd_of_dvd ((fin.cast hdim.symm) ⟨j, hj⟩) y m,
  rw [hy, ← smul_eq_mul, ← zsmul_eq_smul_cast, ← b.basis.coord_apply, ← fin.cast_mk, hn],
  exact dvd_add (dvd_mul_right _ _) last_dvd
end

end int_facts
