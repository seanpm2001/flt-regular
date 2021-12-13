import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume
import data.zmod.extras
import tactic
import data.nat.prime_extras
import ready_for_mathlib.totient
import algebra.gcd_monoid.nat
import number_theory.cyclotomic.factoring

-- TODO I (alex) commented this out as it seems redundent now? -- agree, seems redundant - Eric
-- lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab : a.coprime b)
--     : b.coprime c ∧ a.coprime c := sorry
theorem eq_pow_of_prod_eq_pow {α : Type*} [comm_cancel_monoid_with_zero α]
  [unique_factorization_monoid α] [nontrivial α] {c : associates α} (A : finset (associates α))
  (hA : ∀ (a : associates α) (ha : a ∈ A), a ≠ 0)
  (hab : set.pairwise (↑A : set (associates α)) (λ a b, ∀ d, d ∣ a → d ∣ b → ¬ prime d)) {k : ℕ} (h : A.prod id = c ^ k) :
  ∀ (a : associates α) (ha : a ∈ A), ∃ (d : associates α), a = d ^ k :=
begin
  classical,
  induction A using finset.induction_on with a A ha hi generalizing h,
  { simp, },
  { simp only [ha, forall_eq_or_imp, finset.prod_insert,
      id.def, not_false_iff, finset.mem_insert] at h ⊢,
    split,
    { refine associates.eq_pow_of_mul_eq_pow (hA a (A.mem_insert_self a)) _ _ h,
      { rw finset.prod_ne_zero_iff,
        intros b hb,
        exact hA b (finset.mem_insert_of_mem hb), },
      sorry, },
    { apply hi,
      intros b hb,
      exact hA b (finset.mem_insert_of_mem hb),
      simp at hab,
      rw set.pairwise_insert at hab,
      exact hab.1,
      rw mul_comm at h, },
     },
end

lemma flt_three_case_one_aux {A B C : zmod 9} (h : A ^ 3 + B ^ 3 = C ^ 3) : 3 ∣ A * B * C :=
by dec_trivial!

open polynomial fractional_ideal
open_locale non_zero_divisors
theorem flt_regular_case_one_main {p a b c : ℕ} [h_prime : fact p.prime] (hp : is_regular_number p)
  (hp_ne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hab : a.coprime b)
  (hpabc : p.coprime (a * b * c)) (hp_five : 5 ≤ p) : false :=
begin
  have h_prime : p.prime := fact.out _,
  let pp : ℕ+ := ⟨p, nat.prime.pos h_prime⟩,
  have h_fac := pow_add_pow_eq_prod_add_zeta_mul (nat.odd_iff.mp (nat.prime.odd h_prime hp_ne_two))
    (is_cyclotomic_extension.zeta'_primitive_root pp ℚ (cyclotomic_field pp ℚ)) a b,
  have h_faci : ↑a ^ p + ↑b ^ p =
    (nth_roots_finset p (cyclotomic_ring pp ℤ ℚ)).prod (λ (ζ : cyclotomic_ring pp ℤ ℚ), ↑a + ζ * ↑b)
    := sorry,
  -- TODO need to generalize a few mathlib results for this it seems
  rw_mod_cast h at h_fac,
  rw_mod_cast h at h_faci,
  symmetry' at h_fac,
  symmetry' at h_faci,
  push_cast at h_fac,
  push_cast at h_faci,
  have h_frac := congr_arg (span_singleton (cyclotomic_ring pp ℤ ℚ)⁰) h_fac,
  -- ideal is a UFM but fractional ideal not, is there a sensible notion of UFG?
  have h_ideal := congr_arg (λ t, (ideal.span {t} : ideal (cyclotomic_ring pp ℤ ℚ))) h_faci,
  simp only [span_singleton_prod, span_singleton_pow,
    ←ideal.span_singleton_pow, ideal.span_singleton_prod] at h_frac h_ideal,
  sorry,
end

/-- Case I (when a,b,c are coprime to the exponent), of FLT for regular primes, by reduction to
  the case of 5 ≤ p. -/
theorem flt_regular_case_one {p a b c : ℕ} [h_prime : fact p.prime] (hp : is_regular_number p)
  (hp_ne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hab : a.coprime b)
  (hpabc : p.coprime (a * b * c)) : false :=
begin
  unfreezingI { rcases eq_or_ne p 3 with rfl | hp_three },
  { suffices : 3 ∣ a * b * c,
    { exact (nat.prime_three.dvd_iff_not_coprime.mp this) hpabc, },
    have : (a : zmod 9) ^ 3 + b ^ 3 = c ^ 3,
    { rw_mod_cast h },
    convert dvd_of_dvd_zmod (by norm_num : 3 ∣ 9) (by exact_mod_cast flt_three_case_one_aux this) },
  { have hp_five : 5 ≤ p, from h_prime.elim.five_le hp_ne_two hp_three,
    exact flt_regular_case_one_main hp hp_ne_two h hab hpabc hp_five, }
end

/-- Case II (when a,b,c are not coprime to the exponent), of FLT for regular primes. -/
theorem flt_regular_case_two (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p ∣ a * b * c) : a * b * c = 0 := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p) (hpne_two : p ≠ 2)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 :=
begin
  may_assume hcoprime : ({a, b, c} : finset ℕ).gcd id = 1,
  { let s : finset ℕ := {a, b, c},
    let d : ℕ := s.gcd id,
    rcases eq_or_ne c 0 with rfl | hc, --budget may_assume ;b needed for `image_div_gcd_coprime`
    { rw mul_zero },
    cases d.eq_zero_or_pos with hd hd,
    { rw finset.gcd_eq_zero_iff at hd,
      rw mul_eq_zero,
      exact or.inr (hd c $ by simp) },
    specialize h_red p (a/d) (b/d) (c/d) ‹_› hp hpne_two _ _,
    { have habc := congr_arg (/ d^p) h,
      simp only at habc,
      rw nat.add_div (pow_pos hd p) at habc,
      have : ite (d ^ p ≤ a ^ p % d ^ p + b ^ p % d ^ p) 1 0 = 0,
      { simp only [nat.one_ne_zero, ite_eq_right_iff, imp_false, not_le],
        convert pow_pos hd p,
        rw add_eq_zero_iff,
        split;
        { apply nat.mod_eq_zero_of_dvd,
          apply pow_dvd_pow_of_dvd,
          apply finset.gcd_dvd,
          simp } },
      have key : ∀ x ∈ ({a, b, c} : finset ℕ), x ^ p / d ^ p = (x / d) ^ p,
      { intros x xh,
        rw div_pow''', -- TODO move this lemma to a reasonable place / name and mathlib
        exact (finset.gcd_dvd xh), },
      simpa only [this, key, true_or, eq_self_iff_true, or_true, finset.mem_insert,
                  finset.mem_singleton] using habc },
    { convert s.coprime_of_div_gcd _ hc using 1,
      conv_rhs { rw finset.gcd_eq_gcd_image },
      congr,
      simp only [finset.image_insert, id.def, finset.image_singleton, normalize_eq],
      simp },
    { have habc := congr_arg (* d^3) h_red,
      simp only [zero_mul] at habc,
      replace habc : (a / d * d) * (b / d * d) * (c / d * d) = 0,
      { convert habc using 1, ring },
      iterate 3 { rw nat.div_mul_cancel at habc },
      exact habc,
      all_goals { apply finset.gcd_dvd, simp } } },
  cases nat.coprime_or_dvd_of_prime (fact.out p.prime) (a * b * c) with hpabc hpabc,
  { exact absurd hpabc (flt_regular_case_one hp hpne_two h sorry) },
  { exact flt_regular_case_two p a b c hp hpne_two h hpabc }
end
