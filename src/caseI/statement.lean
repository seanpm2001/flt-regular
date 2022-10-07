import may_assume.lemmas
import number_theory.cyclotomic.factoring
import number_theory.cyclotomic.Unit_lemmas
import ready_for_mathlib.exists_eq_pow_of_mul_eq_pow
import ready_for_mathlib.roots_of_unity
import number_theory.cyclotomic.case_I

open finset nat is_cyclotomic_extension ideal polynomial int

open_locale big_operators number_field

namespace flt_regular

variables {p : ℕ} (hpri : p.prime)

local notation `P` := (⟨p, hpri.pos⟩ : ℕ+)
local notation `K` := cyclotomic_field P ℚ
local notation `R` := 𝓞 K

namespace caseI

/-- Statement of case I with additional assumptions. -/
def slightly_easier : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- Statement of case I. -/
def statement : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseI : ¬ ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

lemma may_assume : slightly_easier → statement :=
begin
  intro Heasy,
  intros a b c p hpri hreg hodd hprod hI H,
  have hp5 : 5 ≤ p,
  { by_contra' habs,
    have : p ∈ finset.Ioo 2 5 := finset.mem_Icc.2 ⟨nat.lt_of_le_and_ne hpri.two_le hodd.symm,
      by linarith⟩,
    fin_cases this,
    { exact may_assume.p_ne_three hprod H rfl },
    { rw [show 4 = 2 * 2, from rfl] at hpri,
      refine nat.not_prime_mul one_lt_two one_lt_two hpri } },
  rcases may_assume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩,
  let d := ({a, b, c} : finset ℤ).gcd id,
  have hdiv : ¬↑p ∣ (a / d) * (b / d) * (c / d),
  { have hadiv : d ∣ a := gcd_dvd (by simp),
    have hbdiv : d ∣ b := gcd_dvd (by simp),
    have hcdiv : d ∣ c := gcd_dvd (by simp),
    intro hdiv,
    replace hdiv := dvd_mul_of_dvd_right hdiv ((d * d) * d),
    rw [mul_assoc, ← mul_assoc d, ← mul_assoc d, int.mul_div_cancel' hadiv, mul_assoc,
      mul_comm a, mul_assoc (b / d), ← mul_assoc _ (b / d), int.mul_div_cancel' hbdiv,
      mul_comm, mul_assoc, mul_assoc, int.div_mul_cancel hcdiv, mul_comm, mul_assoc,
      mul_comm c, ← mul_assoc] at hdiv,
    exact hI hdiv },
  obtain ⟨X, Y, Z, H1, H2, H3, H4, H5⟩ := a_not_cong_b hpri hp5 hprodxyx Hxyz hunit hdiv,
  exact Heasy hpri hreg hp5 H4 H2 H3 (λ hfin, H5 hfin) H1
end

end caseI

lemma ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id)) : is_coprime a b  :=
begin
  rw [← gcd_eq_one_iff_coprime],
  by_contra' h,
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h,
  replace hqpri : prime (q : ℤ) := prime_iff_nat_abs_prime.2 (by simp [hqpri]),
  obtain ⟨n, hn⟩ := hq,
  have haq : ↑q ∣ a,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_left a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hbq : ↑q ∣ b,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_right a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hcq : ↑q ∣ c,
  { suffices : ↑q ∣ c ^ p,
    { exact hqpri.dvd_of_dvd_pow this },
    rw [← H],
    exact dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero) },
  have Hq : ↑q ∣ ({a, b, c} : finset ℤ).gcd id,
  { refine dvd_gcd (λ x hx, _),
    simp only [mem_insert, mem_singleton] at hx,
    rcases hx with H | H | H;
    simpa [H] },
  exact not_is_unit_of_not_is_unit_dvd hqpri.not_unit Hq hgcd
end

theorem exists_ideal {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id)) (caseI : ¬ ↑p ∣ a * b * c)
  {ζ : R} (hζ : ζ ∈ nth_roots_finset p R) : ∃ I, span ({a + ζ * b} : set R) = I ^ p :=
begin
  have h5P : 5 ≤ P := h5p,
  haveI : fact ((P : ℕ).prime) := ⟨hpri⟩,
  classical,
  have H₁ := congr_arg (algebra_map ℤ R) H,
  simp only [eq_int_cast, int.cast_add, int.cast_pow] at H₁,
  have hζ' := is_primitive_root.unit'_coe (zeta_spec P ℚ K),
  rw [pow_add_pow_eq_prod_add_zeta_runity_mul (or.resolve_left (prime.eq_two_or_odd hpri)
    (λ _, by linarith)) hζ'] at H₁,
  replace H₁ := congr_arg (λ x, span ({x} : set R)) H₁,
  simp only [span_singleton_prod, ← span_singleton_pow] at H₁,
  obtain ⟨I, hI⟩ := exists_eq_pow_of_prod_eq_pow p (span ({c} : set R)) (λ η₁ hη₁ η₂ hη₂ hη, _) H₁ ζ hζ,
  { exact ⟨I, hI⟩ },
  { exact flt_ideals_coprime h5P H (ab_coprime H hpri.ne_zero hgcd) hη₁ hη₂ hη caseI }
end
.

theorem is_principal {a b c : ℤ} {ζ : R} (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (caseI : ¬ ↑p ∣ a * b * c) (H : a ^ p + b ^ p = c ^ p) (hζ : is_primitive_root ζ p) :
  ∃ (u : Rˣ) (α : R), ↑u * (α ^ p) = ↑a + ζ * ↑b :=
begin
  replace hζ := hζ.mem_nth_roots_finset hpri.pos,
  obtain ⟨I, hI⟩ := exists_ideal hpri hp5 H hgcd caseI hζ,
  by_cases hIpzero : I ^ p = 0,
  { refine ⟨1, 0, _⟩,
    simp [hIpzero, zero_eq_bot, span_singleton_eq_bot] at hI,
    simp [hpri.pos, hI] },
  have hIzero : I ≠ 0,
  { intro hIzero,
    simp only [hIzero, zero_pow hpri.pos] at hIpzero,
    exact hIpzero rfl },
  have hIprin : I.is_principal,
  { have : class_group.mk0 _ ⟨_, mem_non_zero_divisors_of_ne_zero hIpzero⟩ = (1 : class_group R K),
    { rw [class_group.mk0_eq_one_iff (mem_non_zero_divisors_of_ne_zero hIpzero)],
      exact ⟨⟨↑a + ζ * ↑b, hI.symm⟩⟩ },
    rw [← submonoid_class.mk_pow I (mem_non_zero_divisors_of_ne_zero hIzero), map_pow] at this,
    cases (dvd_prime hpri).1 (order_of_dvd_of_pow_eq_one this) with h1 habs,
    { exact (class_group.mk0_eq_one_iff _).1 (order_of_eq_one_iff.1 h1) },
    { exfalso,
      refine hpri.coprime_iff_not_dvd.1 hreg _,
      simp_rw [← habs],
      exact order_of_dvd_card_univ, } },
  obtain ⟨α, hα⟩ := hIprin,
  replace hα := congr_arg (λ J, J ^ p) hα,
  simp only [←hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα,
  obtain ⟨u, hu⟩ := hα,
  refine ⟨u⁻¹, α, _⟩,
  rw [← hu, mul_comm _ ↑u, ← mul_assoc],
  simp
end

--local attribute [-instance] cyclotomic_field.algebra

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} {p : ℕ} (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
begin
  intro H,
  haveI := (⟨hpri⟩ : fact ((P : ℕ).prime)),
  haveI diamond : is_cyclotomic_extension {P} ℚ K := cyclotomic_field.is_cyclotomic_extension P ℚ,
  let ζ := zeta P ℚ K, have hζ := (zeta_spec P ℚ K),
  let ζ' := (⟨ζ, hζ.is_integral hpri.pos⟩ : 𝓞 K),
  have hζ' : is_primitive_root ζ' p := is_primitive_root.coe_submonoid_class_iff.1 hζ,
  obtain ⟨u, α, hu⟩ := is_principal hpri hreg hp5 hgcd caseI H hζ',
  rw [show ζ' = (hζ.unit' : R), from rfl, mul_comm _ ↑b, ← pow_one hζ.unit'] at hu,
  obtain ⟨k, hk⟩ := @flt_regular.caseI.exists_int_sum_eq_zero P K _ _
    (by {convert diamond, by exact subsingleton.elim _ _ }) ζ hζ sorry _ a b 1 u α hu.symm,
  sorry
end

/-- CaseI. -/
theorem caseI {a b c : ℤ} {p : ℕ} (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
flt_regular.caseI.may_assume (λ x y z p₁ Hpri Hreg HP5 Hprod Hunit Hxy HI,
    caseI_easier Hpri Hreg HP5 Hprod Hunit Hxy HI) hpri hreg hodd hprod caseI

end flt_regular
