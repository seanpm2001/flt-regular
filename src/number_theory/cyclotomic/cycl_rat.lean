import ring_theory.polynomial.eisenstein
import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.rat
import number_theory.cyclotomic.Unit_lemmas
import ready_for_mathlib.basis
import ring_theory.dedekind_domain.ideal
import ready_for_mathlib.is_cyclotomic_extension
import number_theory.cyclotomic.zeta_sub_one_prime

universes u

open finite_dimensional polynomial algebra nat finset fintype

variables (p : ℕ+) (L : Type u) [field L] [char_zero L] [is_cyclotomic_extension {p} ℚ L]

section int_facts

noncomputable theory

open_locale number_field big_operators

section to_move

variables {R : Type*} [semiring R] {s t : ideal R}

lemma ideal.add_left_subset  : s ≤ s + t := le_sup_left
lemma ideal.add_right_subset : t ≤ s + t := le_sup_right

variables {K : Type*} [semiring K]

lemma add_eq_mul_one_add_div {a : Kˣ} {b : K} : ↑a + b = a * (1 + ↑a⁻¹ * b) :=
by rwa [mul_add, mul_one, ← mul_assoc, units.mul_inv, one_mul]

end to_move

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

local notation `R` := 𝓞 (cyclotomic_field p ℚ)

local attribute [instance] algebra_rat_subsingleton

--This is still annoying
instance [hp : fact ((p : ℕ).prime)] : is_cyclotomic_extension {p} ℤ ↥(𝓞 (cyclotomic_field p ℚ)) :=
@aaaa p (cyclotomic_field p ℚ) _ _
  (by { convert cyclotomic_field.is_cyclotomic_extension p ℚ, exact subsingleton.elim _ _ }) _

-- TODO I (alex) am not sure whether this is better as ideal span,
-- or fractional_ideal.span_singleton
/-- The principal ideal generated by `x + y ζ^i` for integer `x` and `y` -/
@[nolint unused_arguments]
def flt_ideals [fact ((p : ℕ).prime)] (x y : ℤ) {η : R}
  (hη : η ∈ nth_roots_finset p R) : ideal R :=
  ideal.span ({ x + η * y } : set R)

variable {p} -- why does this not update (n : ℕ+)?

lemma mem_flt_ideals [fact ((p : ℕ).prime)] (x y : ℤ) {η : R}
  (hη : η ∈ nth_roots_finset p R) :
  ↑x + η * ↑y ∈ flt_ideals p x y hη :=
mem_span_singleton.mpr dvd_rfl

lemma ideal.le_add (a b c d : ideal R) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
begin
  simp at *,
  split,
  apply le_trans hab (@le_sup_left _ _ _ _ ),
  apply le_trans hcd (@le_sup_right _ _ _ _ ),
end

lemma not_coprime_not_top (a b : ideal R) : ¬ is_coprime a b ↔ a + b ≠ ⊤ :=
begin
  apply not_iff_not_of_iff,
  rw is_coprime,
  split,
  intro h,
  obtain ⟨x, y , hxy ⟩ := h,
  rw eq_top_iff_one,
  have h2 : x * a + y * b ≤ a + b, by {apply ideal.le_add, all_goals {apply mul_le_left},  },
  apply h2,
  rw hxy,
  simp,
  intro h,
  refine ⟨1,1,_⟩,
  simp [h],
end

instance a1 : is_galois ℚ (cyclotomic_field p ℚ) := sorry

instance a2 :  finite_dimensional ℚ (cyclotomic_field p ℚ) := sorry

instance a3 : number_field (cyclotomic_field p ℚ) := sorry

open is_primitive_root

lemma nth_roots_prim [fact (p : ℕ).prime] {η : R} (hη : η ∈ nth_roots_finset p R)
  (hne1 : η ≠ 1) : is_primitive_root η p :=
begin
  have hζ' := (zeta_spec p ℚ ((cyclotomic_field p ℚ))).unit'_coe,
    rw (nth_roots_one_eq_bUnion_primitive_roots' hζ') at hη,
    simp at *,
    obtain ⟨a, ha, h2⟩ := hη,
    have ha2 : a = p, by {rw (dvd_prime _inst_4.out) at ha,
    cases ha,
    exfalso,
    rw ha at h2,
    simp at h2,
    rw h2 at hne1,
    simp at *,
    exact hne1,
    exact ha,},
    rw ha2 at h2,
    have hn :  0 <(p : ℕ), by {norm_num,},
    rw (mem_primitive_roots hn) at h2,
    exact h2,
end

lemma prim_coe (ζ : R) (hζ : is_primitive_root ζ p) :
  is_primitive_root (ζ : (cyclotomic_field p ℚ))  p :=
coe_submonoid_class_iff.mpr hζ

lemma zeta_sub_one_dvb_p [fact (p : ℕ).prime] (ph : 5 ≤ p) {η : R} (hη : η ∈ nth_roots_finset p R)
  (hne1 : η ≠ 1): (1 - η) ∣ (p : R) :=
begin
  have h00 : (1 - η) ∣ (p : R) ↔ (η - 1) ∣ (p : R), by {have hh : -(η - 1) = (1 - η), by {ring},
  simp_rw [←hh],
  apply neg_dvd},
  rw h00,
  have : is_primitive_root (η : (cyclotomic_field p ℚ))  p, by {
    apply prim_coe p η (nth_roots_prim hη hne1)},
  have h0 : p ≠ 2, by   { intro hP,
    norm_num [hP] at ph },
  have h := dvd_norm ℚ ((η - 1) : R),
  have h2 := is_primitive_root.sub_one_norm_prime this (cyclotomic.irreducible_rat p.2) h0,
  convert h,
  ext,
  rw algebra_map_norm',
  norm_cast at h2,
  rw h2,
  simp,
end



lemma one_sub_zeta_prime [fact (p : ℕ).prime] (ph : 5 ≤ p) {η : R} (hη : η ∈ nth_roots_finset p R)
  (hne1 : η ≠ 1) : prime (1 - η) :=
begin
  have h := (prim_coe p η (nth_roots_prim hη hne1)),

sorry,
end

lemma diff_of_roots  [fact (p : ℕ).prime] (ph : 5 ≤ p) {η₁ η₂ : R} (hη₁ : η₁ ∈ nth_roots_finset p R)
  (hη₂ : η₂ ∈ nth_roots_finset p R) (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
  ∃ (u : Rˣ), (η₁ - η₂) = u * (1 - η₁)  :=
begin
 sorry,
end


lemma diff_of_roots2  [fact (p : ℕ).prime] (ph : 5 ≤ p) {η₁ η₂ : R} (hη₁ : η₁ ∈ nth_roots_finset p R)
  (hη₂ : η₂ ∈ nth_roots_finset p R) (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
  ∃ (u : Rˣ), (η₂ - η₁) = u * (1 - η₁)  :=
begin
 sorry,
end

instance arg : is_dedekind_domain R := sorry

lemma flt_ideals_coprime2 [fact (p : ℕ).prime] (ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : R}
  (hη₁ : η₁ ∈ nth_roots_finset p R) (hη₂ : η₂ ∈ nth_roots_finset p R) (hdiff : η₁ ≠ η₂)
  (hp : is_coprime x y) (hp2 : ¬ (p : ℤ) ∣ (x + y : ℤ) ) (hwlog : η₁ ≠ 1) :
  is_coprime (flt_ideals p x y hη₁) (flt_ideals p x y hη₂) :=
begin
  let I := flt_ideals p x y hη₁ + flt_ideals p x y hη₂,
  by_contra,
  have he := (not_coprime_not_top p (flt_ideals p x y hη₁)  (flt_ideals p x y hη₂)).1 h,
  have := exists_le_maximal I he,
  obtain ⟨P, hP1, hP2⟩:= this,
  have hiP : (flt_ideals p x y hη₁) ≤ P, by {apply le_trans _ hP2, apply ideal.add_left_subset,},
  have hjP : (flt_ideals p x y hη₂) ≤ P, by {apply le_trans _ hP2, apply ideal.add_right_subset,},
  have hel1: ∃ v : Rˣ, (v : R) * y * (1 - η₁) ∈ I, by {
  have := I.add_mem (ideal.add_left_subset $ (mem_flt_ideals _ _ hη₁))
                      (ideal.mul_mem_left _ (-1) $ ideal.add_right_subset $ (mem_flt_ideals _ _ _) ),
    simp only [neg_mul, one_mul, neg_add_rev] at this,
    rw [neg_mul_eq_mul_neg, add_comm] at this,
    simp only [← add_assoc] at this,
    simp at this,
    have hh := diff_of_roots ph hη₁ hη₂ hdiff hwlog,
    obtain ⟨v, hv⟩ := hh,
    refine ⟨v, _⟩,
    have  h3 : -(η₂ * ↑y) + η₁ * ↑y = (η₁ - η₂) * y, by {ring},
    rw h3 at this,
    rw hv at this,
    have h4 :  ↑v * (1 - η₁) * ↑y = v * y * (1-η₁) , by {ring},
    rw ←h4,
    apply this},
  have hel2 : ∃ v : Rˣ, (v : R) * x * (1 - η₁) ∈ I, by {
    have := I.add_mem (ideal.mul_mem_left _ (η₂) $ ideal.add_left_subset $ (mem_flt_ideals _ _ hη₁))
                      (ideal.mul_mem_left _ (-η₁) $ ideal.add_right_subset $ (mem_flt_ideals _ _ _)),
    have h1 :  η₂ * (↑x + η₁ * ↑y) + -η₁ * (↑x + η₂ * ↑y) = (η₂ - η₁) * x, by {ring},
    rw h1 at this,
    have hh := diff_of_roots2 ph hη₁ hη₂ hdiff hwlog,
    obtain ⟨v, hv⟩ := hh,
    refine ⟨v, _⟩,
    rw hv at this,
    have h4 :  ↑v * (1 - η₁) * ↑x = v * x * (1-η₁) , by {ring},
    rw h4 at this,
    exact this},
  have hel11:  (y : R) * (1 - η₁) ∈ P, by {
    obtain ⟨v, hv ⟩:= hel1,
    rw mul_assoc at hv,
    have hvunit : is_unit (v : R), by {exact units.is_unit v, },
    apply (unit_mul_mem_iff_mem P hvunit).1 _,
    apply hP2,
    apply hv,},
  have hel22 : (x : R) * (1 - η₁) ∈ P, by {
      obtain ⟨v, hv ⟩:= hel2,
    rw mul_assoc at hv,
    have hvunit : is_unit (v : R), by {exact units.is_unit v, },
    apply (unit_mul_mem_iff_mem P hvunit).1 _,
    apply hP2,
    apply hv,
  },
  have hPrime:= hP1.is_prime,
  have hprime2 := is_prime.mem_or_mem hPrime hel11,
  have hprime3 := is_prime.mem_or_mem hPrime hel22,
  have HC : (1 - η₁) ∈ P → false,
    begin
    intro h,
    have eta_sub_one_ne_zero :=  sub_ne_zero.mpr (ne.symm hwlog),
    have hηprime : is_prime (ideal.span ({1 - η₁} : set R)) := by {
      rw span_singleton_prime eta_sub_one_ne_zero,
      apply one_sub_zeta_prime ph hη₁ hwlog,},
    have H5 : is_prime (ideal.span ({(p : ℤ)} : set ℤ)), by {
    have h2 : (p : ℤ) ≠ 0, by {simp, },
    have h1 : prime (p : ℤ) , by {simp only [coe_coe], rw  ←prime_iff_prime_int, exact _inst_4.out,},
    rw (span_singleton_prime h2),
    apply h1,  },
    have hηP : (ideal.span ({1 - η₁} : set R)) = P, by {
      have hRdim1 : ring.dimension_le_one R,  by {exact is_dedekind_domain.dimension_le_one,},
      have hle : (ideal.span ({1 - η₁} : set R)) ≤ P, by {rw span_le, simp [h],},
      apply ((@ring.dimension_le_one.prime_le_prime_iff_eq _ _ hRdim1 _ _ hηprime hPrime _).1 hle),
      simp,
      exact sub_ne_zero.mpr (ne.symm hwlog)},
    have hcapZ : P.comap (int.cast_ring_hom R) = ideal.span ({(p : ℤ)} : set ℤ), by {
      have H1 : ideal.span ({(p : ℤ)} : set ℤ) ≤ P.comap (int.cast_ring_hom R), by {
        rw ←hηP,
        apply le_comap_of_map_le _,
        rw map_span,
        simp,
        rw span_singleton_le_span_singleton,
        apply zeta_sub_one_dvb_p ph hη₁ hwlog},
      have H2 : is_prime (P.comap (int.cast_ring_hom R)),
        by {apply @is_prime.comap _ _ _ _ _ _ _ _ hPrime,},
      have H3 : ring.dimension_le_one ℤ, by {exact is_dedekind_domain.dimension_le_one, },
      have H4 :  (ideal.span ({(p : ℤ)} : set ℤ)) ≠ ⊥, by {simp,},
      apply ((@ring.dimension_le_one.prime_le_prime_iff_eq _ _ H3 _ _ H5 H2 H4).1 H1).symm,},
    have hxyinP : (x + y : R) ∈ P, by {
      have H1 : (x : R) + η₁* y ∈ P, by { apply hiP, apply submodule.mem_span_singleton_self},
      have H2 : η₁ * y = y - y * (1 - η₁), by {ring},
      rw H2 at H1,
      have H3 : ↑x + (↑y - ↑y * (1 - η₁)) = (↑x + ↑y) + (-↑y * (1 - η₁)), by {ring},
      rw H3 at H1,
      have H4 : -↑y * (1 - η₁) ∈ P, by {rw ←hηP, rw ideal.mem_span_singleton',
      refine ⟨-(y : R), rfl⟩, },
      apply (ideal.add_mem_iff_left P H4).1 H1,},
    have hxyinP2 : (x + y ) ∈ ideal.span ({(p : ℤ)} : set ℤ), by {rw ←hcapZ, simp [hxyinP]},
    rw mem_span_singleton at hxyinP2,
    apply absurd hxyinP2 hp2,
    end,
  cases hprime2,
  cases hprime3,
  obtain ⟨a, b, hab ⟩ := hp,
  have hone := P.add_mem (ideal.mul_mem_left _ a hprime3) (ideal.mul_mem_left _ b hprime2),
  norm_cast at hone,
  rw hab at hone,
  norm_cast at hone,
  rw ←eq_top_iff_one at hone,
  have hcontra := is_prime.ne_top hPrime,
  rw hone at hcontra,
  simp only [ne.def, eq_self_iff_true, not_true] at hcontra,
  exact hcontra,
  apply HC hprime3,
  apply HC hprime2,
end

lemma aux_lem_flt [fact (p : ℕ).prime] (p5 : 5 ≤ p) {x y z : ℤ}
  (H : x ^ (p : ℕ) + y ^ (p : ℕ) = z ^ (p : ℕ))
  (caseI : ¬ ↑p ∣ x * y * z) : ¬ (p : ℤ) ∣ (x + y : ℤ) :=
begin
  sorry,
end

lemma flt_ideals_coprime [fact (p : ℕ).prime] (p5 : 5 ≤ p) {x y z : ℤ}
  (H : x ^ (p : ℕ) + y ^ (p : ℕ) = z ^ (p : ℕ)) {η₁ η₂ : R} (hxy : is_coprime x y)
  (hη₁ : η₁ ∈ nth_roots_finset p R) (hη₂ : η₂ ∈ nth_roots_finset p R) (hdiff : η₁ ≠ η₂)
  (caseI : ¬ ↑p ∣ x * y * z) : is_coprime (flt_ideals p x y hη₁) (flt_ideals p x y hη₂) :=
begin
   --how does wlog work? I want to have η₁ ≠ 1...
  by_cases h : η₁ ≠ 1,
   apply flt_ideals_coprime2 p5 hη₁ hη₂ hdiff hxy (aux_lem_flt p5 H caseI) h,
  have h2 : η₂ ≠ 1, by {simp at h, rw h at hdiff, exact hdiff.symm},
  have := flt_ideals_coprime2 p5 hη₂ hη₁ hdiff.symm hxy (aux_lem_flt p5 H caseI) h2,
  apply is_coprime.symm,
  exact this,
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
