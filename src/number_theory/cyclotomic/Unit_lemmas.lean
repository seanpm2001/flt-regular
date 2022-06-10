import number_theory.cyclotomic.galois_action_on_cyclo
import number_theory.cyclotomic.cyclotomic_units
import ring_theory.roots_of_unity
import number_theory.number_field

variables (p : ℕ+) (K : Type*) [field K] [algebra ℚ K]


open_locale big_operators non_zero_divisors number_field pnat cyclotomic
open is_cyclotomic_extension
open cyclotomic_ring
open number_field polynomial

local notation `KK` := cyclotomic_field p ℚ
local notation `RR` := 𝓞 (cyclotomic_field p ℚ)
local notation `ζ` := zeta p ℚ KK

local attribute [instance] is_cyclotomic_extension.number_field
universe u
noncomputable theory

/-- zeta now as a unit in the ring of integers. This way there are no coe issues-/
def zeta_unit' : RRˣ :={
val:= (⟨zeta p ℚ KK, zeta_integral p ℚ⟩ : RR),
inv:= (⟨(zeta p ℚ KK)^((p-1): ℕ), zeta_integral' p ℚ (p-1)⟩ : RR),
val_inv := by { have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 cases h2, cases p, dsimp at *, ext1, dsimp at *, rw pow_sub₀, rw this, simp,
 apply mul_inv_cancel, apply h3, apply h3, linarith,},
inv_val:= by{have:= zeta_pow p ℚ KK ,
  have h1:= zeta_primitive_root p ℚ KK, have h2:= h1.is_unit p.2, have h3:=h2.ne_zero,
 cases h2, cases p, dsimp at *, ext1, dsimp at *, rw pow_sub₀, rw this, simp,
 apply inv_mul_cancel, apply h3, apply h3, linarith,} ,}

local notation `ζ'`:= zeta_unit' p

lemma zeta_unit_coe: (ζ' : KK) = ζ :=by refl

lemma zeta_unit_pow : (ζ')^(p : ℤ) = 1 :=
begin
simp_rw zeta_unit',
ext1,
ext1,
simp,
apply zeta_pow,
end

lemma zeta_unit_coe_2 : is_primitive_root (ζ' : RR) p :=
begin
 have z1 := zeta_primitive_root p ℚ KK,
 have : (algebra_map RR KK) ((ζ' : RR)) = ζ, by{refl, },
 rw ← this at z1,
 apply is_primitive_root.of_map_of_injective z1,
 apply is_fraction_ring.injective,
end

--to fix this we have to replace KK by a general cyclotomic extension
local attribute [-instance] cyclotomic_field.algebra
instance zzzz : is_cyclotomic_extension {p} ℚ KK := sorry

/-- `is_gal_conj_real x` means that `x` is real. -/
def is_gal_conj_real (x : KK) : Prop := gal_conj KK p x = x

--bunch of lemmas that should be stated more generally if we decide to go this way
lemma unit_coe (u : RRˣ) : (u : RR) * ((u⁻¹ : RRˣ) : RR) = 1 :=
begin
  norm_cast,
  simp only [mul_right_inv, units.coe_one],
end

lemma unit_coe_non_zero (u : RRˣ) : (u : KK) ≠ 0 :=
begin
  by_contra h,
  have : (u : KK) * ((u⁻¹ : RRˣ ) : KK) = 1,
  { rw [coe_coe, coe_coe, ←subalgebra.coe_mul, ←units.coe_mul, mul_right_inv], refl },
  rw h at this,
  simp at this,
  exact this,
end

lemma coe_life (u : RRˣ) : ((u : RR) : KK)⁻¹ = ((u⁻¹ : RRˣ) : RR) :=
begin
  have hu:= unit_coe_non_zero p u,
  rw [←coe_coe, ←coe_coe, inv_eq_one_div, div_eq_iff hu, coe_coe, coe_coe,
      ←subalgebra.coe_mul, ←units.coe_mul, mul_left_inv], refl
end

lemma auxil (a b c d : RRˣ) (h : a * b⁻¹ = c * d ) : a * d⁻¹ = b * c :=
begin
  rw mul_inv_eq_iff_eq_mul at *,
  rw h,
  apply symm,
  rw mul_assoc,
  rw mul_comm,
end
section totient

open nat

localized "notation `φ` := nat.totient" in nat

/-- The fact that `f` is `gcd_mult`. -/
def is_gcd_mult (f : ℕ → ℕ) : Prop :=
  ∀ a b: ℕ, f (a.gcd b) * f (a * b) = f a * f b * (a.gcd b)

lemma gcd_self_pow (p n m : ℕ) : (p ^ n).gcd (p ^ m) = p ^ (min n m) :=
begin
  wlog h : n ≤ m,
  rw [min_eq_left h],
  apply gcd_eq_left,
  exact pow_dvd_pow p h,
end

lemma totient_pow_mul_self {p : ℕ} (n m : ℕ) (h : nat.prime p)  :
   φ ((p ^ n).gcd (p ^ m)) * φ (p ^ n * p ^ m) = φ (p ^ n) * φ (p ^ m) * (p ^ n).gcd (p ^ m) :=
begin
  wlog hnm : n ≤ m using [n m], -- chris: this is a nice tactic you'll be interested in!
  --have hnm : n ≤ m, sorry,
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [nat.gcd_one_left, mul_one, one_mul, pow_zero]},
  rcases m.eq_zero_or_pos with rfl | hm,
  { simp only [mul_one, one_mul, nat.gcd_one_right, totient_one, pow_zero]},
  have h20 : 0 < n + m, by linarith,
  rw [totient_prime_pow h hn, totient_prime_pow h hm, ←pow_add, totient_prime_pow h h20,
      gcd_self_pow, min_eq_left hnm, totient_prime_pow h hn],
  have : p ^ (n + m - 1) * (p - 1) = (p ^ (m - 1) * (p - 1))*p^n ,
  by {have : p^(n+m-1)=p^n * p^(m-1), by  {rw nat.add_sub_assoc, apply pow_add, linarith,},
  rw [this, mul_rotate],},
  rw [this, ←mul_assoc],
end
/-
def finsupp_min  (f g  : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  {support := f.support ∩ g.support,
  to_fun := (λ x, min (f.to_fun x) (g.to_fun x)),
  mem_support_to_fun := by {intros a, split, intro ha, simp at *, apply not_or ha.1 ha.2,
  intro ha, simp at *, rw decidable.not_or_iff_and_not at ha, convert ha,},}

lemma gcd_min_supp (a b  : ℕ) (ha : a ≠ 0) (hb: b ≠ 0) :
  (finsupp_min a.factorization b.factorization).prod pow = a.gcd b :=
begin
  have hgab : a.gcd b ≠ 0, by { sorry},
  rw  ←factorization_prod_pow_eq_self hgab,
  apply congr,
  apply congr,
  refl,
  rw (factorization_gcd ha hb),
  rw finsupp_min,
  work_on_goal 1 { dsimp at *, simp at *, dsimp at *, ext1, refl }, refl,
end
-/

lemma p_val_nat_div_coprime (a p : ℕ) (ha :  0 < a ) (hp : p.prime) : coprime p (a/ p^(padic_val_nat p a)) :=
begin
refine coprime_of_dvd _,
intros q hq hpq,
rw dvd_prime at hpq,
cases hpq,
rw hpq at hq,
intro H,
exact not_prime_one hq,
rw hpq,
intro H,
haveI : fact p.prime, by {simp [hp], exact {out := trivial},},
have h1 :  p^(padic_val_nat p a) ∣ a, by  {have:= padic_val_int_dvd p a, norm_cast at this,
  convert this,},
have:= dvd_div_iff  (h1),
rw this at H,
have c1:= pow_succ_padic_val_nat_not_dvd ha,
have r1 : (p^(padic_val_nat p a))*p = p^((padic_val_nat p a) + 1), by {rw pow_add, simp, },
rw r1 at H,
exact c1 H,
exact _inst,
exact hp,
end

lemma prime_ext2 (a b : ℕ) (ha : 0 < a) (hb : 0 <b ) (hab : ¬ a.coprime b) :
 ∃ (p: ℕ) (r s: ℕ+), nat.prime p ∧ p^(r : ℕ) ∣ a ∧ p^(s : ℕ) ∣ b ∧
  nat.coprime (p^(r+s : ℕ)) ((a*b)/p^(r+s : ℕ))
  ∧ nat.coprime (p) (a/p^(r : ℕ))
  ∧ nat.coprime (p) (b/p^(s : ℕ)) :=
begin
  rw prime.not_coprime_iff_dvd at hab,
  obtain ⟨p, hp, h2⟩ := hab,
  haveI : fact p.prime,
  exact {out := hp},
  refine ⟨p, ⟨(padic_val_nat p a), by {have := (one_le_padic_val_nat_of_dvd ha h2.1), linarith, }⟩,
    ⟨(padic_val_nat p b), by {have := (one_le_padic_val_nat_of_dvd hb h2.2), linarith, }⟩, hp,
    by {have:= padic_val_int_dvd p a, norm_cast at this, convert this, },
    by {have:= padic_val_int_dvd p b, norm_cast at this, convert this, }, _⟩,
  simp,
  split,
  rw ←padic_val_nat.mul p (ne_of_gt ha) (ne_of_gt hb),
  apply coprime.pow_left,
  apply p_val_nat_div_coprime (a*b) p (mul_pos ha hb) hp,
  split,
  apply p_val_nat_div_coprime a p ha hp,
  apply p_val_nat_div_coprime b p hb hp,
end

/-- An induction principle. -/
def sub_induction2  {P : ℕ → ℕ → Sort u}
  (H : ∀n m, ((∀ x y, x < n → y < m → P x y) → P n m)) : Π (n m : ℕ), P n m :=
begin
  intros n m,
  apply H _ _,
  induction n,
  work_on_goal 1 { intros x y ᾰ ᾰ_1, dsimp at *, simp at *, cases ᾰ }, intros x y H1 H2,
  apply or.by_cases (decidable.lt_or_eq_of_le (le_of_lt_succ H1)),
  intro hn,
  apply n_ih,
  apply hn,
  apply H2,
  intro hn,
  rw hn,
  apply H _ _,
  intros a b hab hab2,
  apply n_ih,
  apply hab,
  linarith,
end

lemma totient_mul_gen : is_gcd_mult φ :=
begin
  apply sub_induction2,
  intros n m hxy,
  by_cases hco : coprime n m,
  rw coprime at hco,
  rw hco,
  simp only [totient_one, one_mul, mul_one],
  apply totient_mul hco,
  by_cases g1 : 0  < n,
  by_cases g2 : 0 < m,
  obtain ⟨p, r ,s, hprs⟩ := (prime_ext2 n m g1 g2 hco),
  have h1: n = p^(r : ℕ) * (n / p^(r : ℕ)), by {apply (nat.mul_div_cancel' hprs.2.1).symm, },
  have h2: m = p^(s : ℕ) * (m / p^(s : ℕ)), by {apply (nat.mul_div_cancel' hprs.2.2.1).symm,},
  rw [h1,h2],
  have : p ^ ↑r * (n / p ^ ↑r) * (p ^ ↑s * (m / p ^ ↑s)) = p^(r+s : ℕ) * (n*m / p^(r+s : ℕ)),
  by { simp_rw [←mul_assoc], rw [(nat.mul_div_cancel' hprs.2.1)], rw mul_assoc,
    rw [(nat.mul_div_cancel' hprs.2.2.1)], apply symm, apply nat.mul_div_cancel',
    convert mul_dvd_mul hprs.2.1 hprs.2.2.1, apply pow_add,},
  rw this,
  rw totient_mul hprs.2.2.2.1,
  simp_rw totient_mul  (coprime.pow_left r hprs.2.2.2.2.1),
  simp_rw totient_mul (coprime.pow_left s hprs.2.2.2.2.2),
  have e2 : (n*m / p^(r+s : ℕ)) = (n/ p^(r : ℕ)) * (m / p^(s: ℕ)) , by { rw pow_add,
    apply (nat.div_mul_div_comm hprs.2.1 hprs.2.2.1).symm,},
  rw e2,
  rw coprime.gcd_mul _ (coprime.pow_left s hprs.2.2.2.2.2),
  simp_rw nat.gcd_comm,
  simp_rw coprime.gcd_mul _ (coprime.pow_left r hprs.2.2.2.2.1),
  have h33:= (coprime.pow_left r hprs.2.2.2.2.2),
  rw coprime at h33,
  rw nat.gcd_comm at h33,
  rw h33,
  have h44:= (coprime.pow_left s hprs.2.2.2.2.1),
  rw coprime at h44,
  rw h44,
  simp,
  rw (gcd_self_pow p s r),
  have h55:= (coprime.pow_left (min (s : ℕ) (r : ℕ)) hprs.2.2.2.2.1),
  have h66:= coprime.gcd_right (m/p^(s : ℕ)) h55,
  simp_rw totient_mul h66,
  have i1 : n/p^(r : ℕ) < n, by {apply (nat.div_lt_self g1), have : 1 < p ,
      by { apply prime.one_lt hprs.1 },
    have h0 : 1 = 1^(0 : ℕ), by {simp only [one_pow],},
    rw h0,
    apply pow_lt_pow_of_lt_right this r.prop,},
  have i2 : m/p^(s : ℕ) < m, by {apply (nat.div_lt_self g2), have : 1 < p ,
      by { apply prime.one_lt hprs.1 },
    have h0 : 1 = 1^(0 : ℕ), by {simp only [one_pow],},
    rw h0,
    apply pow_lt_pow_of_lt_right this s.prop,},
  have hi1i2 := hxy (n/p^(r : ℕ)) (m/p^(s : ℕ)) i1 i2,
  rw ←(gcd_self_pow p s r),
  have e2 := totient_pow_mul_self (r : ℕ) (s : ℕ) hprs.1,
  have V := congr (congr_arg has_mul.mul hi1i2) e2,
  rw pow_add,
  rw ←mul_assoc,
  have st1 : ∀ (a b c d  : ℕ), a * b * c * d = b * d * a * c, by {intros a b c d, ring},
  have st2 : ∀ (a b c d e f : ℕ), a * b * c * d * e * f = b * d * f * a * c * e,
    by {intros a b c d e f, ring},
  rw st1,
  simp_rw ← mul_assoc at *,
   simp_rw ← mul_assoc at *,
  rw st2,
  rw nat.gcd_comm,
  have st3 : (p^(r : ℕ)).gcd (p^(s : ℕ)) = (p^(s : ℕ)).gcd (p^(r : ℕ)), by {apply nat.gcd_comm},
  rw ←st3,
  exact V,
  simp at g2,
  rw g2,
  simp,
  simp at g1,
  rw g1,
  simp,
end

lemma totient_super_multiplicative (a b : ℕ) : a.totient * b.totient ≤ (a * b).totient :=
begin
 let d := a.gcd b,
  by_cases d ≠ 0,
  {have := totient_mul_gen a b,
  simp only [ne.def, nat.gcd_eq_zero_iff, not_and] at *,
  have hd: 0 < d.totient,  by {apply nat.totient_pos, simp_rw d, by_cases ha:  a = 0,
    apply gcd_pos_of_pos_right _ (nat.pos_of_ne_zero (h ha)),
    apply gcd_pos_of_pos_left _(nat.pos_of_ne_zero ( ha)),},
  by_cases HA : a ≠ 0,
  by_cases HB : b ≠ 0,
  have ha: 0 < a.totient,
    by {apply nat.totient_pos, by_contra H,  simp only [ne.def, not_lt, _root_.le_zero_iff] at *,
    rw H at HA,  simp only [eq_self_iff_true, not_true] at HA, exact HA,},
  have hb: 0 < b.totient,
    by {apply nat.totient_pos, by_contra H,  simp only [ne.def, not_lt, _root_.le_zero_iff] at *,
    rw H at HB,  simp only [eq_self_iff_true, not_true] at HB, exact HB},
  have hdd: d.totient ≤ d, by {apply nat.totient_le,},
  have hr :  φ (d) * (φ (a) * φ (b)) ≤ φ (d) * φ (a * b) ↔ (φ (a) * φ (b)) ≤ φ (a * b) ,
  by {apply mul_le_mul_left hd,},
  simp_rw ← hr,
  rw this,
  rw mul_comm,
  exact mul_le_mul_left' hdd (φ a * φ b),
  simp at HB,
  rw HB,
   simp only [totient_zero, mul_zero],
   simp only [not_not] at HA,
  rw HA,
   simp only [totient_zero, zero_mul],
  },
   simp only [nat.gcd_eq_zero_iff, not_not] at h,
   simp only [ h.1, totient_zero, zero_mul],
end

end totient

variable {K}

lemma contains_two_primitive_roots {p q : ℕ} {x y : K} (hx : is_primitive_root x p)
  (hy : is_primitive_root y q) :
  (lcm p q ).totient ≤ (finite_dimensional.finrank ℚ K) :=
begin
  let k := lcm p q,
  rcases nat.eq_zero_or_pos p with rfl | hppos,
  { simp },
  rcases nat.eq_zero_or_pos q with rfl | hqpos,
  { simp },
  let k := lcm p q,
  have hkpos : 0 < k := nat.pos_of_ne_zero (nat.lcm_ne_zero  hppos.ne' hqpos.ne'),
  set xu := is_unit.unit (hx.is_unit hppos) with hxu,
  let yu := is_unit.unit (hy.is_unit hqpos),
  have hxmem : xu ∈ roots_of_unity ⟨k, hkpos⟩ K,
  { rw [mem_roots_of_unity, pnat.mk_coe, ← units.coe_eq_one, units.coe_pow, is_unit.unit_spec],
    exact (hx.pow_eq_one_iff_dvd _).2 (dvd_lcm_left _ _) },
  have hymem : yu ∈ roots_of_unity ⟨k, hkpos⟩ K,
  { rw [mem_roots_of_unity, pnat.mk_coe, ← units.coe_eq_one, units.coe_pow, is_unit.unit_spec],
    exact (hy.pow_eq_one_iff_dvd _).2 (dvd_lcm_right _ _) },
  have hxuord : order_of (⟨xu, hxmem⟩ : roots_of_unity ⟨k, hkpos⟩ K) = p,
  { rw [← order_of_injective (roots_of_unity ⟨k, hkpos⟩ K).subtype subtype.coe_injective,
      subgroup.coe_subtype, subgroup.coe_mk, ← order_of_units, is_unit.unit_spec],
    exact hx.eq_order_of.symm },
  have hyuord : order_of (⟨yu, hymem⟩ : roots_of_unity ⟨k, hkpos⟩ K) = q,
  { rw [← order_of_injective (roots_of_unity ⟨k, hkpos⟩ K).subtype subtype.coe_injective,
      subgroup.coe_subtype, subgroup.coe_mk, ← order_of_units, is_unit.unit_spec],
    exact hy.eq_order_of.symm },
  obtain ⟨g : roots_of_unity ⟨k, hkpos⟩ K, hg⟩ := is_cyclic.exists_monoid_generator,
  obtain ⟨nx, hnx⟩ := hg ⟨xu, hxmem⟩,
  obtain ⟨ny, hny⟩ := hg ⟨yu, hymem⟩,
  obtain ⟨p₁, hp₁⟩ := dvd_lcm_left p q,
  obtain ⟨q₁, hq₁⟩ := dvd_lcm_left p q,
  have H : order_of g = k,
  { refine nat.dvd_antisymm (order_of_dvd_of_pow_eq_one _) (nat.lcm_dvd _ _),
    { have := (mem_roots_of_unity _ _).1 g.2,
      simp only [subtype.val_eq_coe, pnat.mk_coe] at this,
      exact_mod_cast this },
    { rw [← hxuord, ← hnx, order_of_pow],
      exact nat.div_dvd_of_dvd ((order_of g).gcd_dvd_left nx), },
    { rw [← hyuord, ← hny, order_of_pow],
      exact nat.div_dvd_of_dvd ((order_of g).gcd_dvd_left ny) } },
  sorry,
  all_goals { apply_instance }
end

variable (K)

lemma totient_le_one_dvd_two {a : ℕ} (han : 0 < a) (ha : a.totient ≤ 1) : a ∣ 2 :=
begin
 cases nat.totient_eq_one_iff.1 (show a.totient = 1, by linarith [nat.totient_pos han]) with h h;
  simp [h]
end

-- please speed this up
-- is it faster now?
lemma roots_of_unity_in_cyclo_aux (x : KK) (n l : ℕ) (hl : l ∈ n.divisors)
(hx : x ∈ RR)
(hhl : (cyclotomic l {x // x ∈ 𝓞 (cyclotomic_field p ℚ)}).is_root ⟨x, hx⟩) : l ∣ 2 * p :=
begin
by_contra,
  have hpl': is_primitive_root (⟨x, hx⟩ : RR) l, by {rw is_root_cyclotomic_iff.symm, apply hhl,
  apply_instance,
  fsplit,
  rw nat.cast_ne_zero,
  apply (ne_of_gt (nat.pos_of_mem_divisors hl)),},
  have hpl: is_primitive_root x l, by {have : (algebra_map RR KK) (⟨x, hx⟩) = x, by{refl},
  have h4 := is_primitive_root.map_of_injective hpl', rw ← this,
  apply h4,
  apply is_fraction_ring.injective, },
  have hpp: is_primitive_root (ζ' : KK) p, by { rw zeta_unit_coe, apply zeta_primitive_root,},
  have KEY := contains_two_primitive_roots hpl hpp,
  have hirr : irreducible (cyclotomic p ℚ), by {exact cyclotomic.irreducible_rat p.prop},
  have hrank:= is_cyclotomic_extension.finrank KK hirr,
  rw hrank at KEY,
  have pdivlcm : (p : ℕ) ∣ lcm l p := dvd_lcm_right l ↑p,
  cases pdivlcm,
  have ineq1 := totient_super_multiplicative (p: ℕ) pdivlcm_w,
  rw ←pdivlcm_h at ineq1,
  have KEY3 := (mul_le_iff_le_one_right (nat.totient_pos p.prop)).mp (le_trans ineq1 KEY),
  have pdiv_ne_zero : 0 < pdivlcm_w, by {by_contra,
  simp only [not_lt, le_zero_iff] at h,
  rw h at pdivlcm_h,
  simp only [mul_zero, lcm_eq_zero_iff, pnat.ne_zero, or_false] at pdivlcm_h,
  apply absurd pdivlcm_h (ne_of_gt (nat.pos_of_mem_divisors hl)),},
  have K5 := (nat.dvd_prime nat.prime_two).1 (totient_le_one_dvd_two pdiv_ne_zero KEY3),
  cases K5,
  rw K5 at pdivlcm_h,
  simp only [mul_one] at pdivlcm_h,
  rw lcm_eq_right_iff at pdivlcm_h,
  have K6 : (p : ℕ) ∣ 2*(p : ℕ) := dvd_mul_left ↑p 2,
  apply absurd (dvd_trans pdivlcm_h K6) h,
  simp only [eq_self_iff_true, normalize_eq, pnat.coe_inj],
  rw K5 at pdivlcm_h,
  rw mul_comm at pdivlcm_h,
  have := dvd_lcm_left l (p : ℕ),
  simp_rw pdivlcm_h at this,
  apply absurd this h,
end

--do more generally
lemma roots_of_unity_in_cyclo (hpo : odd (p : ℕ)) (x : KK)
  (h : ∃ (n : ℕ) (h : 0 < n), x^(n: ℕ) = 1) :
  ∃ (m : ℕ) (k : ℕ+), x = (-1)^(k : ℕ) * (ζ')^(m : ℕ) :=
begin
  obtain ⟨n, hn0, hn⟩ := h,
  have hx : x ∈ RR, by {rw mem_ring_of_integers,
  refine ⟨(X ^ n - 1),_⟩,
  split,
  { exact (monic_X_pow_sub_C 1 (ne_of_lt hn0).symm) },
  { simp only [hn, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self] },},
  have hxu : (⟨x, hx⟩ : RR)^n = 1, by {ext, simp only [submonoid_class.mk_pow, set_like.coe_mk,
    submonoid_class.coe_one], apply hn} ,
  have H: ∃ (m : ℕ) (k: ℕ+), (⟨x, hx⟩ : RR) = (-1)^(k : ℕ) * (ζ')^(m : ℕ),
  by {obtain ⟨l, hl, hhl⟩ := ((_root_.is_root_of_unity_iff hn0 _).1 hxu),
  have hlp := roots_of_unity_in_cyclo_aux p x n l hl hx hhl,
  simp only [is_root.def] at hhl,
  have isPrimRoot : is_primitive_root (ζ' : RR) p, by {apply zeta_unit_coe_2},
  have hxl : (⟨x, hx⟩: RR)^l =1 , by {apply is_root_of_unity_of_root_cyclotomic _ hhl,
    simp only [nat.mem_divisors, dvd_refl, ne.def, true_and],
   apply (pos_iff_ne_zero.1 (nat.pos_of_mem_divisors hl))},
  have hxp' : (⟨x, hx⟩: RR)^(2* p : ℕ) = 1 , by {cases hlp,
  rw [hlp_h, pow_mul, hxl], simp only [one_pow],},
  have hxp'': (⟨x, hx⟩: RR)^(p : ℕ) = 1 ∨ (⟨x, hx⟩: RR)^(p : ℕ) = -1,
  by {rw mul_comm at hxp', rw pow_mul at hxp',
  apply eq_or_eq_neg_of_sq_eq_sq (⟨x, hx⟩^(p : ℕ) : RR) 1 _,
  simp only [submonoid_class.mk_pow, one_pow],
  apply hxp',},
  cases hxp'',
  obtain ⟨i, hi,Hi⟩ := (is_primitive_root.eq_pow_of_pow_eq_one isPrimRoot hxp'' p.prop),
  refine ⟨i, 2, _⟩,
  simp only [pnat.coe_bit0, pnat.one_coe, neg_one_sq, one_mul],
  apply Hi.symm,
  have hone : (-1 : RR)^(p : ℕ)= (-1 : RR), by {apply odd.neg_one_pow hpo,},
  have hxp3 : (-1 * ⟨x, hx⟩: RR)^( p : ℕ) = 1, by {rw [mul_pow, hone, hxp''],
  simp only [mul_neg, mul_one, neg_neg],},
  obtain ⟨i, hi,Hi⟩ := (is_primitive_root.eq_pow_of_pow_eq_one isPrimRoot hxp3 p.prop),
  refine ⟨i, 1, _⟩,
  simp_rw Hi,
  simp only [pnat.one_coe, pow_one, neg_mul, one_mul, neg_neg],},
  obtain ⟨m, k, hmk⟩ := H,
  refine ⟨m, k, _⟩,
  have eq : ((⟨x, hx⟩ : RR) : KK) = x := rfl,
  rw [←eq, hmk],
  norm_cast,
  rw [subalgebra.coe_mul],
  congr' 1,
  { push_cast },
  { simp only [units.coe_pow, subsemiring_class.coe_pow, coe_coe]}
end

lemma zeta_runity_pow_even (hpo : odd (p : ℕ)) (n : ℕ) : ∃ (m : ℕ),
  (ζ')^n = (ζ')^(2*m) :=
begin
  by_cases n = 0,
  use 0,
  rw h,
  simp only [mul_zero],
  rw odd at hpo,
  obtain ⟨r, hr⟩ := hpo,
  have he : 2*(r+1)*n=p*n+n, by {rw hr, linarith,},
  use (r+1)*n,
  rw ←mul_assoc,
  simp_rw he,
  rw pow_add,
  have h1 : (zeta_unit' p)^ ((p : ℤ) * n) = 1,
  by {have:= zeta_unit_pow p, simp_rw zpow_mul, simp_rw this, simp only [one_zpow],},
  norm_cast at h1,
  simp_rw h1,
  simp only [one_mul],
end


lemma unit_inv_conj_not_neg_zeta_runity (h : 2 < p) (u : RRˣ) (n : ℕ) :
  u * (unit_gal_conj (zeta_primitive_root p ℚ _) u)⁻¹ ≠ -(ζ') ^ n :=
begin
  by_contra H,
  sorry,
end

-- this proof has mild coe annoyances rn
lemma unit_inv_conj_is_root_of_unity (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ m : ℕ, u * (unit_gal_conj (zeta_primitive_root p ℚ _) u)⁻¹ = (ζ' ^ (m))^2 :=
begin
  have := mem_roots_of_unity_of_abs_eq_one
    (u * (unit_gal_conj (zeta_primitive_root p ℚ _) u)⁻¹ : KK) _ _,
  have H:= roots_of_unity_in_cyclo p hpo
    ((u * (unit_gal_conj (zeta_primitive_root p ℚ _) u)⁻¹ : KK)) this,
  obtain ⟨n, k, hz⟩ := H,
  simp_rw ← pow_mul,
  have hk := nat.even_or_odd k,
  cases hk,
  {simp only [hk.neg_one_pow, coe_coe, one_mul] at hz,
  simp_rw coe_life at hz,
  rw [←subalgebra.coe_mul, ←units.coe_mul, ←subalgebra.coe_pow, ←units.coe_pow] at hz,
  norm_cast at hz,
  rw hz,
  refine (exists_congr $ λ a, _).mp (zeta_runity_pow_even p hpo n),
  { rw mul_comm } },
  { by_contra hc,
    simp [hk.neg_one_pow] at hz,
    simp_rw coe_life at hz,
    rw [←subalgebra.coe_mul, ←units.coe_mul, ←subalgebra.coe_pow, ←units.coe_pow] at hz,
    norm_cast at hz,
    simpa [hz] using unit_inv_conj_not_neg_zeta_runity p h u n },
  { exact unit_lemma_val_one (zeta_primitive_root p ℚ _) u,},
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj (zeta_primitive_root p ℚ _) u)⁻¹ : KK) =
      (↑(unit_gal_conj (zeta_primitive_root p ℚ _) u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simp,
    rw coe_life,
    norm_cast,
    apply uni_gal_conj_inv, },
end


lemma unit_lemma_gal_conj (h : 2 < p) (hpo : odd (p : ℕ)) (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), (is_gal_conj_real p (x : KK)) ∧ (u : KK) = x * (ζ' ^ n) :=

begin
  have := unit_inv_conj_is_root_of_unity p h hpo u,
  obtain ⟨m, hm⟩ := this,
  let xuu:=u * ((ζ')⁻¹ ^ (m)),
  use [xuu, m],
   rw is_gal_conj_real,
  have hy : u * (ζ' ^ ( m))⁻¹ = (unit_gal_conj (zeta_primitive_root p ℚ _) u) * ζ' ^ ( m),
  by {rw pow_two at hm,
  have := auxil p u (unit_gal_conj (zeta_primitive_root p ℚ _) u) (ζ' ^ (m)) (ζ' ^ (m)),
  apply this hm},
  dsimp,
  simp only [inv_pow, alg_hom.map_mul],
  have hz: gal_conj KK p (ζ'^ ( m))⁻¹ =(ζ' ^ ( m)) ,
  by {simp_rw zeta_unit', simp},
  rw ← coe_coe,
  rw ← coe_coe,
  split,
  rw (_ : (↑(ζ' ^ m)⁻¹ : KK) = (ζ' ^ m : KK)⁻¹),
  rw hz,
  have hzz := unit_gal_conj_spec (zeta_primitive_root p ℚ _) u,
  rw hzz,
  simp only [coe_coe],
  rw [←subalgebra.coe_pow, ←units.coe_pow, ←subalgebra.coe_mul, ←units.coe_mul],
  rw ← hy,
  simp only [subalgebra.coe_pow, subalgebra.coe_eq_zero, mul_eq_mul_left_iff,
  units.ne_zero, or_false, subalgebra.coe_mul, units.coe_pow, units.coe_mul],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  simp_rw ← inv_pow,
  simp only [inv_pow, coe_coe],
  rw ← coe_life,
  simp only [subalgebra.coe_pow, units.coe_pow],
  simp,
  norm_cast,
  rw [mul_assoc, ←subalgebra.coe_mul, units.inv_mul],
  simp,
end

/-
lemma unit_lemma (u : RRˣ) :
  ∃ (x : RRˣ) (n : ℤ), element_is_real (x : KK) ∧ (u : KK) = x * (zeta_runity p ℚ) ^ n :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  { have : ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (zeta_runity p ℚ) ^ (2 * m),
    sorry, --follows from above with some work
          -- what we have shows its +- a power of zeta_runity
    obtain ⟨m, hm⟩ := this,
    use [u * (zeta_runity p ℚ)⁻¹ ^ m, m],
    split,
    { rw element_is_real,
      intro φ,
      have := congr_arg (conj ∘ φ ∘ coe) hm,
      simp at this,
      simp [alg_hom.map_inv],
      rw ← coe_coe,
      rw ← coe_coe, -- TODO this is annoying
      rw (_ : (↑(zeta_runity p ℚ ^ m)⁻¹ : KK) = (zeta_runity p ℚ ^ m : KK)⁻¹),
      rw alg_hom.map_inv,
      rw ring_hom.map_inv,
      rw mul_inv_eq_iff_eq_mul₀,
      simp,
      sorry, -- wow we should really have some more structure and simp lemmas to tame this beast
      sorry, -- similar silly goal to below
      sorry,
       },
    { simp only [mul_assoc, inv_pow, subalgebra.coe_mul, coe_coe, units.coe_mul, zpow_coe_nat],
      norm_cast,
      simp, }, },
  { exact unit_lemma_val_one p u, },
  { apply is_integral_mul,
    exact number_field.ring_of_integers.is_integral_coe (coe_b u),
    rw (_ : ((unit_gal_conj p u)⁻¹ : KK) = (↑(unit_gal_conj p u⁻¹))),
    exact number_field.ring_of_integers.is_integral_coe (coe_b _),
    simp,
    sorry, -- tis a silly goal
     },
end
-/
