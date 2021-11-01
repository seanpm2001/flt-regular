import number_theory.cyclotomic.basic
import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.number_field_embeddings
import number_theory.cyclotomic.absolute_value

universes u

open finite_dimensional

variables (L : Type u) [field L] [char_zero L]

namespace rat

section singleton

variables (n : ℕ+) [is_cyclotomic_extension {n} ℚ L]

lemma degree : finrank ℚ L = (n : ℕ).totient := sorry

end singleton

end rat

namespace int

section singleton

variables (n : ℕ+)

instance : is_integral_closure (cyclotomic_ring n ℤ ℚ) ℤ (cyclotomic_field n ℚ) := sorry

end singleton

end int

section int_facts

variables (p : ℕ+)



local notation `KK` := cyclotomic_field p ℚ

local notation `RR` := number_field.ring_of_integers (cyclotomic_field p ℚ)

--A.K.A theorem:FLT_facts 3
lemma flt_fact_3 [fact (p : ℕ).prime] (a : RR) :
  ∃ (n : ℤ), (a^(p : ℕ) - n) ∈ ideal.span ({p} : set RR) := sorry

/-- The principal ideal generated by `x + y ζ^i` for integer `x` and `y` -/
noncomputable def flt_ideals (x y : ℤ) (i  : ℕ) : ideal RR :=
  ideal.span ({ x+y*(cyclotomic_ring.zeta p ℚ)^i} : set RR)

lemma flt_fact_2 [fact (p : ℕ).prime] (ph: 5 ≤ p) (x y : ℤ) (i j : ℕ) (h : i ≠ j)
  (hp : is_coprime x y) : (flt_ideals p x y i) + (flt_ideals p x y i) = ⊤ := sorry

instance : number_field KK := sorry

open cyclotomic_ring embeddings

noncomputable theory
open is_cyclotomic_extension
open polynomial

local notation `ζ` := zeta' p ℚ KK

@[simp]
lemma minpoly_zeta' : minpoly ℚ ζ = cyclotomic p ℚ :=
begin
  rw ← map_cyclotomic_int,
  have : is_primitive_root ζ p,
  from zeta'_primitive_root p ℚ (cyclotomic_field p ℚ),
  rw cyclotomic_eq_minpoly this p.pos,
  have : is_integral ℤ ζ,
  from is_primitive_root.is_integral this p.pos,
  have h_mins : minpoly ℚ ζ = (minpoly ℤ ζ).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ this,
  rw h_mins,
  refl,
end

-- a version of cyclotomic_eq_minpoly
lemma minpoly_primitive_root {z : KK} (h : is_primitive_root z p) : minpoly ℚ z = cyclotomic p ℚ :=
begin
  rw ← map_cyclotomic_int,
  rw cyclotomic_eq_minpoly h p.pos,
  have : is_integral ℤ z,
  from is_primitive_root.is_integral h p.pos,
  have h_mins : minpoly ℚ z = (minpoly ℤ z).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions ℚ this,
  rw h_mins,
  refl,
end

def power_basis_zeta : power_basis ℚ KK :=
{ gen := zeta' p ℚ KK,
  dim := (minpoly ℚ (zeta' p ℚ (cyclotomic_field p ℚ))).nat_degree,
  basis := basis.mk (is_integral.linear_independent_pow
      (is_separable.is_integral ℚ (zeta' p ℚ (cyclotomic_field p ℚ)))) sorry,
  basis_eq_pow := by simp }

@[simp]
lemma power_basis_zeta_gen : (power_basis_zeta p).gen = ζ := rfl

-- complex conjugation as a Galois automorphism
def gal_conj : KK →ₐ[ℚ] KK := power_basis.lift (power_basis_zeta p) ζ⁻¹
begin
  simp only [power_basis_zeta_gen, minpoly_zeta'],
  have : is_primitive_root ζ p,
  from zeta'_primitive_root p ℚ (cyclotomic_field p ℚ),
  have : is_primitive_root ζ⁻¹ p,
  exact is_primitive_root.inv' this,
  rw ← minpoly_primitive_root _ this,
  exact minpoly.aeval _ _,
end

@[simp]
lemma gal_conj_zeta : gal_conj p ζ = ζ⁻¹ := power_basis.lift_gen _ _ _
open_locale complex_conjugate

lemma conj_norm_one (x : ℂ) (h : complex.abs x = 1) : conj x = x⁻¹ := sorry

@[simp]
lemma embedding_conj (x : KK) (φ : KK →+* ℂ) : conj (φ x) = φ (gal_conj p x) :=
begin
  swap,
  revert x,
  suffices : φ (gal_conj p ζ) = conj (φ ζ),
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  rw conj_norm_one,
  simp [ring_hom.map_inv],
  sorry,
end

lemma gal_conj_idempotent : (gal_conj p).comp (gal_conj p) = (alg_hom.id _ _) :=
begin
  suffices : (gal_conj p ∘ gal_conj p) ζ = (alg_hom.id ℚ _) ζ,
  sorry, -- this should be a general lemma about checking automorphisms agree only on a generator
  simp,
end

def unit_gal_conj : units RR → units RR :=
λ ⟨u_val, u_inv, u_val_inv, u_inv_val⟩,
  ⟨⟨gal_conj p u_val, sorry⟩, ⟨gal_conj p u_inv, sorry⟩,
  begin
    ext,
    simp only [subalgebra.coe_one, set_like.coe_mk, subalgebra.coe_mul],
    rw ← alg_hom.map_mul,
    rw_mod_cast u_val_inv,
    simp,
  end, begin
    ext,
    simp only [subalgebra.coe_one, set_like.coe_mk, subalgebra.coe_mul],
    rw ← alg_hom.map_mul,
    rw_mod_cast u_inv_val,
    simp,
  end⟩

lemma unit_gal_conj_spec (u : units RR) : gal_conj p u = unit_gal_conj p u :=
begin
  cases u,
  simp [unit_gal_conj],
end

lemma unit_lemma_val_one (u : units RR) (φ : KK →+* ℂ) :
  complex.abs (φ (u * (unit_gal_conj p u)⁻¹)) = 1 :=
begin
  rw ring_hom.map_mul,
  rw complex.abs.is_absolute_value.abv_mul,
  rw ring_hom.map_inv,
  rw is_absolute_value.abv_inv complex.abs,
  rw ← unit_gal_conj_spec,
  rw ← embedding_conj,
  simp [-embedding_conj],
end

lemma unit_lemma (u : units RR) :
  ∃ (x : units RR) (n : ℤ), element_is_real (x : KK) ∧ (u : KK) = x * (zeta p ℚ) ^ n :=
begin
  have := mem_roots_of_unity_of_abs_eq_one (u * (unit_gal_conj p u)⁻¹ : KK) _ _,
  { have : ∃ m : ℕ, u * (unit_gal_conj p u)⁻¹ = (zeta p ℚ) ^ (2 * m),
    sorry, --follows from above with some work
          -- what we have shows its +- a power of zeta
    obtain ⟨m, hm⟩ := this,
    use [u * (zeta p ℚ)⁻¹ ^ m, m],
    split,
    { rw element_is_real,
      intro φ,
      have := congr_arg (conj ∘ φ ∘ coe) hm,
      simp at this,
      simp [alg_hom.map_inv],
      rw ← coe_coe,
      rw ← coe_coe, -- TODO this is annoying
      rw (_ : (↑(zeta p ℚ ^ m)⁻¹ : KK) = (zeta p ℚ ^ m : KK)⁻¹),
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


end int_facts