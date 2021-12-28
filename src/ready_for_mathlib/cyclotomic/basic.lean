import ready_for_mathlib.cyclotomic
import number_theory.cyclotomic.basic

open polynomial algebra finite_dimensional module set

open_locale big_operators

universes u v w z

variables (n : ℕ+) (S T : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

section fact

-- TODO: eschew the need for this fact. We have that `ɸ_{np^k}(x) = ɸₙ(x^p^k)/ɸₙ(x^p^(k-1))
-- (modulo off by one errors) so we can fix all the instances to not require these requirements.
-- this may have to be made a local fact; it may be too slow. hopefully not.
instance {n : ℕ+} {α} [add_monoid α] [has_one α] [char_zero α] : fact (((n : ℕ) : α) ≠ 0) :=
⟨by exact_mod_cast n.ne_zero⟩

end fact

namespace is_cyclotomic_extension

section fintype

lemma integral [is_domain B] [is_noetherian_ring A] [fintype S] [is_cyclotomic_extension S A B] :
  algebra.is_integral A B :=
is_integral_of_noetherian $ is_noetherian_of_fg_of_noetherian' $ (finite S A B).out

--This is a lemma, but it can be made local instance.
lemma finite_dimensional [fintype S] [is_cyclotomic_extension S K L] : finite_dimensional K L :=
finite S K L

end fintype

section cyclotomic_eq_X_pow

variables {A B}

-- some weaker conditions may suffice (maybe normality of L), but this works for us
-- note that this lemma is written in this weird way so we can use it at point of use easier
lemma adjoin_roots_cyclotomic_eq_adjoin_nth_roots [decidable_eq B] [is_domain B]
  (hζ : ∃ ζ : B, is_primitive_root ζ n) :
  adjoin A ↑((map (algebra_map A B) (cyclotomic n A)).roots.to_finset) =
  adjoin A {b : B | ∃ (a : ℕ+), a ∈ ({n} : set ℕ+) ∧ b ^ (a : ℕ) = 1} :=
begin
  simp only [mem_singleton_iff, exists_eq_left, map_cyclotomic],
  refine le_antisymm (adjoin_mono (λ x hx, _)) (adjoin_le (λ x hx, _)),
  { simp only [multiset.mem_to_finset, finset.mem_coe,
               map_cyclotomic, mem_roots (cyclotomic_ne_zero n B)] at hx,
    simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq],
    rw is_root_of_unity_iff n.pos,
    exact ⟨n, nat.mem_divisors_self n n.ne_zero, hx⟩ },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx,
    obtain ⟨ζ, hζ⟩ := hζ,
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos,
    refine set_like.mem_coe.2 (subalgebra.pow_mem _ (subset_adjoin _) _),
    rwa [finset.mem_coe, multiset.mem_to_finset, mem_roots $ cyclotomic_ne_zero n B],
    exact is_root_cyclotomic n.pos hζ }
end

lemma adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic [decidable_eq B] [is_domain B]
  (ζ : B) (hζ : is_primitive_root ζ n) :
  adjoin A (((map (algebra_map A B) (cyclotomic n A)).roots.to_finset) : set B) = adjoin A ({ζ}) :=
begin
  refine le_antisymm (adjoin_le (λ x hx, _)) (adjoin_mono (λ x hx, _)),
  { suffices hx : x ^ ↑n = 1,
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos,
    exact set_like.mem_coe.2 (subalgebra.pow_mem _ (subset_adjoin $ mem_singleton ζ) _),
    rw is_root_of_unity_iff n.pos,
    refine ⟨n, nat.mem_divisors_self n n.ne_zero, _⟩,
    rwa [finset.mem_coe, multiset.mem_to_finset,
         map_cyclotomic, mem_roots $ cyclotomic_ne_zero n B] at hx },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx,
    simpa only [hx, multiset.mem_to_finset, finset.mem_coe, map_cyclotomic,
                mem_roots (cyclotomic_ne_zero n B)] using is_root_cyclotomic n.pos hζ }
end

lemma adjoin_primitive_root_eq_top [is_domain B] [h : is_cyclotomic_extension {n} A B]
  (ζ : B) (hζ : is_primitive_root ζ n) : adjoin A ({ζ} : set B) = ⊤ :=
begin
  classical,
  rw ←adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n ζ hζ,
  rw adjoin_roots_cyclotomic_eq_adjoin_nth_roots n ⟨ζ, hζ⟩,
  exact ((iff_adjoin_eq_top {n} A B).mp h).2,
end

end cyclotomic_eq_X_pow

section field

lemma splits_X_pow_sub_one [H : is_cyclotomic_extension S K L] (hS : n ∈ S) (hn : (n : K) ≠ 0) :
  splits (algebra_map K L) (X ^ (n : ℕ) - 1) :=
begin
  rw [← splits_id_iff_splits, polynomial.map_sub, polynomial.map_one,
      polynomial.map_pow, polynomial.map_X],
  obtain ⟨z, hz⟩ := ((is_cyclotomic_extension_iff _ _ _).1 H).1 hS,
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hz,
  replace hn : ((n : ℕ) : L) ≠ 0,
  { intro h,
    rw [← ring_hom.map_nat_cast (algebra_map K L)] at h,
    have := (ring_hom.injective_iff _).1 (algebra_map K L).injective _ h,
    norm_cast at this },
  exact X_pow_sub_one_splits ((is_root_cyclotomic_iff hn).1 hz),
end

lemma splits_cyclotomic [is_cyclotomic_extension S K L] (hS : n ∈ S) (hn : (n : K) ≠ 0) :
  splits (algebra_map K L) (cyclotomic n K) :=
begin
  refine splits_of_splits_of_dvd _ (X_pow_sub_C_ne_zero n.pos _)
    (splits_X_pow_sub_one n S K L hS hn) _,
  use (∏ (i : ℕ) in (n : ℕ).proper_divisors, polynomial.cyclotomic i K),
  rw [(eq_cyclotomic_iff n.pos _).1 rfl, ring_hom.map_one],
end

section singleton

variables [is_cyclotomic_extension {n} K L]

lemma splitting_field_X_pow_sub_one (hn : (n : K) ≠ 0) :
  is_splitting_field K L (X ^ (n : ℕ) - 1) :=
{ splits := splits_X_pow_sub_one n {n} K L (mem_singleton n) hn,
  adjoin_roots :=
  begin
    rw [← ((iff_adjoin_eq_top {n} K L).1 infer_instance).2],
    congr,
    refine set.ext (λ x, _),
    simp only [polynomial.map_pow, mem_singleton_iff, multiset.mem_to_finset, exists_eq_left,
      mem_set_of_eq, polynomial.map_X, polynomial.map_one, finset.mem_coe, polynomial.map_sub],
    rwa [← ring_hom.map_one C, mem_roots (@X_pow_sub_C_ne_zero _ (field.to_nontrivial L) _ _
      n.pos _), is_root.def, eval_sub, eval_pow, eval_C, eval_X, sub_eq_zero]
  end }

lemma splitting_field_cyclotomic (hn : ((n : ℕ) : K) ≠ 0) :
  is_splitting_field K L (cyclotomic n K) :=
{ splits := splits_cyclotomic n {n} K L (mem_singleton n) hn,
  adjoin_roots :=
  begin
    replace hn : ((n : ℕ) : L) ≠ 0,
    { rw [←(algebra_map K L).map_nat_cast, algebra_map_eq_smul_one, smul_ne_zero_iff_ne' hn],
      exact one_ne_zero },
    rw [← ((iff_adjoin_eq_top {n} K L).1 infer_instance).2],
    letI := classical.dec_eq L,
    refine adjoin_roots_cyclotomic_eq_adjoin_nth_roots n _,
    convert @is_cyclotomic_extension.exists_root _ K L _ _ _ _ _ (mem_singleton n),
    ext ζ,
    rw [←is_root_cyclotomic_iff hn, is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  end }

end singleton

end field

end is_cyclotomic_extension

section cyclotomic_field

/-- Given `n : ℕ+` and a field `K`, we define `cyclotomic n K` as the splitting field of
`cyclotomic n K`. -/
@[derive [field, algebra K, inhabited]]
def cyclotomic_field : Type w := (cyclotomic n K).splitting_field

namespace cyclotomic_field

instance is_cyclotomic_extension [hn : fact (((n : ℕ) : K) ≠ 0)] :
  is_cyclotomic_extension {n} K (cyclotomic_field n K) :=
{ exists_root := λ a han,
  begin
    rw mem_singleton_iff at han,
    subst a,
    exact exists_root_of_splits _ (splitting_field.splits _) (degree_cyclotomic_pos n K (n.pos)).ne'
  end,
  adjoin_roots :=
  begin
    replace hn : ((n : ℕ) : cyclotomic_field n K) ≠ 0,
    { rw [←(algebra_map K (cyclotomic_field n K)).map_nat_cast, algebra_map_eq_smul_one,
           smul_ne_zero_iff_ne' hn.out],
      exact one_ne_zero },
    rw [←algebra.eq_top_iff, ←splitting_field.adjoin_roots, eq_comm],
    letI := classical.dec_eq (cyclotomic_field n K),
    refine is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots n _,
    convert exists_root_of_splits _ (splitting_field.splits (cyclotomic n K))
              (degree_cyclotomic_pos n _ n.pos).ne',
    ext ζ,
    rw [←is_root_cyclotomic_iff hn, is_root.def, eval₂_eq_eval_map, map_cyclotomic],
    refl
  end }

end cyclotomic_field

end cyclotomic_field

section is_domain

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

section cyclotomic_ring

/-- If `K` is the fraction field of `A`, the `A`-algebra structure on `cyclotomic_field n K`.
This is not an instance since it causes diamonds when `A = ℤ`. -/
@[nolint unused_arguments] -- Eric: why shouldn't we make this a more general `def`?
def cyclotomic_field.algebra_base : algebra A (cyclotomic_field n K) :=
((algebra_map K (cyclotomic_field n K)).comp (algebra_map A K)).to_algebra

local attribute [instance] cyclotomic_field.algebra_base

instance cyclotomic_field.no_zero_smul_divisors : no_zero_smul_divisors A (cyclotomic_field n K) :=
no_zero_smul_divisors.of_algebra_map_injective $ function.injective.comp
(no_zero_smul_divisors.algebra_map_injective _ _) $ is_fraction_ring.injective A K

/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `cyclotomic_ring n A K` as
the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of `X ^ n - 1`. -/
-- with `no_zero_smul_divisors A (cyclotomic_field n K)` (which should be fine)
@[derive [comm_ring, is_domain, inhabited]]
def cyclotomic_ring : Type w := adjoin A { b : (cyclotomic_field n K) | b ^ (n : ℕ) = 1 }

namespace cyclotomic_ring

/-- The `A`-algebra structure on `cyclotomic_ring n A K`.
This is not an instance since it causes diamonds when `A = ℤ`. -/
def algebra_base : algebra A (cyclotomic_ring n A K) := (adjoin A _).algebra
-- todo: let `derive` do this. current issue: Lean doesn't let you be a grown-up and remove attrs

local attribute [instance] cyclotomic_ring.algebra_base

instance : no_zero_smul_divisors A (cyclotomic_ring n A K) := (adjoin A _).no_zero_smul_divisors_bot

example (R S : Type*) [comm_semiring R] [comm_semiring S] [algebra R S]
  (T : subalgebra R S) (x y : R) (h : algebra_map R T x = algebra_map R T y) :
  algebra_map R S x = algebra_map R S y :=
begin
  have miao := congr_arg ⇑(algebra_map ↥T S) h,
  rwa [←is_scalar_tower.algebra_map_apply, ←is_scalar_tower.algebra_map_apply] at miao,
end

lemma algebra_base_injective : function.injective $ algebra_map A (cyclotomic_ring n A K) :=
no_zero_smul_divisors.algebra_map_injective _ _ -- ta da!
-- todo: can we carry this instance to more general cases? or do we have to work harder
-- for injective algebra maps in cyclotomic extensions?

lemma eq_adjoin_single (μ : (cyclotomic_field n K))
  (h : μ ∈ primitive_roots n ((cyclotomic_field n K))) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) :=
begin
  letI := classical.prop_decidable,
  rw [mem_primitive_roots n.pos] at h,
  rw [←is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n μ h,
      is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots n ⟨μ, h⟩],
  simp [cyclotomic_ring]
end

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

lemma adjoin_algebra_injective :
  function.injective $ algebra_map (cyclotomic_ring n A K) (cyclotomic_field n K) :=
subtype.val_injective

instance : no_zero_smul_divisors (cyclotomic_ring n A K) (cyclotomic_field n K) :=
no_zero_smul_divisors.of_algebra_map_injective (adjoin_algebra_injective n A K)

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) :=
is_scalar_tower.subalgebra' _ _ _ _

lemma is_cyclotomic_extension [hn : fact (((n : ℕ) : A) ≠ 0)] :
  is_cyclotomic_extension {n} A (cyclotomic_ring n A K) :=
{ exists_root := λ a han,
  begin
    rw mem_singleton_iff at han,
    subst a,
    haveI : fact (((n : ℕ) : K) ≠ 0),
    { apply fact.mk,
      replace hn := hn.1,
      contrapose! hn,
      apply is_fraction_ring.injective A K,
      rwa [ring_hom.map_nat_cast, ring_hom.map_zero] },
    have ham : function.injective (algebra_map (cyclotomic_ring n A K) (cyclotomic_field n K)),
    { exact subtype.val_injective },
    obtain ⟨μ, hμ⟩ := let h := (cyclotomic_field.is_cyclotomic_extension n K).exists_root
                      in h $ mem_singleton n,
    refine ⟨⟨μ, subset_adjoin _⟩, _⟩,
    { apply (is_root_of_unity_iff n.pos (cyclotomic_field n K)).mpr,
      refine ⟨n, nat.mem_divisors_self _ n.ne_zero, _⟩,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hμ },
    -- why does this duplicate hμ? I can't even remove it with `dedup`...
    simp_rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ←is_root.def] at hμ ⊢,
    have hnr : ((n : ℕ) : cyclotomic_ring n A K) ≠ 0,
    { replace hn := hn.1,
      contrapose! hn,
      apply algebra_base_injective n A K,
      rwa [ring_hom.map_nat_cast, ring_hom.map_zero] },
    have hnf : ((n : ℕ) : cyclotomic_field n K) ≠ 0,
    { contrapose! hnr,
      apply adjoin_algebra_injective,
      rwa [ring_hom.map_nat_cast, ring_hom.map_zero] },
    rw is_root_cyclotomic_iff hnr,
    rw is_root_cyclotomic_iff hnf at hμ,
    rwa ←is_primitive_root.map_iff_of_injective (adjoin_algebra_injective n A K)
  end,
  adjoin_roots := λ x,
  begin
    refine adjoin_induction' (λ y hy, _) (λ a, _) (λ y z hy hz, _) (λ y z hy hz, _) x,
    { refine subset_adjoin _,
      simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq],
      rwa [← subalgebra.coe_eq_one, subalgebra.coe_pow, subtype.coe_mk] },
    { exact subalgebra.algebra_map_mem _ a },
    { exact subalgebra.add_mem _ hy hz },
    { exact subalgebra.mul_mem _ hy hz },
  end }

instance [hn : fact (((n : ℕ) : K) ≠ 0)] :
  is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) :=
{ map_units := λ ⟨x, hx⟩, begin
    rw is_unit_iff_ne_zero,
    apply ring_hom.map_ne_zero_of_mem_non_zero_divisors,
    apply adjoin_algebra_injective,
    exact hx
  end,
  surj := λ x,
  begin
    refine algebra.adjoin_induction (((is_cyclotomic_extension.iff_singleton n K _).1
      (cyclotomic_field.is_cyclotomic_extension n K)).2 x) (λ y hy, _) (λ k, _) _ _,
    { exact ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, by simpa⟩ },
    { have : is_localization (non_zero_divisors A) K := infer_instance,
      replace := this.surj,
      obtain ⟨⟨z, w⟩, hw⟩ := this k,
      refine ⟨⟨algebra_map A _ z, algebra_map A _ w, ring_hom.map_mem_non_zero_divisors _
        (algebra_base_injective n A K) w.2⟩, _⟩,
      letI : is_scalar_tower A K (cyclotomic_field n K) :=
        is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
      rw [set_like.coe_mk, ← is_scalar_tower.algebra_map_apply,
        ← is_scalar_tower.algebra_map_apply, @is_scalar_tower.algebra_map_apply A K _ _ _ _ _
        (_root_.cyclotomic_field.algebra n K) _ _ w, ← ring_hom.map_mul, hw,
        ← is_scalar_tower.algebra_map_apply] },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, hb],
      simp },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, mul_comm ((algebra_map _ _) ↑a.2), mul_assoc,
        ← mul_assoc z, hb, ← mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, ha],
      simp }
  end,
  eq_iff_exists := λ x y, ⟨λ h, ⟨1, by rw adjoin_algebra_injective n A K h⟩,
    λ ⟨c, hc⟩, by rw mul_right_cancel₀ (non_zero_divisors.ne_zero c.prop) hc⟩ }

end cyclotomic_ring

end cyclotomic_ring

end is_domain
