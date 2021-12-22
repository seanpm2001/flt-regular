import ready_for_mathlib.cyclotomic
import number_theory.number_field
import algebra.char_p.algebra

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

section basic

/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that `cyclotomic a A` has a root in `B` for all `a ∈ S` and that `B` is generated over `A` by the
roots of `X ^ n - 1`. -/
class is_cyclotomic_extension : Prop :=
(ex_root {a : ℕ+} (ha : a ∈ S) : ∃ r : B, aeval r (cyclotomic a A) = 0)
(adjoint_roots : ∀ (x : B), x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })

namespace is_cyclotomic_extension

lemma iff : is_cyclotomic_extension S A B ↔
 (∀ (a : ℕ+), a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
⟨λ h, ⟨h.ex_root, h.adjoint_roots⟩, λ h, ⟨h.1, h.2⟩⟩

lemma iff_adjoin_eq_top : is_cyclotomic_extension S A B ↔
 (∀ (a : ℕ+), a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
 (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } = ⊤) :=
⟨λ h, ⟨h.ex_root, algebra.eq_top_iff.2 h.adjoint_roots⟩, λ h, ⟨h.1, algebra.eq_top_iff.1 h.2⟩⟩

lemma adjoin_eq_top [h : is_cyclotomic_extension S A B] :
  adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } = ⊤ := ((iff_adjoin_eq_top _ _ _).mp h).2

lemma iff_singleton : is_cyclotomic_extension {n} A B ↔
 (∃ r : B, aeval r (cyclotomic n A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 }) :=
begin
  refine ⟨λ h, ⟨((iff _ _ _).1 h).1 n (set.mem_singleton _), by simpa using ((iff _ _ _).1 h).2⟩,
  λ h, ⟨λ a ha, _, by simpa using h.2⟩⟩,
  obtain ⟨⟨b, hb⟩, H⟩ := h,
  exact ⟨b, (set.mem_singleton_iff.1 ha).symm ▸ hb⟩
end

--Is this the best way of stating the result?
lemma empty [h : is_cyclotomic_extension ∅ A B] : (⊤ : subalgebra A B) = ⊥ :=
begin
  replace h := h.adjoint_roots,
  simp only [set.mem_empty_eq, set.set_of_false, adjoin_empty, exists_false, false_and] at h,
  exact (algebra.eq_top_iff.2 h).symm,
end

--This is a lemma, but it can be made local instance.
lemma trans (C : Type w) [comm_ring C] [algebra A C] [algebra B C]
  [is_scalar_tower A B C] [hS : is_cyclotomic_extension S A B]
  [hT : is_cyclotomic_extension T B C] : is_cyclotomic_extension (S ∪ T) A C :=
begin
  refine ⟨λ n hn, _, λ x, _⟩,
  { cases hn,
    { obtain ⟨b, hb⟩ := ((iff _ _ _).1 hS).1 n hn,
      refine ⟨algebra_map B C b, _⟩,
      replace hb := congr_arg (algebra_map B C) hb,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ring_hom.map_zero, ← eval₂_at_apply,
        eval₂_eq_eval_map, map_cyclotomic] at hb,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
    { obtain ⟨c, hc⟩ := ((iff _ _ _).1 hT).1 n hn,
      refine ⟨c, _⟩,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hc,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] } },
  { refine adjoin_induction (((iff _ _ _).1 hT).2 x) (λ c ⟨n, hn⟩, subset_adjoin
      ⟨n, or.inr hn.1, hn.2⟩) (λ b, _) (λ x y hx hy, subalgebra.add_mem _ hx hy)
      (λ x y hx hy, subalgebra.mul_mem _ hx hy),
    { let f := is_scalar_tower.to_alg_hom A B C,
      have hb : f b ∈ (adjoin A { b : B | ∃ (a : ℕ+), a ∈ S ∧ b ^ (a : ℕ) = 1 }).map f :=
        ⟨b, ((iff _ _ _).1 hS).2 b, rfl⟩,
      rw [is_scalar_tower.to_alg_hom_apply, ← adjoin_image] at hb,
      refine adjoin_mono (λ y hy, _) hb,
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy,
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← alg_hom.map_pow, hn.2, alg_hom.map_one]⟩⟩ } }
end

lemma roots_union_eq_union_roots (T : set ℕ+) :
  { b :B | ∃ (n : ℕ+), n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1 } =
  { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 } ∪
  { b : B | ∃ (n : ℕ+), n ∈ T ∧ b ^ (n : ℕ ) = 1 } :=
begin
  refine le_antisymm (λ x hx, _) (λ x hx, _),
  { obtain ⟨n, hn⟩ := hx,
    cases hn.1 with h₁ h₂,
    { left, exact ⟨n, ⟨h₁, hn.2⟩⟩ },
    { right, exact ⟨n, ⟨h₂, hn.2⟩⟩ } },
  { cases hx,
    { obtain ⟨n, hn⟩ := hx,
      exact ⟨n, ⟨or.inl hn.1, hn.2⟩⟩ },
    { obtain ⟨n, hn⟩ := hx,
      exact ⟨n, ⟨or.inr hn.1, hn.2⟩⟩ } }
end

lemma union_right [h : is_cyclotomic_extension (S ∪ T) A B]
  : is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((iff _ _ _).1 h).1 n (mem_union_right S hn),
    refine ⟨b, _⟩,
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hb,
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
  { replace h := ((iff _ _ _).1 h).2 b,
    rwa [roots_union_eq_union_roots, adjoin_union_eq_adjoin_adjoin,
      subalgebra.mem_restrict_scalars] at h }
end

lemma union_left [h : is_cyclotomic_extension T A B] (hS : S ⊆ T) :
  is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((iff _ _ _).1 h).1 n (hS hn),
    refine ⟨⟨b, subset_adjoin ⟨n, hn, _⟩⟩, _⟩,
    { rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← is_root.def] at hb,
      suffices : (X ^ (n : ℕ) - 1).is_root b,
      { simpa [sub_eq_zero] using this },
      exact hb.dvd cyclotomic.dvd_X_pow_sub_one },
      rwa [← subalgebra.coe_eq_zero, aeval_subalgebra_coe, subtype.coe_mk] },
  { convert mem_top,
    rw ← adjoin_adjoin_coe_preimage,
    simp,
    norm_cast, }
end

end is_cyclotomic_extension

end basic

namespace is_cyclotomic_extension

section fintype

lemma finite_of_singleton [is_domain B] [h : is_cyclotomic_extension {n} A B] : finite A B :=
begin
  classical,
  rw [module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2],
  refine fg_adjoin_of_finite _ (λ b hb, _),
  { simp only [mem_singleton_iff, exists_eq_left],
    have : {b : B | b ^ (n : ℕ) = 1} = (nth_roots n (1 : B)).to_finset :=
      set.ext (λ x, ⟨λ h, by simpa using h, λ h, by simpa using h⟩),
    rw [this],
    exact (nth_roots ↑n 1).to_finset.finite_to_set },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb,
    refine ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩ }
end

--This is a lemma, but it can be made local instance.
lemma finite [is_domain B] [h₁ : fintype S] [h₂ : is_cyclotomic_extension S A B] : finite A B :=
begin
  unfreezingI {revert h₂ A B},
  refine set.finite.induction_on (set.finite.intro h₁) (λ A B, _) (λ n S hn hS H A B, _),
  { introsI _ _ _ _ _,
    refine module.finite_def.2 ⟨({1} : finset B), _⟩,
    simp [← top_to_submodule, empty, to_submodule_bot] },
  { introsI _ _ _ _ h,
    haveI : is_cyclotomic_extension S A (adjoin A { b : B | ∃ (n : ℕ+),
      n ∈ S ∧ b ^ (n : ℕ) = 1 }) := union_left _ (insert n S) _ _ (subset_insert n S),
    haveI := H A (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }),
    haveI : finite (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) B,
    { rw [← union_singleton] at h,
      letI := @union_right S {n} A B _ _ _ h,
      exact finite_of_singleton n _ _ },
    exact finite.trans (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) _ }
end

lemma integral [is_domain B] [is_noetherian_ring A] [fintype S] [is_cyclotomic_extension S A B] :
  algebra.is_integral A B :=
is_integral_of_noetherian $ is_noetherian_of_fg_of_noetherian' $ (finite S A B).out

--This is a lemma, but it can be made local instance.
lemma number_field [h : number_field K] [fintype S] [is_cyclotomic_extension S K L] :
  number_field L :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map K L).injective,
  to_finite_dimensional := @finite.trans _ K L _ _ _ _
    (@algebra_rat L _ (char_zero_of_injective_algebra_map (algebra_map K L).injective)) _ _
    h.to_finite_dimensional (finite S K L) }

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
  obtain ⟨z, hz⟩ := ((iff _ _ _).1 H).1 n hS,
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
    convert @is_cyclotomic_extension.ex_root _ K L _ _ _ _ _ (mem_singleton n),
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
{ ex_root := λ a han,
  begin
    rw mem_singleton_iff at han,
    subst a,
    exact exists_root_of_splits _ (splitting_field.splits _) (degree_cyclotomic_pos n K (n.pos)).ne'
  end,
  adjoint_roots :=
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
@[nolint unused_arguments]
def cyclotomic_field.algebra_base : algebra A (cyclotomic_field n K) :=
((algebra_map K (cyclotomic_field n K)).comp (algebra_map A K)).to_algebra

local attribute [instance] cyclotomic_field.algebra_base

/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `cyclotomic_ring n A K` as
the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of `X ^ n - 1`. -/
@[derive [comm_ring, inhabited]]
def cyclotomic_ring : Type w := adjoin A { b : (cyclotomic_field n K) | b ^ (n : ℕ) = 1 }

namespace cyclotomic_ring

/-- The `A`-algebra structure on `cyclotomic_ring n A K`.
This is not an instance since it causes diamonds when `A = ℤ`. -/
def algebra_base : algebra A (cyclotomic_ring n A K) := (adjoin A _).algebra

local attribute [instance] cyclotomic_ring.algebra_base

example (R S : Type*) [comm_semiring R] [comm_semiring S] [algebra R S]
  (T : subalgebra R S) (x y : R) (h : algebra_map R T x = algebra_map R T y) :
  algebra_map R S x = algebra_map R S y :=
begin
  have miao := congr_arg ⇑(algebra_map ↥T S) h,
  rwa [←is_scalar_tower.algebra_map_apply, ←is_scalar_tower.algebra_map_apply] at miao,
end

lemma algebra_base_injective : function.injective $ algebra_map A (cyclotomic_ring n A K) :=
begin
  show function.injective (algebra_map A (adjoin A _)),
  intros a b hab,
  letI : is_scalar_tower A K (cyclotomic_field n K) :=
    is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
  replace hab := congr_arg (algebra_map ↥(adjoin A _) (cyclotomic_field n K)) hab,
  rw [← is_scalar_tower.algebra_map_apply, ← is_scalar_tower.algebra_map_apply,
    @is_scalar_tower.algebra_map_apply A K _ _ _ _ _ (cyclotomic_field.algebra n K) _ _ a,
    @is_scalar_tower.algebra_map_apply A K _ _ _ _ _ (cyclotomic_field.algebra n K) _ _ b] at hab,
  exact (is_fraction_ring.injective A K) ((algebra_map K (cyclotomic_field n K)).injective hab),
end

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

instance : is_domain (cyclotomic_ring n A K) := (adjoin A _).is_domain

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

lemma adjoin_algebra_injective :
  function.injective $ algebra_map (cyclotomic_ring n A K) (cyclotomic_field n K) :=
subtype.val_injective

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) :=
is_scalar_tower.subalgebra' _ _ _ _

lemma is_cyclotomic_extension [hn : fact (((n : ℕ) : A) ≠ 0)] :
  is_cyclotomic_extension {n} A (cyclotomic_ring n A K) :=
{ ex_root := λ a han,
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
    obtain ⟨μ, hμ⟩ := let h := (cyclotomic_field.is_cyclotomic_extension n K).ex_root
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
  adjoint_roots := λ x,
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
