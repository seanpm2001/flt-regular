import ring_theory.polynomial.cyclotomic
import number_theory.number_field

open polynomial algebra finite_dimensional

universes u v w z

variables (n : ℕ+) (S : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

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

lemma iff_singleton : is_cyclotomic_extension {n} A B ↔
 (∃ r : B, aeval r (cyclotomic n A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 }) :=
begin
  refine ⟨λ h, ⟨((iff _ _ _).1 h).1 n (set.mem_singleton _), by simpa using ((iff _ _ _).1 h).2⟩,
  λ h, ⟨λ a ha, _, by simpa using h.2⟩⟩,
  obtain ⟨⟨b, hb⟩, H⟩ := h,
  exact ⟨b, (set.mem_singleton_iff.1 ha).symm ▸ hb⟩
end

end is_cyclotomic_extension

--TODO: add equivalent definitions

end basic

section field

section fintype

variables [h₁ : fintype S] [h₂ : is_cyclotomic_extension S K L]
include h₁ h₂

namespace is_cyclotomic_extension

@[priority 100] -- see Note [lower instance priority]
instance finite_dimensional : finite_dimensional K L := sorry

lemma number_field [number_field K] : number_field L := sorry

end is_cyclotomic_extension

end fintype

section singleton

variables [is_cyclotomic_extension {n} K L]

namespace is_cyclotomic_extension

instance splitting_field_X_pow_sub_one : is_splitting_field K L (X ^ (n : ℕ) - 1) := sorry

instance splitting_field_cyclotomic : is_splitting_field K L (cyclotomic n K) := sorry

end is_cyclotomic_extension

end singleton

section cyclotomic_field

/-- Given `n : ℕ+` and a field `K`, we define `cyclotomic n K` as the splitting field of
`cyclotomic n K`. -/
@[derive [field, algebra K, inhabited]]
def cyclotomic_field : Type w := (cyclotomic n K).splitting_field

namespace cyclotomic_field

instance is_cyclotomic_extension : is_cyclotomic_extension {n} K (cyclotomic_field n K) := sorry

end cyclotomic_field

end cyclotomic_field

end field

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

lemma eq_adjoin_single (μ : (cyclotomic_field n K))
  (h : μ ∈ primitive_roots n ((cyclotomic_field n K))) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) := sorry

instance : is_domain (cyclotomic_ring n A K) := sorry

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) := sorry

lemma is_cyclotomic_extension : is_cyclotomic_extension {n} A (cyclotomic_ring n A K) := sorry

instance : is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) := sorry

end cyclotomic_ring

end cyclotomic_ring

end is_domain
