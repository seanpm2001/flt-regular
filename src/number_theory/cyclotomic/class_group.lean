import number_theory.class_number.finite
import number_theory.class_number.admissible_abs

import number_theory.cyclotomic.basic
import number_theory.cyclotomic.rat

variables (n : ℕ+) [fact (((n : ℕ) : ℚ) ≠ 0)]

section finiteness

local attribute [instance] is_cyclotomic_extension.finite_dimensional

noncomputable instance class_group.fintype_of_cyclotomic_ring :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n ℚ)
  absolute_value.abs_is_admissible

end finiteness
