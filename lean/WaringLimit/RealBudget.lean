import WaringLimit.Final
import WaringLimit.Meaning

namespace WaringLimit

/-- A checked path of arithmetic exponent pairs and Weyl intervals
whose actual logarithmic budget, including the continuous tail, is
at most 6.8720586795654902. -/
theorem limiting_real_budget :
    ∃ s x, RealPath start s x ∧
      totalCharge s x ≤ (34360293397827451 : ℝ)/5000000000000000 := by
  obtain ⟨s,x,p,h⟩ := certified_real_bound limiting_certificate
  refine ⟨s,x,p,h.trans ?_⟩
  norm_num [D]

#print axioms limiting_real_budget
end WaringLimit
