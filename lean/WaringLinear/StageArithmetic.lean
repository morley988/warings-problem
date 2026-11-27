import WaringLinear.ShortenedMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The three normalized powers in the conductor update -/

namespace WaringLinear
open scoped BigOperators
noncomputable section

theorem good_stage_power {ι : Type*} [Fintype ι] (m I : ι → ℝ)
    (X p k D θ B C : ℝ) (hX : 0<X) (hD : 0≤D) (hB : 0≤B) (hC : 0≤C)
    (hm : ∀ i,0<m i) (hsize : ∀ i,X^θ≤m i)
    (hmass : (∑ i,(m i)⁻¹)≤1)
    (hI : ∀ i,I i≤(m i)^p*C*(X/m i)^(p-k+D)) :
    (∑ i,4*(m i)⁻¹*(B*X^2/(m i)^k)*I i) ≤
      4*B*C*X^(p+2-k+(1-θ)*D) := by
  have H := shorten_child_excess m X (p-k) D θ hX hD hm hsize hmass
  calc
    _ ≤ ∑ i,4*(m i)⁻¹*(B*X^2/(m i)^k)*((m i)^p*C*(X/m i)^(p-k+D)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left (hI i)
      have hm' := hm i
      positivity
    _ = (4*B*C*X^2)*∑ i,(m i)^(p-k-1)*(X/m i)^(p-k+D) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_sub (hm i),Real.rpow_sub (hm i),Real.rpow_one]
      ring
    _ ≤ (4*B*C*X^2)*X^(p-k+(1-θ)*D) := mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by
      rw [show p+2-k+(1-θ)*D=(2:ℝ)+(p-k+(1-θ)*D) by ring,
        Real.rpow_add hX (2:ℝ) (p-k+(1-θ)*D),Real.rpow_two]
      ring

theorem exceptional_stage_power {κ : Type*} [Fintype κ] (d J : κ → ℝ)
    (X t Z C : ℝ) (hX : 0<X) (hC : 0≤C) (hd : ∀ j,0<d j)
    (hZ : (∑ j,((d j)^t)⁻¹)≤Z) (hJ : ∀ j,J j≤C*(X/d j)^t) :
    (∑ j,J j)≤C*Z*X^t := by
  calc
    _ ≤ ∑ j,C*(X/d j)^t := Finset.sum_le_sum (fun j _ => hJ j)
    _ = (C*X^t)* ∑ j,((d j)^t)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.div_rpow hX.le (hd j).le]
      ring
    _ ≤ (C*X^t)*Z := mul_le_mul_of_nonneg_left hZ (mul_nonneg hC (Real.rpow_nonneg hX.le t))
    _ = _ := by ring

theorem low_stage_power (I X p k u z E C : ℝ) (hX : 0<X)
    (hI : I ≤ C*X^(u-k+E)) :
    X^((1-z)*(p+2-u))*I ≤ C*X^(p+2-k+E-(p+2-u)*z) := by
  apply (mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg hX.le _)).trans
  rw [show p+2-k+E-(p+2-u)*z=(1-z)*(p+2-u)+(u-k+E) by ring,Real.rpow_add hX ((1-z)*(p+2-u)) (u-k+E)]
  exact le_of_eq (by ring)

/-- Combining the contracted and low-spectrum branches with the exceptional
same-order children yields the exact allowed new excess. -/
theorem combine_stage_powers (I X p k u z E D θ G L P A : ℝ)
    (hX : 1≤X) (hG : 0≤G) (hL : 0≤L)
    (hA₁ : (1-θ)*D≤A) (hA₂ : E-(p+2-u)*z≤A)
    (hI : I ≤ L*X^(p+2-k+E-(p+2-u)*z)+
               G*X^(p+2-k+(1-θ)*D)+P*X^(p+2-k+A)) :
    I ≤ (L+G+P)*X^(p+2-k+A) := by
  have h1 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX
    (by linarith : p+2-k+E-(p+2-u)*z≤p+2-k+A)) hL
  have h2 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX
    (by linarith : p+2-k+(1-θ)*D≤p+2-k+A)) hG
  rw [add_mul,add_mul]
  linarith only [hI,h1,h2]

end
#print axioms good_stage_power
#print axioms exceptional_stage_power
#print axioms combine_stage_powers
end WaringLinear
