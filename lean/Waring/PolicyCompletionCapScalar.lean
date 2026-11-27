import Waring.PolicyCompletionAllocationScale
import Waring.CartesianFloorScales

/-! # Ambient powers after the literal integer-cutoff cap

The scale comparison is uniform even when a resource saving is negative.
No saving is changed: only a fixed multiplicative constant is introduced.
-/
noncomputable section
namespace Waring.PolicyCompletionCapScalar
open PolicyCompletionAllocationScale

theorem fixed_dilation_cutoff {D P : ℝ} (hD : 1≤D) (hP : 2≤P) :
    0<⌊D*P⌋₊ ∧ (⌊D*P⌋₊:ℝ)≤D*P ∧
      P≤(2*D)*(⌊D*P⌋₊:ℝ) ∧ (⌊D*P⌋₊:ℝ)≤(2*D)*P := by
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hPp : 0<P := by linarith
  have hDP : 2≤D*P := by nlinarith
  have hf := CartesianFloorScales.half_le_floor hDP
  have hu := Nat.floor_le (mul_nonneg hDp.le hPp.le)
  refine ⟨Nat.floor_pos.mpr (by linarith),hu,?_,?_⟩
  · nlinarith [show (0:ℝ)≤⌊D*P⌋₊ by positivity]
  · nlinarith

theorem root_prefactor_bound {A B E T P δ d : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hE : 0≤E) (hT : 0≤T)
    (hP : 1≤P) (hδ : 0≤δ) (hd : 0<d) (hET : E≤T*P^δ) :
    (A+B*E)^(1/d)≤(A+B*T)^(1/d)*P^(δ/d) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hp := Real.one_le_rpow hP hδ
  have hh : A+B*E≤(A+B*T)*P^δ := by
    nlinarith [mul_le_mul_of_nonneg_left hET hB,mul_le_mul_of_nonneg_left hp hA]
  calc
    _ ≤ ((A+B*T)*P^δ)^(1/d) := Real.rpow_le_rpow (by positivity) hh (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤A+B*T) (Real.rpow_nonneg hPp.le _),
        ← Real.rpow_mul hPp.le]
      congr 1
      congr 1
      ring

/-- The root exponent, diagonal cap, and ambient scale all retain their
original values after replacing the actual center cutoff by P. -/
theorem scalar_scaled_cap {F A B E T U P N K S Bsave δ d a : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hE : 0≤E) (hT : 0≤T) (hU : 0≤U)
    (hP : 1≤P) (hN : 0<N) (hK : 1≤K) (hPN : P≤K*N) (hNP : N≤K*P)
    (hBsave : 0≤Bsave) (hS : |S|≤Bsave)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hd : 1≤d)
    (hET : E≤T*P^δ)
    (hcap : F≤(A+B*E)^(1/d)*(U*P^a)*N^(δ/d-min 1 S/d)) :
    F≤((A+B*T)^(1/d)*U*K^(Bsave+2))*P^(a+2*δ/d-min 1 S/d) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hdpos : 0<d := zero_lt_one.trans_le hd
  have hr := root_prefactor_bound hA hB hE hT hP hδ hdpos hET
  have he := capped_exponent_abs hBsave hS hδ hδ1 hd
  have hc := rpow_comparable hPp hN hK hNP hPN he
  calc
    F ≤ (A+B*E)^(1/d)*(U*P^a)*N^(δ/d-min 1 S/d) := hcap
    _ ≤ ((A+B*T)^(1/d)*P^(δ/d))*(U*P^a)*
        (K^(Bsave+2)*P^(δ/d-min 1 S/d)) := by
      gcongr
    _ = ((A+B*T)^(1/d)*U*K^(Bsave+2))*
        (P^(δ/d)*P^a*P^(δ/d-min 1 S/d)) := by ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_add hPp,← Real.rpow_add hPp]
      congr 1
      ring

#print axioms fixed_dilation_cutoff
#print axioms scalar_scaled_cap
end Waring.PolicyCompletionCapScalar
