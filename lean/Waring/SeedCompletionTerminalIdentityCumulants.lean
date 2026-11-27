import Waring.SeedCompletionTerminalIdentityLog

/-! # Nonzero rational coefficients through the eighth weighted power sum

The finite table is verified by multiplication with the normalized sinh
series. No analytic Bernoulli-number theorem or external table is assumed.
-/

noncomputable section
namespace Waring.SeedCompletionTerminalIdentity

def cumulantCoefficient : ℕ → ℚ
  | 1 => 1/3
  | 3 => -1/45
  | 5 => 2/945
  | 7 => -1/4725
  | 9 => 2/93555
  | 11 => -1382/638512875
  | 13 => 4/18243225
  | 15 => -3617/162820783125
  | _ => 0

def cumulantSeries : PowerSeries ℚ := PowerSeries.mk cumulantCoefficient

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem unitSinh_derivative_approx :
    SeriesAgree 15 (PowerSeries.derivative ℚ unitSinh) (unitSinh*cumulantSeries) := by
  intro n hn
  interval_cases n <;>
    norm_num [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      unitSinh,cumulantSeries,cumulantCoefficient,PowerSeries.coeff_mk,Nat.factorial]

theorem unitSinh_logDerivative_approx :
    SeriesAgree 15 (logDerivative unitSinh) cumulantSeries := by
  have H := unitSinh_derivative_approx.mul (SeriesAgree.refl 15 unitSinh⁻¹)
  have he : (unitSinh*cumulantSeries)*unitSinh⁻¹=cumulantSeries := by
    calc
      _ = (unitSinh*unitSinh⁻¹)*cumulantSeries := by ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel unitSinh (by rw [unitSinh_constant]; norm_num),one_mul]
  rw [he] at H
  exact H

theorem unitSinh_logDerivative_nonzero {r : ℕ} (hr : 1≤r) (hr8 : r≤8) :
    PowerSeries.coeff (2*r-1) (logDerivative unitSinh)≠0 := by
  rw [unitSinh_logDerivative_approx (2*r-1) (by omega)]
  interval_cases r <;> norm_num [cumulantSeries,cumulantCoefficient,PowerSeries.coeff_mk]

theorem powers_eq_of_unitSymbol_agree (k : ℕ) (params other : List (ℚ×ℚ))
    {r : ℕ} (hr : 1≤r) (hr8 : r≤8)
    (h : SeriesAgree (2*r) (unitSymbol k params) (unitSymbol k other)) :
    (params.map (fun hm => (hm.1*hm.2^k)^(2*r))).sum=
      (other.map (fun hm => (hm.1*hm.2^k)^(2*r))).sum := by
  have hidx : 2*r-1+1=2*r := by omega
  have hh : SeriesAgree (2*r-1+1) (unitSymbol k params) (unitSymbol k other) := by
    rw [hidx]
    exact h
  have H := hh.logDerivative (2*r-1) le_rfl
  rw [logDerivative_unitSymbol_coeff,logDerivative_unitSymbol_coeff,hidx] at H
  exact mul_left_cancel₀ (unitSinh_logDerivative_nonzero hr hr8) H

#print axioms unitSinh_logDerivative_nonzero
#print axioms powers_eq_of_unitSymbol_agree
end Waring.SeedCompletionTerminalIdentity
