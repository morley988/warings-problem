import Waring.SeedCompletionTerminalIdentitySinh

/-! # Finite coefficient agreement and logarithmic derivatives

All operations are formal over the rationals. Agreement through degree N+1
determines the logarithmic derivative through degree N; products turn into
sums, making the weighted power sums visible without a multivariate expansion.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalIdentity

def SeriesAgree (N : ℕ) (f g : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ,n≤N → PowerSeries.coeff n f=PowerSeries.coeff n g

theorem SeriesAgree.refl (N : ℕ) (f : PowerSeries ℚ) : SeriesAgree N f f := fun _ _ => rfl

theorem SeriesAgree.mono {M N : ℕ} {f g : PowerSeries ℚ} (h : SeriesAgree N f g)
    (hMN : M≤N) : SeriesAgree M f g := fun n hn => h n (hn.trans hMN)

theorem SeriesAgree.mul {N : ℕ} {f g f' g' : PowerSeries ℚ}
    (hf : SeriesAgree N f f') (hg : SeriesAgree N g g') :
    SeriesAgree N (f*g) (f'*g') := by
  intro n hn
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega),hg ij.2 (by omega)]

theorem SeriesAgree.inv {N : ℕ} {f g : PowerSeries ℚ}
    (h : SeriesAgree N f g) : SeriesAgree N f⁻¹ g⁻¹ := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc : PowerSeries.constantCoeff f=PowerSeries.constantCoeff g := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h 0 (by omega)
    rw [PowerSeries.coeff_inv,PowerSeries.coeff_inv,hc]
    split_ifs with hn0
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      have hs := Finset.mem_antidiagonal.mp hij
      split_ifs with hj
      · rw [h ij.1 (by omega),ih ij.2 hj (by omega)]
      · rfl

def logDerivative (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.derivative ℚ f*f⁻¹

theorem SeriesAgree.logDerivative {N : ℕ} {f g : PowerSeries ℚ}
    (h : SeriesAgree (N+1) f g) : SeriesAgree N (logDerivative f) (logDerivative g) := by
  apply SeriesAgree.mul _ (h.inv.mono (by omega))
  intro n hn
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_derivative,h (n+1) (by omega)]

theorem derivative_rescale (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative ℚ (PowerSeries.rescale a f)=
      PowerSeries.C a*PowerSeries.rescale a (PowerSeries.derivative ℚ f) := by
  ext n
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_rescale,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,PowerSeries.coeff_derivative,pow_succ]
  ring

theorem inv_rescale (a : ℚ) (f : PowerSeries ℚ) (hf : PowerSeries.constantCoeff f≠0) :
    (PowerSeries.rescale a f)⁻¹=PowerSeries.rescale a f⁻¹ := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simpa using hf)).mpr
  rw [← map_mul,PowerSeries.inv_mul_cancel f hf,map_one]

theorem logDerivative_rescale_coeff (a : ℚ) (f : PowerSeries ℚ)
    (hf : PowerSeries.constantCoeff f≠0) (n : ℕ) :
    PowerSeries.coeff n (logDerivative (PowerSeries.rescale a f))=
      PowerSeries.coeff n (logDerivative f)*a^(n+1) := by
  unfold logDerivative
  rw [derivative_rescale,inv_rescale a f hf,mul_assoc,← map_mul,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale,pow_succ]
  ring

theorem logDerivative_mul (f g : PowerSeries ℚ)
    (hf : PowerSeries.constantCoeff f≠0) (hg : PowerSeries.constantCoeff g≠0) :
    logDerivative (f*g)=logDerivative f+logDerivative g := by
  unfold logDerivative
  change (f*g).derivativeFun*(f*g)⁻¹=f.derivativeFun*f⁻¹+g.derivativeFun*g⁻¹
  rw [PowerSeries.derivativeFun_mul,PowerSeries.mul_inv_rev]
  simp only [smul_eq_mul]
  calc
    _ = (f.derivativeFun*f⁻¹)*(g*g⁻¹)+(g.derivativeFun*g⁻¹)*(f*f⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel f hf,PowerSeries.mul_inv_cancel g hg]; ring

theorem logDerivative_unitSymbol_coeff (k : ℕ) (params : List (ℚ×ℚ)) (n : ℕ) :
    PowerSeries.coeff n (logDerivative (unitSymbol k params))=
      PowerSeries.coeff n (logDerivative unitSinh)*
        (params.map (fun hm => (hm.1*hm.2^k)^(n+1))).sum := by
  induction params with
  | nil => simp [unitSymbol,logDerivative]
  | cons p rest ih =>
      change PowerSeries.coeff n (logDerivative
        (PowerSeries.rescale (p.1*p.2^k) unitSinh*unitSymbol k rest))=_
      rw [logDerivative_mul _ _ (by simp [unitSinh_constant])
        (by rw [unitSymbol_constant]; norm_num),map_add,
        logDerivative_rescale_coeff _ _ (by rw [unitSinh_constant]; norm_num),ih]
      simp only [List.map_cons,List.sum_cons]
      ring

#print axioms SeriesAgree.logDerivative
#print axioms logDerivative_unitSymbol_coeff
end Waring.SeedCompletionTerminalIdentity
