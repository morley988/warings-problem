import Waring.RestrictedSmoothUnoptimized

/-! # Exact scale arithmetic for the restricted smooth mean -/

noncomputable section
namespace Waring.RestrictedSmoothArcs

def optimizedScale (P T R : ℝ) : ℝ := P/(T*R)

theorem optimizedScale_mul {P T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    optimizedScale P T R*R=P/T := by
  unfold optimizedScale
  field_simp

theorem optimizedScale_bounds {P T R : ℝ} (hP : 1 ≤ P) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hsmall : T*R^2 ≤ P) :
    R ≤ optimizedScale P T R ∧ 1 ≤ optimizedScale P T R ∧ optimizedScale P T R*R ≤ P := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRM : R ≤ optimizedScale P T R := by
    apply (le_div_iff₀ (mul_pos hTp hRp)).mpr
    nlinarith [hsmall]
  refine ⟨hRM,hR.trans hRM,?_⟩
  rw [optimizedScale_mul hTp hRp]
  exact div_le_self (zero_le_one.trans hP) hT

theorem optimizedScale_separation (k : ℕ) {P Q T R m : ℝ}
    (hP : 0 < P) (hT : 0 < T) (hR : 0 < R) (hm : 0 ≤ m)
    (hTpow : T^k=4*Q^2) (hmM : m ≤ optimizedScale P T R*R) :
    4*Q*(m^k*(Q/P^k)) ≤ 1 := by
  rw [optimizedScale_mul hT hR] at hmM
  have hmul : m*T ≤ P := (le_div_iff₀ hT).mp hmM
  have hpow : (m*T)^k ≤ P^k := pow_le_pow_left₀ (mul_nonneg hm hT.le) hmul k
  calc
    _ = (T^k*m^k)/P^k := by rw [hTpow]; ring
    _ ≤ 1 := (div_le_one (pow_pos hP k)).mpr (by simpa only [mul_pow,mul_comm] using hpow)

theorem optimizedScale_small_term (k s : ℕ) {P Q T R lam : ℝ}
    (hP : 1 ≤ P) (hT : 1 ≤ T) (hR : 1 ≤ R) (hlam : 1 ≤ lam)
    (hTpow : T^k=4*Q^2) :
    Q*(Q/P^k)*(optimizedScale P T R)^s ≤
      P^((s : ℝ)-(k : ℝ))*T^(lam-(s : ℝ)+(k : ℝ)) := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQT : Q^2 ≤ T^s*T^(lam-(s : ℝ)+(k : ℝ)) := by
    calc
      Q^2 ≤ T^k := by rw [hTpow]; nlinarith [sq_nonneg Q]
      _ = T^((k : ℝ)) := (Real.rpow_natCast T k).symm
      _ ≤ T^((s : ℝ)+(lam-(s : ℝ)+(k : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = _ := by rw [Real.rpow_add hTp,Real.rpow_natCast]
  have hratio : Q^2/(T^s*R^s) ≤ T^(lam-(s : ℝ)+(k : ℝ)) := by
    apply (div_le_iff₀ (mul_pos (pow_pos hTp s) (pow_pos hRp s))).mpr
    calc
      _ ≤ T^s*T^(lam-(s : ℝ)+(k : ℝ)) := hQT
      _ ≤ (T^s*T^(lam-(s : ℝ)+(k : ℝ)))*R^s :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hR)
      _ = _ := by ring
  calc
    _ = (P^s/P^k)*(Q^2/(T^s*R^s)) := by
      unfold optimizedScale
      rw [div_pow,mul_pow]
      field_simp <;> ring
    _ ≤ (P^s/P^k)*T^(lam-(s : ℝ)+(k : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by rw [Real.rpow_sub hPp,Real.rpow_natCast,Real.rpow_natCast]

theorem optimizedScale_main_term (k s : ℕ) {P T R lam : ℝ}
    (hP : 0 < P) (hT : 0 < T) (hR : 0 < R) :
    (optimizedScale P T R*R)^s*(P/optimizedScale P T R)^lam/(optimizedScale P T R)^k =
      P^((s : ℝ)-(k : ℝ))*T^(lam-(s : ℝ)+(k : ℝ))*R^((s : ℝ)+(lam-(s : ℝ)+(k : ℝ))) := by
  have hPM : P/optimizedScale P T R=T*R := by unfold optimizedScale; field_simp
  rw [optimizedScale_mul hT hR,hPM,
    show lam-(s : ℝ)+(k : ℝ)=lam+(k : ℝ)-(s : ℝ) by ring,
    show (s : ℝ)+(lam+(k : ℝ)-(s : ℝ))=lam+(k : ℝ) by ring,
    Real.rpow_sub hP,Real.rpow_sub hT,Real.rpow_add hT,Real.rpow_add hR,
    Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast,
    Real.mul_rpow hT.le hR.le]
  simp only [Real.rpow_natCast]
  unfold optimizedScale
  rw [div_pow,div_pow,mul_pow]
  field_simp <;> ring

theorem optimizedScale_total (k s : ℕ) {P Q T R lam L : ℝ}
    (hP : 1 ≤ P) (hT : 1 ≤ T) (hR : 1 ≤ R) (hlam : 1 ≤ lam)
    (hTpow : T^k=4*Q^2) (hL0 : 0 ≤ L) (hL : (s : ℝ)+(lam-(s : ℝ)+(k : ℝ)) ≤ L) :
    Q*(Q/P^k)*(optimizedScale P T R)^s+
      (optimizedScale P T R*R)^s*(P/optimizedScale P T R)^lam/(optimizedScale P T R)^k ≤
        2*P^((s : ℝ)-(k : ℝ))*T^(lam-(s : ℝ)+(k : ℝ))*R^L := by
  have hPp := zero_lt_one.trans_le hP
  have hTp := zero_lt_one.trans_le hT
  have hRp := zero_lt_one.trans_le hR
  have hbase : 0 ≤ P^((s : ℝ)-(k : ℝ))*T^(lam-(s : ℝ)+(k : ℝ)) := by positivity
  rw [optimizedScale_main_term k s hPp hTp hRp]
  have h1 := optimizedScale_small_term k s hP hT hR hlam hTpow
  have h2 := Real.rpow_le_rpow_of_exponent_le hR hL
  have h3 := Real.one_le_rpow hR hL0
  nlinarith [mul_le_mul_of_nonneg_left h2 hbase,
    le_mul_of_one_le_right hbase h3]

#print axioms optimizedScale_total
end Waring.RestrictedSmoothArcs
