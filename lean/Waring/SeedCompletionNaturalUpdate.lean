import Waring.SeedCompletionNaturalScales

/-! # Actual all-depth source recurrence at the precise exponent level -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open PolicyCompletionMajorPowerRanges SeedCompletionSourceBounds SmoothMoments

theorem powerBoxCross_power {k j s u t : ℕ} {D lam κ : ℝ} (φ : Fin j → ℝ)
    (hD : 1≤D) (hq0 : 0≤1-total φ) (hq1 : 1-total φ≤1)
    (hsplit : u+t=2*s) (hF : SourcePowerBound (powerBoxMixed k u D φ) κ)
    (hU : AdmissibleExponent k (2*t) lam) :
    SourcePowerBound (powerBoxCross k s D φ) ((κ+(1-total φ)*lam)/2) := by
  have hUs := admissible_shorter_source_bound hU hD hq0 hq1
  have H := (hF.rpow (by norm_num : (0:ℝ)≤1/2)
    (fun P R _ _ => boxMixedMoment_nonneg ..)).mul
    (hUs.rpow (by norm_num : (0:ℝ)≤1/2) (fun P R _ _ => smoothMoment_nonneg ..))
  have H' : SourcePowerBound
      (fun P R => (powerBoxMixed k u D φ P R)^(1/2:ℝ)*
        (smoothMoment k (2*t) (D*P^(1-total φ)) R)^(1/2:ℝ))
      ((κ+(1-total φ)*lam)/2) := by
    convert H using 1 <;> ring
  apply H'.of_le (fun P R _ _ => boxCrossMoment_nonneg ..)
  intro P R hP hR
  exact boxCrossMoment_le_mixed k s u t hsplit (D*P) P R _ _

theorem powerBoxMixed_power {k j s : ℕ} {D ψ lam χ : ℝ} (φ : Fin j → ℝ)
    (hk : 2≤k) (hjk : j<k) (hD : 1≤D)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hψ : 0≤ψ) (hψk : (k:ℝ)*ψ≤1) (hsum : total φ+ψ≤1)
    (hU : AdmissibleExponent k (2*(s+1)) lam)
    (hX : SourcePowerBound (powerBoxCross k (s+1) (2*D) (Fin.cons ψ φ)) χ) :
    SourcePowerBound (powerBoxMixed k (s+1) D φ)
      (parameterExponent k φ+(2*((s:ℝ)+1)-1)*ψ+
        max (parameterExponent k φ+1+ψ+(1-total φ-ψ)*lam) χ) := by
  let a := parameterExponent k φ
  let q := 1-total φ-ψ
  let n := 2*(s+1)-1
  let C := powerBoxCard k D φ
  let V := fun P R : ℝ => P^ψ*R
  let Z := fun P (_ : ℝ) => ((naturalCenters (D*P)).card:ℝ)
  let U := fun P R : ℝ => smoothMoment k (2*(s+1)) (D*P^q) R
  let X := powerBoxCross k (s+1) (2*D) (Fin.cons ψ φ)
  let G := fun P R : ℝ => C P R*(V P R)^n*(C P R*V P R*Z P R*U P R+X P R)
  have htotal : 0≤total φ := Finset.sum_nonneg (fun i _ => hφ i)
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hq1 : q≤1 := by dsimp [q]; linarith
  have hC : SourcePowerBound C a := powerBoxCard_power hD φ hφ hshift
  have hV : SourcePowerBound V ψ := by
    simpa only [add_zero] using (ambient_power ψ).mul smoothness_power
  have hZ : SourcePowerBound Z 1 := powerCentersCard_power hD
  have hUs : SourcePowerBound U (q*lam) := admissible_shorter_source_bound hU hD hq0 hq1
  have hdiag : SourcePowerBound (fun P R => C P R*V P R*Z P R*U P R)
      (a+1+ψ+q*lam) := by
    convert ((hC.mul hV).mul hZ).mul hUs using 1 <;> ring
  have hG := (hC.mul (hV.natPow n)).mul (hdiag.add hX)
  have hn : (n:ℝ)=2*((s:ℝ)+1)-1 := by
    dsimp [n]
    rw [show 2*(s+1)-1=2*s+1 by omega]
    push_cast
    ring
  have hG' : SourcePowerBound G
      (parameterExponent k φ+(2*((s:ℝ)+1)-1)*ψ+
        max (parameterExponent k φ+1+ψ+(1-total φ-ψ)*lam) χ) := by
    convert hG using 1
    dsimp only [a,q]
    rw [hn]
    ring
  apply hG'.of_epsilon_domination
  intro δ hδ
  refine ⟨1/2,by norm_num,?_⟩
  intro η hη hηle
  obtain ⟨K,hK,L₀,hL₀,hrec⟩ := box_recurrence k j s hjk (half_pos hη) hδ
  obtain ⟨P₂,hP₂,hRtwo⟩ := fixed_power_eventually_two hη
  refine ⟨K*D^δ,by positivity,max (max L₀ D) P₂,hL₀.trans
    ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro P hPP
  have hPL₀ : L₀≤P := (le_max_left L₀ D).trans ((le_max_left (max L₀ D) P₂).trans hPP)
  have hDP : D≤P := (le_max_right L₀ D).trans ((le_max_left (max L₀ D) P₂).trans hPP)
  have hPP₂ : P₂≤P := (le_max_right (max L₀ D) P₂).trans hPP
  have hP : 1≤P := hL₀.trans hPL₀
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hPD : P≤D*P := le_mul_of_one_le_left hPp.le hD
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hhalf (x : ℝ) (hx : 0≤x) (hkx : (k:ℝ)*x≤1) : x≤1/2 := by
    nlinarith [mul_nonneg (show 0≤(k:ℝ)-2 by linarith) hx]
  have hφhalf (i : Fin j) : φ i≤1/2 := hhalf _ (hφ i) (by
    have H := hshift i
    dsimp [shiftExponents] at H
    linarith)
  have hψhalf : ψ≤1/2 := hhalf _ hψ hψk
  have hR1 : 1≤P^η := Real.one_le_rpow hP hη.le
  have hMR (x : ℝ) (hx : x≤1/2) : P^x*P^η≤P := by
    rw [← Real.rpow_add hPp]
    exact (Real.rpow_le_rpow_of_exponent_le hP (by linarith)).trans_eq (Real.rpow_one P)
  have hQ0 : 0≤1-total φ := by linarith
  have hQ1 : 1-total φ≤1 := by linarith
  have hVQ : P^ψ≤D*P^(1-total φ) :=
    (Real.rpow_le_rpow_of_exponent_le hP (by linarith)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) hD)
  have hQP : D*P^(1-total φ)≤D*P := mul_le_mul_of_nonneg_left
    ((Real.rpow_le_rpow_of_exponent_le hP hQ1).trans_eq (Real.rpow_one P)) hDp.le
  have H := hrec (D*P) (hPL₀.trans hPD) P (P^η) (fun i => P^(φ i))
    (fun i => Real.one_le_rpow hP (hφ i))
    (fun i => (hMR (φ i) (hφhalf i)).trans hPD)
    (D*P^(1-total φ)) (P^ψ) (Real.one_le_rpow hP hψ) hVQ hQP
    (hMR ψ hψhalf) (hRtwo P hPP₂) (fixed_dilation_lower_smoothness hD hDP hη)
  have hquot : D*P^(1-total φ)/P^ψ=D*P^q := by
    dsimp [q]
    rw [Real.rpow_sub hPp (1-total φ) ψ]
    ring
  have hMnext : Fin.cons (P^ψ) (fun i => P^(φ i))=
      fun i : Fin (j+1) => (P:ℝ)^((Fin.cons ψ φ : Fin (j+1) → ℝ) i) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hnext : boxCrossMoment k (s+1) (2*(D*P)) P (P^η)
      (Fin.cons (P^ψ) (fun i => P^(φ i))) (2*(D*P^(1-total φ)/P^ψ))=X P (P^η) := by
    rw [hMnext,hquot]
    dsimp only [X,powerBoxCross]
    rw [total_cons]
    have he : 1-(ψ+total φ)=q := by dsimp [q]; ring
    rw [he]
    congr 1 <;> ring
  rw [hnext,hquot] at H
  rw [abs_of_nonneg (show 0≤powerBoxMixed k (s+1) D φ P (P^η) from boxMixedMoment_nonneg ..)]
  calc
    _ ≤ K*(D*P)^δ*G P (P^η) := by
      convert H using 1 <;> dsimp only [G,C,V,Z,U,n,powerBoxCard,powerBoxMixed] <;> ring
    _ = (K*D^δ)*P^δ*G P (P^η) := by
      rw [Real.mul_rpow hDp.le hPp.le]
      ring
    _ ≤ (K*D^δ)*P^δ*|G P (P^η)| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

#print axioms powerBoxCross_power
#print axioms powerBoxMixed_power
end Waring.SeedCompletionNaturalBox
