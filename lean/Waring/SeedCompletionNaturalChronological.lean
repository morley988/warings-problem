import Waring.SeedCompletionNaturalInitial

/-! # Chronological source stages and their exact backward exponent rows -/
noncomputable section
namespace Waring.SeedCompletionNaturalBox
open PolicyCompletionMajorPowerRanges SeedCompletionSourceBounds SmoothMoments

theorem powerBoxMixed_power_snoc {k j s : ℕ} {D ψ lam χ : ℝ} (φ : Fin j → ℝ)
    (hk : 2≤k) (hjk : j<k) (hD : 1≤D)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hψ : 0≤ψ) (hψk : (k:ℝ)*ψ≤1) (hsum : total φ+ψ≤1)
    (hU : AdmissibleExponent k (2*(s+1)) lam)
    (hX : SourcePowerBound (powerBoxCross k (s+1) (2*D) (Fin.snoc φ ψ)) χ) :
    SourcePowerBound (powerBoxMixed k (s+1) D φ)
      (parameterExponent k φ+(2*((s:ℝ)+1)-1)*ψ+
        max (parameterExponent k φ+1+ψ+(1-total φ-ψ)*lam) χ) := by
  exact powerBoxMixed_power φ hk hjk hD hφ hshift hψ hψk hsum hU
    (hX.congr (fun P R _ _ => powerBoxCross_snoc k (s+1) (2*D) ψ φ P R))

theorem backward_cross_power {k j s u t : ℕ} {D ψ lamu lamt χ : ℝ} (φ : Fin j → ℝ)
    (hk : 2≤k) (hjk : j<k) (hD : 1≤D)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hψ : 0≤ψ) (hψk : (k:ℝ)*ψ≤1) (hsum : total φ+ψ≤1)
    (hsplit : (u+1)+t=2*s)
    (hU : AdmissibleExponent k (2*(u+1)) lamu)
    (hT : AdmissibleExponent k (2*t) lamt)
    (hX : SourcePowerBound (powerBoxCross k (u+1) (2*D) (Fin.snoc φ ψ)) χ) :
    SourcePowerBound (powerBoxCross k s D φ)
      ((parameterExponent k φ+(2*((u:ℝ)+1)-1)*ψ+(1-total φ)*lamt)/2+
        max (parameterExponent k φ+1+ψ+(1-total φ-ψ)*lamu) χ/2) := by
  have htotal : 0≤total φ := Finset.sum_nonneg (fun i _ => hφ i)
  have H := powerBoxMixed_power_snoc φ hk hjk hD hφ hshift hψ hψk hsum hU hX
  have H' := powerBoxCross_power φ hD (by linarith) (by linarith) hsplit H hT
  convert H' using 1 <;> ring

theorem first_box_admissible_snoc {k s : ℕ} {ψ lam χ : ℝ}
    (hk : 2≤k) (hψ : 0≤ψ) (hψk : (k:ℝ)*ψ≤1)
    (hU : AdmissibleExponent k (2*(s+1)) lam)
    (hX : SourcePowerBound (powerBoxCross k (s+1) 2 (Fin.snoc emptyPhi ψ)) χ) :
    AdmissibleExponent k (2*(s+2))
      ((2*((s:ℝ)+1)-1)*ψ+max (1+ψ+(1-ψ)*lam) χ) := by
  exact first_box_admissible hk hψ hψk hU
    (hX.congr (fun P R _ _ => powerBoxCross_snoc k (s+1) 2 ψ emptyPhi P R))

#print axioms backward_cross_power
#print axioms first_box_admissible_snoc
end Waring.SeedCompletionNaturalBox
