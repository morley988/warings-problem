import WaringSiegel.WSL4RamanujamFullCount
import WaringSiegel.WSL4RamanujamDigitBudget

/-! # Uniform precision and summand envelope for wild composite exponents

The general odd-prime precision can exceed 4*p^r. The correct universal
bound for r>=1 is p^tau<=2*(p^r)^2. This is sufficient at every composite
exponent m>=4, including the extra unit used for the final Hensel lift.
-/
namespace WaringSiegel.WSL4Local

theorem ramanujam_precision_power_le (p r : ℕ) (hp : 2≤p) (hr : 1≤r) :
    p^(r+if p=2 then 2 else 1)≤2*(p^r)^2 := by
  have hP : 2≤p^r := hp.trans (Nat.le_pow hr)
  by_cases hp2 : p=2
  · subst p
    simp only [ite_true,pow_add]
    norm_num
    nlinarith
  · simp only [if_neg hp2,pow_succ]
    have hpP : p≤p^r := Nat.le_pow hr
    nlinarith

theorem ramanujam_full_wild_envelope_lt (m : ℝ) (hm : 4≤m) :
    4*m*(m+1)*(m*(m+1)/2+1)*(2*m-1)+
      (m-1)*(2*m^2-1)*(m^2+1)+1<8*m^5 := by
  let t := m-4
  have ht : 0≤t := by dsimp [t]; linarith
  have hidentity : 8*m^5-
      (4*m*(m+1)*(m*(m+1)/2+1)*(2*m-1)+
        (m-1)*(2*m^2-1)*(m^2+1)+1)=
      2*t^5+36*t^4+247*t^3+787*t^2+1101*t+450 := by dsimp [t]; ring
  have hpos : 0<2*t^5+36*t^4+247*t^3+787*t^2+1101*t+450 := by positivity
  linarith

#print axioms ramanujam_precision_power_le
#print axioms ramanujam_full_wild_envelope_lt
end WaringSiegel.WSL4Local
