import WaringSiegel.WSL4RamanujamWildCount
import WaringSiegel.WSL4RamanujamDeepBudget

/-! # The complete natural-number cost of the small residue-degree construction -/
namespace WaringSiegel.WSL4Local

theorem full_wild_parameter_count_lt
    (m P H A T f : ℝ) (hm : 4≤m) (hP : 0≤P) (hPm : P≤m)
    (hH : 0≤H) (hHbound : H≤P*(P+1)/2)
    (hA : 0≤A) (hAbound : A≤2*m-1)
    (hT : 0≤T) (hTbound : T≤2*m^2-1)
    (hf : 0≤f) (hfbound : f≤m-1) :
    4*m*(P+1)*(H+1)*A+(m*P+1)*f*T+1<8*m^5 := by
  have hm0 : 0≤m := by linarith
  have hm1 : 0≤m-1 := by linarith
  have hmT : 0≤2*m^2-1 := by nlinarith
  have hH' : H≤m*(m+1)/2 := by
    apply hHbound.trans
    gcongr
  have hfirst : 4*m*(P+1)*(H+1)*A≤4*m*(m+1)*(m*(m+1)/2+1)*(2*m-1) := by gcongr
  have hsecond : (m*P+1)*f*T≤(m-1)*(2*m^2-1)*(m^2+1) := by
    calc
      _≤(m*m+1)*(m-1)*(2*m^2-1) := by gcongr
      _=(m-1)*(2*m^2-1)*(m^2+1) := by ring
  exact (add_le_add_right (add_le_add hfirst hsecond) 1).trans_lt
    (ramanujam_full_wild_envelope_lt m hm)

theorem full_wild_natural_budget_lt
    (p n r f : ℕ) (hp : 2≤p) (hn : 0<n) (hr : 1≤r)
    (hm : 4≤n*p^r) (hf : f<n*p^r) :
    ramanujamDeepBudget p n r*powerDigitBudget p (r+1)+
      ((n*p^r)*p^r+1)*f*(p^(r+if p=2 then 2 else 1)-1)+1<8*(n*p^r)^5 := by
  let P := p^r
  let m := n*P
  let H := P*(P+1)/2
  let A := powerDigitBudget p (r+1)
  let T := p^(r+if p=2 then 2 else 1)-1
  have hPm : P≤m := by dsimp [m]; nlinarith
  have hPmR : (P:ℝ)≤m := by exact_mod_cast hPm
  have hmR : (4:ℝ)≤m := by exact_mod_cast hm
  have hHnat : 2*H≤P*(P+1) := by dsimp [H]; omega
  have hHreal : (H:ℝ)≤(P:ℝ)*(P+1)/2 := by
    have h : 2*(H:ℝ)≤(P:ℝ)*(P+1) := by exact_mod_cast hHnat
    linarith
  have hAnat : A+1≤2*m :=
    (powerDigitBudget_le_twice p r hp).trans (Nat.mul_le_mul_left 2 hPm)
  have hAreal : (A:ℝ)≤2*(m:ℝ)-1 := by
    have h : (A:ℝ)+1≤2*(m:ℝ) := by exact_mod_cast hAnat
    linarith
  have hTnat : T+1≤2*m^2 := by
    have hp1 : 1≤p^(r+if p=2 then 2 else 1) := Nat.one_le_pow _ _ (by omega)
    dsimp [T]
    rw [Nat.sub_add_cancel hp1]
    exact (ramanujam_precision_power_le p r hp hr).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hPm 2))
  have hTreal : (T:ℝ)≤2*(m:ℝ)^2-1 := by
    have h : (T:ℝ)+1≤2*(m:ℝ)^2 := by exact_mod_cast hTnat
    linarith
  have hfreal : (f:ℝ)≤(m:ℝ)-1 := by
    have h : (f:ℝ)+1≤(m:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hf)
    linarith
  have h := full_wild_parameter_count_lt (m:ℝ) (P:ℝ) (H:ℝ) (A:ℝ) (T:ℝ) (f:ℝ)
    hmR (by positivity) hPmR (by positivity) hHreal (by positivity) hAreal
    (by positivity) hTreal (by positivity) hfreal
  have hNat : 4*m*(P+1)*(H+1)*A+(m*P+1)*f*T+1<8*m^5 := by exact_mod_cast h
  simpa only [ramanujamDeepBudget,m,P,H,A,T] using hNat

#print axioms full_wild_natural_budget_lt
end WaringSiegel.WSL4Local
