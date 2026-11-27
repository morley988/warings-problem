import WaringSiegel.WSL4PowerVariationBase
import WaringSiegel.WSL4LocalPowerDensityRecurrence

/-! # Actual conductor increments contract by one degree at every finite prime -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem powerDerivativeOrder_eq_zero_of_unit (k:ℕ) (hku:IsUnit (k:R)) :
    powerDerivativeOrder R k=0 := by
  unfold powerDerivativeOrder
  rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hku]
  rfl

theorem power_count_scaling_ratio (k p:ℕ) (hk:0<k) (hp:2≤p) (hkp:k≤p) :
    (Nat.card (ResidueField R):ℝ)^(p*(k-1))/(Nat.card (ResidueField R):ℝ)^((p-1)*k)=
      1/(Nat.card (ResidueField R):ℝ)^(p-k) := by
  have hk':k-1+1=k := by omega
  have hp':p-2+2=p := by omega
  have hp1:p-2+1=p-1 := by omega
  have he:p-1-(k-1)=p-k := by omega
  simpa only [hk',hp',hp1,he] using
    power_density_scaling_ratio_eq (R:=R) (k-1) (p-2) (by omega)

theorem normalized_power_count_scaling_recurrence
    (k p n:ℕ) (hk:0<k) (hp:2≤p) (hkp:k≤p) (hk0:(k:R)≠0)
    {π:R} (hπ:Irreducible π) (hn:2*powerDerivativeOrder R k≤n) (b:R) :
    normalizedLocalPowerCount R k p (n+k) (π^k*b)=
      primitivePowerDensityAllPrimes R k p (π^k*b)+
        normalizedLocalPowerCount R k p n b*(1/(Nat.card (ResidueField R):ℝ)^(p-k)) := by
  have hk':k-1+1=k := by omega
  have hp':p-2+2=p := by omega
  have hp1:p-2+1=p-1 := by omega
  have hn':n+(k-1)+1=n+k := by omega
  have h := normalized_power_count_scaling_recurrence_all_primes (R:=R)
    (k-1) (p-2) n (by simpa only [hk'] using hk0) hπ (by simpa only [hk'] using (show 2*powerDerivativeOrder R k≤n+(k-1) by omega)) b
  simp only [hk',hp',hp1,hn',power_count_scaling_ratio k p hk hp hkp] at h
  exact h

theorem normalized_power_count_not_mem_recurrence
    (k p n:ℕ) (hk:0<k) (hp:2≤p) (hk0:(k:R)≠0)
    (hn:2*powerDerivativeOrder R k≤n) {a:R} (ha:a∉maximalIdeal R^k) :
    normalizedLocalPowerCount R k p (n+k) a=primitivePowerDensityAllPrimes R k p a := by
  have hk':k-1+1=k := by omega
  have hp':p-2+2=p := by omega
  have hn':n+(k-1)+1=n+k := by omega
  simpa only [hk',hp',hn'] using
    normalized_power_count_eq_of_not_mem_power_ideal (R:=R) (k-1) (p-2) n
      (by simpa only [hk'] using hk0) (by simpa only [hk'] using (show 2*powerDerivativeOrder R k≤n+(k-1) by omega))
      (by simpa only [hk'] using ha)

theorem normalized_power_increment_step
    (k p:ℕ) (hk:0<k) (hp:2≤p) (hkp:k≤p) (hk0:(k:R)≠0) (a:R) :
    (∀ n,2*powerDerivativeOrder R k≤n →
      normalizedLocalPowerCount R k p (n+k+1) a-normalizedLocalPowerCount R k p (n+k) a=0) ∨
    ∃ b:R,∀ n,2*powerDerivativeOrder R k≤n →
      normalizedLocalPowerCount R k p (n+k+1) a-normalizedLocalPowerCount R k p (n+k) a=
        (1/(Nat.card (ResidueField R):ℝ)^(p-k))*
          (normalizedLocalPowerCount R k p (n+1) b-normalizedLocalPowerCount R k p n b) := by
  by_cases ha:a∈maximalIdeal R^k
  · obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [hπ.maximalIdeal_eq,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at ha
    obtain ⟨b,rfl⟩ := ha
    refine Or.inr ⟨b,fun n hn => ?_⟩
    rw [show n+k+1=(n+1)+k by omega,
      normalized_power_count_scaling_recurrence k p (n+1) hk hp hkp hk0 hπ (by omega),
      normalized_power_count_scaling_recurrence k p n hk hp hkp hk0 hπ hn]
    ring
  · left
    intro n hn
    rw [show n+k+1=(n+1)+k by omega,
      normalized_power_count_not_mem_recurrence k p (n+1) hk hp hk0 (by omega) ha,
      normalized_power_count_not_mem_recurrence k p n hk hp hk0 hn ha,sub_self]

#print axioms normalized_power_count_scaling_recurrence
#print axioms normalized_power_increment_step
end WaringSiegel.WSL4Local
