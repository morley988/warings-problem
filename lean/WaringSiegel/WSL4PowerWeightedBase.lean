import WaringSiegel.WSL4PowerIncrementRecurrence
import WaringSiegel.WSL4PowerWeightedRecurrence

/-! # Actual weighted conductor increments for arbitrary positive degree -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3

def powerConductorWeight (R:Type*) [CommRing R] [IsLocalRing R] (k n:ℕ) : ℝ :=
  (Nat.card (ResidueField R):ℝ)^(n/k+1)

def weightedPowerIncrement (R:Type*) [CommRing R] [IsLocalRing R] (k p:ℕ) (a:R) (n:ℕ) : ℝ :=
  powerConductorWeight R k n*
    |normalizedLocalPowerCount R k p (n+1) a-normalizedLocalPowerCount R k p n a|

variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem weightedPowerIncrement_nonneg (k p:ℕ) (a:R) (n:ℕ) :
    0≤weightedPowerIncrement R k p a n := by
  unfold weightedPowerIncrement powerConductorWeight
  positivity

theorem normalizedLocalPowerCount_nonneg (k p:ℕ) (a:R) (n:ℕ) :
    0≤normalizedLocalPowerCount R k p n a := by unfold normalizedLocalPowerCount; positivity

theorem normalizedLocalPowerCount_le_residue_pow (k p:ℕ) (hp:1≤p) (a:R) (n:ℕ) :
    normalizedLocalPowerCount R k p n a≤(Nat.card (ResidueField R):ℝ)^n := by
  letI := dvr_power_quotient_finite (R:=R) n
  have hc := Nat.card_le_card_of_injective
    (fun x:LocalPowerSolutions R (maximalIdeal R^n) k p a => x.val) Subtype.val_injective
  have hc' : localPowerSolutionCount R (maximalIdeal R^n) k p a≤Nat.card (ResidueField R)^(p*n) := by
    simpa only [localPowerSolutionCount,Nat.card_fun,Nat.card_fin,dvr_power_quotient_card,
      ← pow_mul,Nat.mul_comm n p] using hc
  have hq : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  unfold normalizedLocalPowerCount
  apply (div_le_iff₀ (pow_pos hq _)).mpr
  have he:n+(p-1)*n=p*n := by
    calc
      n+(p-1)*n=(p-1+1)*n := by ring
      _=p*n := by rw [Nat.sub_add_cancel hp]
  rw [← pow_add,he]
  exact_mod_cast hc'

theorem weightedPowerIncrement_initial_bound
    (k p T n:ℕ) (hp:1≤p) (hn:n<T+k) (a:R) :
    weightedPowerIncrement R k p a n≤(Nat.card (ResidueField R):ℝ)^(2*(T+k)) := by
  have hq1 : 1≤(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have h0 := normalizedLocalPowerCount_nonneg k p a n
  have h1 := normalizedLocalPowerCount_nonneg k p a (n+1)
  have hnU := (normalizedLocalPowerCount_le_residue_pow k p hp a n).trans
    (pow_le_pow_right₀ hq1 (by omega : n≤T+k))
  have hsU := (normalizedLocalPowerCount_le_residue_pow k p hp a (n+1)).trans
    (pow_le_pow_right₀ hq1 (by omega : n+1≤T+k))
  have habs : |normalizedLocalPowerCount R k p (n+1) a-normalizedLocalPowerCount R k p n a|≤
      (Nat.card (ResidueField R):ℝ)^(T+k) := abs_le.mpr ⟨by linarith,by linarith⟩
  have hw : powerConductorWeight R k n≤(Nat.card (ResidueField R):ℝ)^(T+k) := by
    apply pow_le_pow_right₀ hq1
    have hd := Nat.div_le_self n k
    omega
  unfold weightedPowerIncrement
  calc
    _≤(Nat.card (ResidueField R):ℝ)^(T+k)*(Nat.card (ResidueField R):ℝ)^(T+k) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _=_ := by rw [← pow_add]; congr 1; omega

theorem powerConductorWeight_add_degree (k:ℕ) (hk:0<k) (n:ℕ) :
    powerConductorWeight R k (n+k)=(Nat.card (ResidueField R):ℝ)*powerConductorWeight R k n := by
  unfold powerConductorWeight
  rw [Nat.add_div_right n hk,pow_succ]
  ring

theorem weightedPowerIncrement_good_initial
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (hku:IsUnit (k:R))
    (a:R) (n:ℕ) (hn:n<k) :
    weightedPowerIncrement R k p a n≤
      2*((k-1:ℕ):ℝ)^8/(Nat.card (ResidueField R):ℝ)^2+2/(Nat.card (ResidueField R):ℝ)^2 := by
  have hq0 : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hw : powerConductorWeight R k n=(Nat.card (ResidueField R):ℝ) := by
    simp only [powerConductorWeight,Nat.div_eq_of_lt hn,zero_add,pow_one]
  unfold weightedPowerIncrement
  rw [hw]
  calc
    _≤(Nat.card (ResidueField R):ℝ)*
      (2*((((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (normalized_power_increment_initial k p hk hp hkp hku a n hn) hq0.le
    _=_ := by field_simp

#print axioms normalizedLocalPowerCount_le_residue_pow
#print axioms weightedPowerIncrement_good_initial
end WaringSiegel.WSL4Local
