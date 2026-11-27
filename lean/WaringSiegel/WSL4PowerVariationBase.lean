import WaringSiegel.WSL4PowerFiniteError
import WaringSiegel.WSL4PowerIdealSeries

/-! # Uniform initial errors for the literal local power-count sequence -/
noncomputable section
set_option maxHeartbeats 1600000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem singular_local_power_count_upper (k n p:ℕ) (a:R) :
    Nat.card (SingularLocalPowerSolutions k R (maximalIdeal R^(n+1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) p a)≤Nat.card (ResidueField R)^(p*n) := by
  letI := dvr_power_quotient_finite (R:=R) (n+1)
  let Z := {z:R⧸maximalIdeal R^(n+1)//
    localResidueReduction _ (Ideal.pow_le_self (Nat.succ_ne_zero n)) z=0}
  let f : SingularLocalPowerSolutions k R (maximalIdeal R^(n+1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) p a→(Fin p→Z) :=
    fun x i => ⟨x.val i,x.property.2 i⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have h := Nat.card_le_card_of_injective f hf
  have hZ : Nat.card Z=Nat.card (ResidueField R)^n := residue_reduction_fiber_card n 0
  simpa only [Nat.card_fun,Nat.card_fin,hZ,← pow_mul,Nat.mul_comm n p] using h

theorem normalized_power_count_sub_primitive_bounds
    (k p n:ℕ) (hk:0<k) (hp:1≤p) (hku:IsUnit (k:R)) (a:R) :
    0≤normalizedLocalPowerCount R k p (n+1) a-
      (Nat.card (PrimitivePowerResidues k R p a):ℝ)/(Nat.card (ResidueField R):ℝ)^(p-1) ∧
    normalizedLocalPowerCount R k p (n+1) a-
      (Nat.card (PrimitivePowerResidues k R p a):ℝ)/(Nat.card (ResidueField R):ℝ)^(p-1)≤
        (Nat.card (ResidueField R):ℝ)^(p*n)/(Nat.card (ResidueField R):ℝ)^((p-1)*(n+1)) := by
  letI := dvr_power_quotient_finite (R:=R) (n+1)
  have hc := local_power_count_primitive_add_singular k (maximalIdeal R^(n+1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) p a
  have he := normalized_primitive_local_power_count_eq k hk hku (p-1) n a
  rw [Nat.sub_add_cancel hp] at he
  rw [← he]
  unfold normalizedLocalPowerCount normalizedPrimitiveLocalPowerCount
  rw [hc]
  simp only [Nat.cast_add,add_div,add_sub_cancel_left]
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast singular_local_power_count_upper (R:=R) k n p a

theorem primitive_power_residue_density_upper_eight
    (k p:ℕ) (hk:0<k) (hp:8≤p) (a:R) :
    (Nat.card (PrimitivePowerResidues k R p a):ℝ)/(Nat.card (ResidueField R):ℝ)^(p-1)≤
      1+((k-1:ℕ):ℝ)^8/(Nat.card (ResidueField R):ℝ)^3 := by
  letI := Fintype.ofFinite (ResidueField R)
  have herr := (abs_le.mp (finite_field_power_eight_normalized_error k p hk hp (residue R a))).2
  simp only [← Nat.card_eq_fintype_card] at herr
  let out : PrimitivePowerResidues k R p a→
      {x:Fin p→ResidueField R//(∑ i,x i^k)=residue R a} := fun x => ⟨x.val,x.property.1⟩
  have hinj : Function.Injective out := by
    intro x y h
    exact Subtype.ext (congrArg (fun z:{x:Fin p→ResidueField R//(∑ i,x i^k)=residue R a} => z.val) h)
  have hc := Nat.card_le_card_of_injective out hinj
  have hcR : (Nat.card (PrimitivePowerResidues k R p a):ℝ)≤
      Nat.card {x:Fin p→ResidueField R//(∑ i,x i^k)=residue R a} := by exact_mod_cast hc
  have hdiv := div_le_div_of_nonneg_right hcR (show 0≤(Nat.card (ResidueField R):ℝ)^(p-1) by positivity)
  linarith

theorem normalized_power_count_initial_error
    (k p n:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (hku:IsUnit (k:R))
    (hn:n<k) (a:R) :
    |normalizedLocalPowerCount R k p (n+1) a-1|≤
      (((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3 := by
  have hq0 : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hq1 : 1≤(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  obtain ⟨-,hu⟩ := normalized_power_count_sub_primitive_bounds k p n hk (by omega) hku a
  have hr : (Nat.card (ResidueField R):ℝ)^(p*n)/(Nat.card (ResidueField R):ℝ)^((p-1)*(n+1))≤
      1/(Nat.card (ResidueField R):ℝ)^3 := by
    apply (div_le_div_iff₀ (pow_pos hq0 _) (pow_pos hq0 3)).mpr
    rw [one_mul,← pow_add]
    apply pow_le_pow_right₀ hq1
    have he : p-1+1=p := by omega
    have hpn : n+3≤p-1 := by omega
    nlinarith
  have hl := normalized_local_power_eight_good_tail k p hk hp hku n a
  have hpU := primitive_power_residue_density_upper_eight k p hk hp a
  apply abs_le.mpr
  constructor
  · linarith
  · have hb := hu.trans hr
    rw [add_div]
    linarith

theorem normalized_power_increment_initial
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (hku:IsUnit (k:R))
    (a:R) (n:ℕ) (hn:n<k) :
    |normalizedLocalPowerCount R k p (n+1) a-normalizedLocalPowerCount R k p n a|≤
      2*((((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3) := by
  by_cases hn0:n=0
  · subst n
    rw [normalizedLocalPowerCount_zero]
    have h := normalized_power_count_initial_error k p 0 hk hp hkp hku hn a
    have hE : 0≤((((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3) := by positivity
    linarith
  · have he:n=(n-1)+1 := by omega
    have h1 := normalized_power_count_initial_error k p n hk hp hkp hku hn a
    have h0 := normalized_power_count_initial_error k p (n-1) hk hp hkp hku (by omega) a
    rw [← he] at h0
    calc
      _≤|normalizedLocalPowerCount R k p (n+1) a-1|+|normalizedLocalPowerCount R k p n a-1| := by
        simpa only [abs_sub_comm (1:ℝ) (normalizedLocalPowerCount R k p n a)] using
          abs_sub_le (normalizedLocalPowerCount R k p (n+1) a) 1 (normalizedLocalPowerCount R k p n a)
      _≤_ := by linarith

#print axioms normalized_power_count_initial_error
#print axioms normalized_power_increment_initial
end WaringSiegel.WSL4Local
