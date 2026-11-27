import Waring.EndgameCompletionDiscrete
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Gcd-weighted harmonic completion sums

Writing b=gcd(b,q)*(b/gcd(b,q)) injects the actual frequency set into a
divisor/quotient rectangle. This supplies the logarithmic loss required
when summing the nonzero Fourier frequencies.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion

theorem gcd_harmonic_sum_le (q N : ℕ) (hq : 0<q) :
    (∑ b∈Finset.Icc 1 N,(Nat.gcd b q : ℝ)/(b : ℝ)) ≤
      (q.divisors.card : ℝ)*(harmonic N : ℝ) := by
  let key : ℕ → ℕ × ℕ := fun b=>(Nat.gcd b q,b/Nat.gcd b q)
  have hrec (b : ℕ) : b=(key b).1*(key b).2 := (Nat.mul_div_cancel' (Nat.gcd_dvd_left b q)).symm
  have hinj : Function.Injective key := by
    intro b c hbc
    rw [hrec b,hrec c,hbc]
  have hsub : (Finset.Icc 1 N).image key ⊆ q.divisors ×ˢ Finset.Icc 1 N := by
    intro z hz
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
    have hbpos : 0<b := (Finset.mem_Icc.mp hb).1
    apply Finset.mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hq.ne'⟩,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
    · have hpos : 0<(key b).2 := by
        apply Nat.pos_of_ne_zero
        intro hz
        have hh := hrec b
        rw [hz,Nat.mul_zero] at hh
        omega
      exact hpos
    · exact (Nat.div_le_self _ _).trans (Finset.mem_Icc.mp hb).2
  have hweight (b : ℕ) (hb : b∈Finset.Icc 1 N) :
      (Nat.gcd b q : ℝ)/(b : ℝ)=((key b).2 : ℝ)⁻¹ := by
    have hd : 0<Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
    have hd0 : (Nat.gcd b q : ℝ)≠0 := by exact_mod_cast hd.ne'
    have hbR : (b : ℝ)=(Nat.gcd b q : ℝ)*((key b).2 : ℝ) := by exact_mod_cast hrec b
    rw [hbR]
    field_simp
  calc
    _ = ∑ b∈Finset.Icc 1 N,((key b).2 : ℝ)⁻¹ := Finset.sum_congr rfl hweight
    _ = ∑ z∈(Finset.Icc 1 N).image key,(z.2 : ℝ)⁻¹ :=
      (Finset.sum_image (f := fun z : ℕ × ℕ=>(z.2 : ℝ)⁻¹) hinj.injOn).symm
    _ ≤ ∑ z∈q.divisors ×ˢ Finset.Icc 1 N,(z.2 : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
    _ = (q.divisors.card : ℝ)*∑ b∈Finset.Icc 1 N,(b : ℝ)⁻¹ := by
      rw [Finset.sum_product]
      simp
    _ = _ := by simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

theorem gcd_reflect (q b : ℕ) (hb : b≤q) : Nat.gcd (q-b) q=Nat.gcd b q := by
  calc
    _ = Nat.gcd (q-b) b := by
      have h := Nat.gcd_sub_self_right (m := q-b) (n := q) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self hb] at h
      exact h.symm
    _ = Nat.gcd q b := Nat.gcd_sub_self_left hb
    _ = _ := Nat.gcd_comm _ _

theorem gcd_harmonic_reflection (q : ℕ) :
    (∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)/(q-b : ℕ)) =
      ∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)/(b : ℝ) := by
  symm
  apply Finset.sum_bij (fun b _=>q-b)
  · intro b hb
    have hh := Finset.mem_Icc.mp hb
    apply Finset.mem_Icc.mpr
    omega
  · intro b hb c hc hbc
    have hb' := Finset.mem_Icc.mp hb
    have hc' := Finset.mem_Icc.mp hc
    omega
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    refine ⟨q-b,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    exact Nat.sub_sub_self (by omega)
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    rw [gcd_reflect q b (by omega),Nat.sub_sub_self (by omega)]

theorem gcd_symmetric_harmonic_sum_le (q : ℕ) (hq : 0<q) :
    (∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)/(min b (q-b) : ℕ)) ≤
      2*(q.divisors.card : ℝ)*(harmonic (q-1) : ℝ) := by
  calc
    _ ≤ ∑ b∈Finset.Icc 1 (q-1),
        ((Nat.gcd b q : ℝ)/(b : ℝ)+(Nat.gcd b q : ℝ)/(q-b : ℕ)) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b≤q-b
      · rw [min_eq_left hb]
        exact le_add_of_nonneg_right (by positivity)
      · rw [min_eq_right (by omega)]
        exact le_add_of_nonneg_left (by positivity)
    _ = 2*∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)/(b : ℝ) := by
      rw [Finset.sum_add_distrib,gcd_harmonic_reflection]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gcd_harmonic_sum_le q (q-1) hq)
        (by norm_num : (0 : ℝ)≤2)

theorem sum_nonzero_zmod_eq_Icc (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ b∈(Finset.univ : Finset (ZMod q)).erase 0,f b.val)=
      ∑ b∈Finset.Icc 1 (q-1),f b := by
  symm
  apply Finset.sum_bij (fun (b : ℕ) _=>(b : ZMod q))
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro hz
    have hh := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hh
    omega
  · intro b hb c hc hbc
    have hb' := Finset.mem_Icc.mp hb
    have hc' := Finset.mem_Icc.mp hc
    have hh := congrArg ZMod.val hbc
    rwa [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at hh
  · intro b hb
    have hb0 := (Finset.mem_erase.mp hb).1
    have hbpos : 0<b.val := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hb0
      exact ZMod.val_injective _ (by simpa only [ZMod.val_zero] using hz)
    refine ⟨b.val,Finset.mem_Icc.mpr ⟨hbpos,by have := b.val_lt; omega⟩,ZMod.natCast_zmod_val b⟩
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    rw [ZMod.val_natCast_of_lt (by omega)]

theorem harmonic_le_rpow (N : ℕ) (hN : 1≤N) {ε : ℝ} (hε : 0<ε) :
    (harmonic N : ℝ)≤(1+1/ε)*(N : ℝ)^ε := by
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hp : (1 : ℝ)≤(N : ℝ)^ε := Real.one_le_rpow hN1 hε.le
  calc
    _ ≤ 1+Real.log N := harmonic_le_one_add_log N
    _ ≤ 1+(N : ℝ)^ε/ε := add_le_add_left (Real.log_natCast_le_rpow_div N hε) _
    _ ≤ (N : ℝ)^ε+(N : ℝ)^ε/ε := add_le_add_right hp _
    _ = _ := by ring

theorem harmonic_pred_le_rpow (q : ℕ) (hq : 0<q) {ε : ℝ} (hε : 0<ε) :
    (harmonic (q-1) : ℝ)≤(1+1/ε)*(q : ℝ)^ε := by
  by_cases hq1 : q=1
  · subst q
    simp only [Nat.sub_self,harmonic_zero,Rat.cast_zero,Nat.cast_one,Real.one_rpow,mul_one]
    positivity
  have hN : 1≤q-1 := by omega
  apply (harmonic_le_rpow (q-1) hN hε).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le q 1) hε.le) (by positivity)

theorem gcd_unweighted_sum_le (q : ℕ) (hq : 0<q) :
    (∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)) ≤
      (q : ℝ)*(q.divisors.card : ℝ)*(harmonic (q-1) : ℝ) := by
  calc
    _ ≤ ∑ b∈Finset.Icc 1 (q-1),(q : ℝ)*((Nat.gcd b q : ℝ)/b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb' := Finset.mem_Icc.mp hb
      have hb0 : (b : ℝ)≠0 := by exact_mod_cast (show b≠0 by omega)
      calc
        _ = (b : ℝ)*((Nat.gcd b q : ℝ)/b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show b≤q by omega)) (by positivity)
    _ = (q : ℝ)*∑ b∈Finset.Icc 1 (q-1),(Nat.gcd b q : ℝ)/b := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gcd_harmonic_sum_le q (q-1) hq)
        (Nat.cast_nonneg (α := ℝ) q)

def completedFrequencyWeight (q : ℕ) [NeZero q] (K : ℝ) : ℝ :=
  ∑ b∈(Finset.univ : Finset (ZMod q)).erase 0,
    (Nat.gcd b.val q : ℝ)*(2+K*(q : ℝ)/(min b.val (q-b.val) : ℕ))

theorem completedFrequencyWeight_le (q : ℕ) [NeZero q] {K : ℝ} (hK : 0≤K) :
    completedFrequencyWeight q K ≤
      2*(1+K)*(q : ℝ)*(q.divisors.card : ℝ)*(harmonic (q-1) : ℝ) := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold completedFrequencyWeight
  rw [sum_nonzero_zmod_eq_Icc q (fun b : ℕ=>(Nat.gcd b q : ℝ)*(2+K*(q : ℝ)/(min b (q-b) : ℕ)))]
  have heq (b : ℕ) : (Nat.gcd b q : ℝ)*(2+K*(q : ℝ)/(min b (q-b) : ℕ)) =
      2*(Nat.gcd b q : ℝ)+(K*(q : ℝ))*((Nat.gcd b q : ℝ)/(min b (q-b) : ℕ)) := by ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  apply (add_le_add (mul_le_mul_of_nonneg_left (gcd_unweighted_sum_le q hq) (by norm_num : (0 : ℝ)≤2))
    (mul_le_mul_of_nonneg_left (gcd_symmetric_harmonic_sum_le q hq) (by positivity))).trans_eq
  ring

theorem completedFrequencyWeight_normalized_le_rpow {K ε : ℝ} (hK : 0≤K) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q],
      (q : ℝ)⁻¹*completedFrequencyWeight q K≤C*(q : ℝ)^ε := by
  have hhalf : 0<ε/2 := by positivity
  obtain ⟨D,hD,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow 1 hhalf
  refine ⟨2*(1+K)*D*(1+1/(ε/2)),by positivity,?_⟩
  intro q _
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hnorm : (q : ℝ)⁻¹*completedFrequencyWeight q K ≤
      2*(1+K)*(q.divisors.card : ℝ)*(harmonic (q-1) : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (completedFrequencyWeight_le q hK) (by positivity)).trans_eq
    field_simp
  have hdivq : (q.divisors.card : ℝ)≤D*(q : ℝ)^(ε/2) := by simpa only [pow_one] using hdiv q hq
  have hhar := harmonic_pred_le_rpow q hq hhalf
  apply hnorm.trans
  have hprod := mul_le_mul hdivq hhar (by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _=>by positivity)) (by positivity)
  rw [mul_assoc (2*(1+K)) (q.divisors.card : ℝ) (harmonic (q-1) : ℝ)]
  apply (mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ)≤2*(1+K))).trans_eq
  rw [show (q : ℝ)^ε=(q : ℝ)^(ε/2)*(q : ℝ)^(ε/2) by
    rw [← Real.rpow_add hqR]; congr 1; ring]
  ring

#print axioms gcd_symmetric_harmonic_sum_le
#print axioms completedFrequencyWeight_normalized_le_rpow

end Waring.EndgameCompletion
