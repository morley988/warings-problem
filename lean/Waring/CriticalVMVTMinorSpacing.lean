import Waring.FiniteSpacing
import Waring.RationalSpacing
import Waring.DyadicLogLoss

/-!
# The finite reciprocal average in the critical VMVT minor-arc argument

The distance hypothesis is imposed on the actual multiples of the leading
coefficient. Short blocks of sample indices give separated signed fractional
parts. The proof retains an explicit dyadic depth before absorbing the fixed
logarithmic loss into an arbitrary positive power.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CriticalVMVTMinorSpacing

open RationalSpacing FiniteSpacing

/-- Nearest-integer representatives are separated whenever their difference
is separated from every integer. -/
theorem signedFraction_separation_of_difference
    (k N : ℕ) (θ α δ : ℝ)
    (hminor : ∀ d : ℕ, 1 ≤ d → d ≤ N → δ ≤ integerDistance ((d : ℝ) * θ))
    {y z : ℕ} (hyz : y < z) (hk : 0 < k) (hshort : k * (z-y) ≤ N) :
    δ ≤ |signedFraction ((k : ℝ)*y*θ+α) -
      signedFraction ((k : ℝ)*z*θ+α)| := by
  have hd : 1 ≤ k*(z-y) := Nat.mul_pos hk (Nat.sub_pos_of_lt hyz)
  have h := (hminor (k*(z-y)) hd hshort).trans
    (round_le (((k*(z-y) : ℕ) : ℝ)*θ)
      (round ((k : ℝ)*z*θ+α) - round ((k : ℝ)*y*θ+α)))
  rw [abs_sub_comm]
  convert h using 1
  congr 1
  unfold signedFraction
  rw [Nat.cast_mul, Nat.cast_sub hyz.le, Int.cast_sub]
  ring

/-- Indices with the same quotient by `N/k+1` have differences at most `N/k`.
This choice allows at most `k` blocks, without divisibility assumptions on `N`.
-/
theorem short_difference_of_same_block (k N y z : ℕ)
    (hblock : y/(N/k+1) = z/(N/k+1)) :
    z-y ≤ N/k := by
  have hy := Nat.mod_add_div y (N/k+1)
  have hz := Nat.mod_add_div z (N/k+1)
  have hyr : y%(N/k+1) < N/k+1 := Nat.mod_lt y (Nat.succ_pos (N/k))
  have hzr : z%(N/k+1) < N/k+1 := Nat.mod_lt z (Nat.succ_pos (N/k))
  rw [hblock] at hy
  omega

theorem block_index_lt (k N : ℕ) (hk : 0 < k) {y : ℕ} (hy : y ≤ N) :
    y/(N/k+1) < k := by
  have hmod := Nat.mod_lt N hk
  have hdiv := Nat.div_add_mod N k
  have hN : N < k*(N/k+1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos (N/k))).mpr (hy.trans_lt hN)

/-- Actual reciprocal sum with every cutoff and dyadic loss explicit. -/
theorem reciprocal_sum_dyadic
    (k N T : ℕ) (hk : 0 < k) (θ α : ℝ) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hcover : 1/2 ≤ a*2^T)
    (hminor : ∀ d : ℕ, 1 ≤ d → d ≤ N → δ ≤ integerDistance ((d : ℝ)*θ)) :
    (∑ y ∈ Finset.Icc 1 N,
      truncatedReciprocal a (integerDistance ((k : ℝ)*y*θ+α))) ≤
        (k : ℝ) * (4/δ*(T+1 : ℕ) + 4/a) := by
  classical
  let S := Finset.Icc 1 N
  let block := fun y : ℕ => y/(N/k+1)
  have hmaps : ∀ y ∈ S, block y ∈ Finset.range k := by
    intro y hy
    exact Finset.mem_range.mpr (block_index_lt k N hk (Finset.mem_Icc.mp hy).2)
  have hfiber (b : ℕ) :
      (∑ y ∈ S.filter (fun y => block y=b),
        truncatedReciprocal a (integerDistance ((k : ℝ)*y*θ+α))) ≤
      4/δ*(T+1 : ℕ) + 4/a := by
    simpa only [abs_signedFraction] using
      reciprocal_sum_of_separation (S.filter (fun y => block y=b))
        (fun y => signedFraction ((k : ℝ)*y*θ+α)) T ha hδ
        (fun y _ => (abs_signedFraction_le _).trans hcover)
        (by
          intro y hy z hz hyz
          have hblock : y/(N/k+1)=z/(N/k+1) :=
            (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hz).2.symm
          rcases lt_or_gt_of_ne hyz with hyz | hzy
          · apply signedFraction_separation_of_difference k N θ α δ hminor hyz hk
            exact (Nat.mul_le_mul_left k (short_difference_of_same_block k N y z hblock)).trans
              (Nat.mul_div_le N k)
          · rw [abs_sub_comm]
            apply signedFraction_separation_of_difference k N θ α δ hminor hzy hk
            exact (Nat.mul_le_mul_left k (short_difference_of_same_block k N z y hblock.symm)).trans
              (Nat.mul_div_le N k))
  calc
    (∑ y ∈ Finset.Icc 1 N, truncatedReciprocal a (integerDistance ((k : ℝ)*y*θ+α))) =
        ∑ b ∈ Finset.range k, ∑ y ∈ S.filter (fun y => block y=b),
          truncatedReciprocal a (integerDistance ((k : ℝ)*y*θ+α)) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ ≤ ∑ b ∈ Finset.range k, (4/δ*(T+1 : ℕ) + 4/a) :=
      Finset.sum_le_sum (fun b _ => hfiber b)
    _ = _ := by simp; ring

/-- Uniform power-saving form of the actual reciprocal average. The proof
works already for `N ≥ 1`; the usual minor-arc application has `N ≥ 2k`. -/
theorem reciprocal_average_bound (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ θ α : ℝ,
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        (2*(k : ℝ)*(N : ℝ)^(k-1))⁻¹ < integerDistance ((d : ℝ)*θ)) →
      (N : ℝ)⁻¹ * (∑ y ∈ Finset.Icc 1 N,
        truncatedReciprocal ((L*(N : ℝ)^(k-1))⁻¹)
          (integerDistance ((k : ℝ)*y*θ+α))) ≤
        C*(N : ℝ)^((k : ℝ)-2+ε) := by
  obtain ⟨TL,hTL,_⟩ := ShortHeightDistribution.exists_dyadic_cover
    (a := 1) (P := L) (by norm_num) hL
  simp only [one_mul] at hTL
  obtain ⟨D,hD,hdepth⟩ := DyadicLogLoss.clog_depth_pow_le_rpow 1 hε
  let A : ℝ := (k : ℝ) + TL + 1
  let C : ℝ := 4*(k : ℝ)*(2*(k : ℝ)*A*D+L)
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN θ α hminor
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let T := (k-1)*Nat.clog 2 N+TL
  have hNcover : (N : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 N) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) N
  have hcover : L*(N : ℝ)^(k-1) ≤ (2 : ℝ)^T := by
    dsimp [T]
    rw [pow_add, mul_comm (k-1), pow_mul]
    calc
      L*(N : ℝ)^(k-1) = (N : ℝ)^(k-1)*L := mul_comm _ _
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hNR.le hNcover (k-1)) hTL
        (by positivity) (by positivity)
  have hacover : 1/2 ≤ (L*(N : ℝ)^(k-1))⁻¹*(2 : ℝ)^T := by
    have h := mul_le_mul_of_nonneg_left hcover
      (inv_nonneg.mpr (show 0 ≤ L*(N : ℝ)^(k-1) by positivity))
    have heq : (L*(N : ℝ)^(k-1))⁻¹*(L*(N : ℝ)^(k-1))=1 :=
      inv_mul_cancel₀ (by positivity)
    rw [heq] at h
    linarith
  have hfinite := reciprocal_sum_dyadic k N T hkpos θ α
    (by positivity : 0 < (L*(N : ℝ)^(k-1))⁻¹)
    (by positivity : 0 < (2*(k : ℝ)*(N : ℝ)^(k-1))⁻¹)
    hacover (fun d hd hdN => (hminor d hd hdN).le)
  have hdepthN : ((Nat.clog 2 N+1 : ℕ) : ℝ) ≤ D*(N : ℝ)^ε := by
    simpa only [pow_one] using hdepth N hNpos
  have hT : ((T+1 : ℕ) : ℝ) ≤ A*D*(N : ℝ)^ε := by
    have hnat : T+1 ≤ (k+TL+1)*(Nat.clog 2 N+1) := by
      dsimp [T]
      have hkm : k-1 ≤ k := Nat.sub_le _ _
      nlinarith
    have hcast : ((T+1 : ℕ) : ℝ) ≤ A*((Nat.clog 2 N+1 : ℕ) : ℝ) := by
      dsimp [A]
      exact_mod_cast hnat
    exact hcast.trans (by nlinarith [mul_le_mul_of_nonneg_left hdepthN hA.le])
  have hpow : (1 : ℝ) ≤ (N : ℝ)^ε := Real.one_le_rpow hNR1 hε.le
  have hbracket : 2*(k : ℝ)*((T+1 : ℕ) : ℝ)+L ≤
      (2*(k : ℝ)*A*D+L)*(N : ℝ)^ε := by
    nlinarith [mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2*(k : ℝ)),
      mul_le_mul_of_nonneg_left hpow hLpos.le]
  have hpower : (N : ℝ)⁻¹*(N : ℝ)^(k-1)=(N : ℝ)^(k-2) := by
    have hexp : k-1=(k-2)+1 := by omega
    rw [hexp,pow_succ]
    field_simp
  calc
    _ ≤ (N : ℝ)⁻¹*((k : ℝ)*(4 / (2*(k : ℝ)*(N : ℝ)^(k-1))⁻¹ *
        ((T+1 : ℕ) : ℝ)+4/(L*(N : ℝ)^(k-1))⁻¹)) :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ = 4*(k : ℝ)*(N : ℝ)^(k-2)*(2*(k : ℝ)*((T+1 : ℕ) : ℝ)+L) := by
      simp only [div_inv_eq_mul]
      rw [show (N : ℝ)⁻¹*((k : ℝ)*(4*(2*(k : ℝ)*(N : ℝ)^(k-1))*
          ((T+1 : ℕ) : ℝ)+4*(L*(N : ℝ)^(k-1)))) =
        4*(k : ℝ)*((N : ℝ)⁻¹*(N : ℝ)^(k-1))*
          (2*(k : ℝ)*((T+1 : ℕ) : ℝ)+L) by ring,hpower]
    _ ≤ 4*(k : ℝ)*(N : ℝ)^(k-2)*
        ((2*(k : ℝ)*A*D+L)*(N : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = C*(N : ℝ)^((k : ℝ)-2+ε) := by
      dsimp [C]
      rw [Real.rpow_add hNR,show (k : ℝ)-2=((k-2 : ℕ) : ℝ) by
        rw [Nat.cast_sub hk]; norm_num]
      rw [Real.rpow_natCast]
      ring

#print axioms reciprocal_sum_dyadic
#print axioms reciprocal_average_bound
end Waring.CriticalVMVTMinorSpacing
