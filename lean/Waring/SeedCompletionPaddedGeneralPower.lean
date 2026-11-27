import Waring.SeedCompletionPaddedHigherPower
import Waring.SeedCompletionPaddedDivisorPower
import Waring.SeedCompletionPaddedSharpDivisorPower
import Waring.SeedCompletionPaddedSharpSecondPower

/-! # All dyadic moments from the literal padded second moments

The loss in the second-moment estimates is retained unchanged.  In particular,
the transport itself does not assume a special residual polynomial degree.
-/

noncomputable section
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionSourceBounds SeedCompletionNaturalBox
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorBoxRanges

def dyadicExponent (n : ℕ) (A δ : ℝ) : ℝ :=
  (2:ℝ)^(n+1)-((n:ℝ)+1)+((2:ℝ)^(n+1)-1)*A+δ

theorem padded_dyadic_power_of_seconds {k j : ℕ} (n r : ℕ)
    {D δ : ℝ} (hD : 1≤D) (φ : Fin j→ℝ)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hbase : ∀ t≤n, ∀ E : ℝ, 1≤E →
      SourcePowerBound (paddedMoment k (r+t) 1 E φ)
        (1+parameterExponent k φ+((r+t:ℕ):ℝ)+δ)) :
    SourcePowerBound (paddedMoment k r (2^n) D φ)
      (dyadicExponent n (parameterExponent k φ+(r:ℝ)) δ) := by
  induction n generalizing r D with
  | zero =>
      convert hbase 0 (by omega) D hD using 1 <;> norm_num [dyadicExponent] <;> ring
  | succ n ih =>
      have hcur := ih r hD (fun t ht E hE=>hbase t (by omega) E hE)
      have hnext : SourcePowerBound (paddedMoment k (r+1) (2^n) (2*D) φ)
          (dyadicExponent n (parameterExponent k φ+((r+1:ℕ):ℝ)) δ) := by
        apply ih (r+1) (by linarith)
        intro t ht E hE
        simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
          hbase (t+1) (by omega) E hE
      have H := padded_double_power hD φ hφ hshift hcur hnext
      have hp : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
      have heq : 2*(2^n:ℕ)=2^(n+1) := by simp [pow_succ,Nat.mul_comm]
      rw [heq] at H
      apply H.weaken
      apply max_le
      · simp only [dyadicExponent,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,
          Nat.cast_one,pow_succ]
        nlinarith only [hp]
      · simp only [dyadicExponent,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,
          Nat.cast_one,pow_succ]
        nlinarith only [hp]

theorem padded_dyadic_power {k j r n : ℕ} (hk : k≤18)
    (hjk : j+(r+n)<k) (hj : 1≤j) (hJ : 2≤(k-(j+(r+n)))/2)
    (hjJ : j≤(k-(j+(r+n)))/2+1) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hφ1 : ∀ i,φ i≤1)
    (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r (2^n) D φ)
      (dyadicExponent n (parameterExponent k φ+(r:ℝ)) (curveLoss φ)) := by
  apply padded_dyadic_power_of_seconds n r hD φ hφ hshift
  intro t ht E hE
  have hmon : (k-(j+(r+n)))/2≤(k-(j+(r+t)))/2 :=
    Nat.div_le_div_right (by omega)
  exact padded_second_power hk (by omega) hj (hJ.trans hmon)
    (hjJ.trans (by omega)) hE φ hφ hφ1 hshift

open SeedCompletionDivisorPowerScales PolicyCompletionSharpResidualSource

theorem padded_dyadic_divisor_power {k j r n : ℕ} (hk : k≤18)
    (hjk : j+(r+n)+2≤k) (hj : 1≤j) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hφ1 : ∀ i,φ i≤1)
    (hshift : ∀ i,0≤shiftExponents k φ i) (hprefix : PrefixCondition k φ) :
    SourcePowerBound (paddedMoment k r (2^n) D φ)
      (dyadicExponent n (parameterExponent k φ+(r:ℝ)) (curveLoss φ)) := by
  apply padded_dyadic_power_of_seconds n r hD φ hφ hshift
  intro t ht E hE
  exact padded_second_divisor_power hk (by omega) hj hE φ hφ hφ1 hshift hprefix

theorem padded_dyadic_sharp_power {k j r n : ℕ} (hk : k≤18)
    (hjk : j+(r+n)<k) (hj : 1≤j) (hJ : 2≤(k-(j+(r+n)))/2)
    (hjJ : j≤(k-(j+(r+n)))/2+1)
    (hgood : ∀ t≤n,SharpResidual k (j+(r+t))) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hφ1 : ∀ i,φ i≤1)
    (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r (2^n) D φ)
      (dyadicExponent n (parameterExponent k φ+(r:ℝ)) 0) := by
  apply padded_dyadic_power_of_seconds n r hD φ hφ hshift
  intro t ht E hE
  have hmon : (k-(j+(r+n)))/2≤(k-(j+(r+t)))/2 :=
    Nat.div_le_div_right (by omega)
  simpa only [add_zero] using padded_second_sharp_power hk (by omega) hj (hgood t ht)
    (hJ.trans hmon) (hjJ.trans (by omega)) hE φ hφ hφ1 hshift

theorem padded_dyadic_sharp_divisor_power {k j r n : ℕ} (hk : k≤18)
    (hjk : j+(r+n)+2≤k) (hj : 1≤j)
    (hgood : ∀ t≤n,SharpResidual k (j+(r+t))) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hφ1 : ∀ i,φ i≤1)
    (hshift : ∀ i,0≤shiftExponents k φ i) (hprefix : PrefixCondition k φ) :
    SourcePowerBound (paddedMoment k r (2^n) D φ)
      (dyadicExponent n (parameterExponent k φ+(r:ℝ)) 0) := by
  apply padded_dyadic_power_of_seconds n r hD φ hφ hshift
  intro t ht E hE
  simpa only [add_zero] using padded_second_sharp_divisor_power hk (by omega) hj
    (hgood t ht) hE φ hφ hφ1 hshift hprefix

#print axioms padded_dyadic_power_of_seconds
#print axioms padded_dyadic_power
#print axioms padded_dyadic_divisor_power
#print axioms padded_dyadic_sharp_power
#print axioms padded_dyadic_sharp_divisor_power
end Waring.SeedCompletionPaddedSource
