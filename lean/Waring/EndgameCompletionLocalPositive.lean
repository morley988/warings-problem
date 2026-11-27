import Waring.EndgameCompletionSingularPrimeLocal

/-! # Uniform positive prime-power densities for product variables -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace Waring.EndgameCompletion
open LocalSolubility

def productLocalDensity (q k u v L : ℕ) [NeZero q] (n : ℤ) : ℝ :=
  (q : ℝ)*(productPowerSolutions k u v L q n).card/(q : ℝ)^(u+(L+1)*v)

theorem fullProductSingularCoefficient_eq_density (q k u v L : ℕ) [NeZero q] (n : ℤ) :
    fullProductSingularCoefficient q k u v (L+1) n=(productLocalDensity q k u v L n : ℂ) := by
  rw [fullProductSingularCoefficient_eq_count]
  simp [productLocalDensity]

theorem productLocalDensity_nonneg (q k u v L : ℕ) [NeZero q] (n : ℤ) :
    0≤productLocalDensity q k u v L n := by unfold productLocalDensity; positivity

def primeDensityLower (p s m d : ℕ) : ℝ :=
  (p : ℝ)^d*(Nat.totient (p^d) : ℝ)^m/((p : ℝ)^d)^(s+m)

theorem primeDensityLower_pos {p : ℕ} (hp : 0<p) (s m d : ℕ) :
    0<primeDensityLower p s m d := by
  have ht : (0 : ℝ)<Nat.totient (p^d) := by exact_mod_cast Nat.totient_pos.mpr (pow_pos hp d)
  unfold primeDensityLower
  positivity

theorem totient_prime_add {p : ℕ} (hp : p.Prime) (r d : ℕ) (hd : 0<d) :
    Nat.totient (p^(r+d))=p^r*Nat.totient (p^d) := by
  rw [Nat.totient_prime_pow hp (by omega),Nat.totient_prime_pow hp hd,
    show r+d-1=r+(d-1) by omega,pow_add]
  ring

theorem primeDensity_scale {p : ℕ} (hp : p.Prime) (s m d r : ℕ) (hs : 0<s) (hd : 0<d) :
    (p^(r+d) : ℝ)*(p : ℝ)^((s-1)*r)*(Nat.totient (p^(r+d)) : ℝ)^m/
      ((p : ℝ)^(r+d))^(s+m)=primeDensityLower p s m d := by
  let A : ℝ := (p : ℝ)^r
  let B : ℝ := (p : ℝ)^d
  let C : ℝ := (Nat.totient (p^d) : ℝ)
  have hA : A≠0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hq : (p : ℝ)^(r+d)=A*B := by rw [pow_add]
  have hpow : (p : ℝ)^((s-1)*r)=A^(s-1) := by simp only [A,← pow_mul,mul_comm r]
  have ht : (Nat.totient (p^(r+d)) : ℝ)=A*C := by
    rw [totient_prime_add hp r d hd,Nat.cast_mul,Nat.cast_pow]
  rw [hq,hpow,ht,mul_pow,mul_pow]
  have hnum : A*B*A^(s-1)*(A^m*C^m)=A^(s+m)*(B*C^m) := by
    rw [pow_add,show A^s=A*A^(s-1) by rw [← pow_succ',Nat.sub_add_cancel hs]]
    ring
  rw [hnum,mul_div_mul_left _ _ (pow_ne_zero _ hA)]
  rfl

theorem degree8_productLocalDensity_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L r : ℕ) (n : ℤ) :
    primeDensityLower p 38 (L*30) (localDepth8 p)≤
      productLocalDensity (p^(r+localDepth8 p)) 8 8 30 L n := by
  have hd : 0<localDepth8 p := by unfold localDepth8; split_ifs <;> omega
  have hc : (p : ℝ)^(37*r)*(Nat.totient (p^(r+localDepth8 p)) : ℝ)^(L*30)≤
      (productPowerSolutions 8 8 30 L (p^(r+localDepth8 p)) n).card := by
    exact_mod_cast degree8_product_local_count_lower hp L r n
  have hD : 8+(L+1)*30=38+L*30 := by omega
  unfold productLocalDensity
  simp only [hD,Nat.cast_pow]
  rw [← primeDensity_scale hp 38 (L*30) (localDepth8 p) r (by omega) hd]
  apply div_le_div_of_nonneg_right
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  · positivity

theorem degree9_productLocalDensity_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L r : ℕ) (n : ℤ) :
    primeDensityLower p 46 (L*35) (localDepth9 p)≤
      productLocalDensity (p^(r+localDepth9 p)) 9 11 35 L n := by
  have hd : 0<localDepth9 p := by unfold localDepth9; split_ifs <;> omega
  have hc : (p : ℝ)^(45*r)*(Nat.totient (p^(r+localDepth9 p)) : ℝ)^(L*35)≤
      (productPowerSolutions 9 11 35 L (p^(r+localDepth9 p)) n).card := by
    exact_mod_cast degree9_product_local_count_lower hp L r n
  have hD : 11+(L+1)*35=46+L*35 := by omega
  unfold productLocalDensity
  simp only [hD,Nat.cast_pow]
  rw [← primeDensity_scale hp 46 (L*35) (localDepth9 p) r (by omega) hd]
  apply div_le_div_of_nonneg_right
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  · positivity

#print axioms degree8_productLocalDensity_lower
#print axioms degree9_productLocalDensity_lower
end Waring.EndgameCompletion
