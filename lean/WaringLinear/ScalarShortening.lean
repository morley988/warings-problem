import WaringLinear.ScalarGramClosure

/-! # The marked scalar shortening step, with arithmetic low conductors discharged -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace WaringLinear

def coprimeBox (N m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => n.Coprime m

/-- An explicit single step on the actual circle. Its high-denominator
input concerns only the complete length-N coprime-interval polynomial
at a/q with gcd(a,q)=1, where q divides the kth power of the designated
mark. There are no small-conductor Gram, divisor multiplicity, or
Haar-volume assumptions. -/
theorem classical_conductor_shortening
    (s marks bad : Finset ℕ) (mark : ℕ→ℕ) (k N R : ℕ)
    (hk : 0<k) (hN : 1≤N) (hbox : ∀n∈s,1≤n ∧ n≤N)
    (hc : ∀n∈s,mark n∈marks) (hdv : ∀n∈s,mark n∣n)
    (hm : ∀ i ∈ marks, 0 < i) (hd : ∀ j ∈ bad, 0 < j)
    (hsq : ∀ i∈marks,Squarefree i) (hodd : ∀i∈marks,¬2∣i)
    (hR : ∀i∈marks,i.primeFactors.card≤R)
    (hbadSet : ∀i∈marks,∀t⊆i.primeFactors,t.Nonempty → (∏q∈t,q)∈bad)
    (p h z θ D E A L P C Z err σ : ℝ)
    (hp : 1≤p) (hh : 0<h) (hhp : h<p+2)
    (hD : 0≤D) (hL : 0≤L) (hP : 0≤P) (hC : 0≤C) (hz:0≤z) (herr:0≤err)
    (hmass : (∑i∈marks,(i:ℝ)⁻¹)≤1) (hsize : ∀i∈marks,(N:ℝ)^θ≤(i:ℝ))
    (hslack : 32*err≤(N:ℝ)^(σ-2*z))
    (hhigh : ∀i∈marks,∀r:ℕ, r∣i^k → N<r → ∀a<r,a.Coprime r →
      ‖scalarPowerSum (coprimeBox N i) k ((a/r:ℝ):ScalarTorus)‖ ≤ err*(N:ℝ)^(1-σ))
    (hlow : (∫x,‖scalarPowerSum s k x‖^h)≤L*(N:ℝ)^(h-(k:ℝ)+E))
    (hshort : ∀i∈marks,(∫x,‖scalarPowerSum (scalarChild s mark i) k x‖^p)
      ≤C*((N:ℝ)/i)^(p-(k:ℝ)+D))
    (hexcept : ∀j∈bad,(∫x,‖scalarPowerSum (dividedState s j) k x‖^(p+2))
      ≤P*((N:ℝ)/j)^(p+2-(k:ℝ)+A))
    (hZ : (∑j∈bad,((j:ℝ)^(p+2-(k:ℝ)+A))⁻¹)≤Z)
    (hAh : E-(p+2-h)*z≤A) (hAD : (1-θ)*D≤A) :
    let B := (18+8*z*Real.logb 2 N)*(((1+(k:ℝ))^R)^2*(2*(k:ℝ)^R))
    let D₀ := 2*(2:ℝ)^R
    (∫x,‖scalarPowerSum s k x‖^(p+2))≤(L+4*B*C+D₀^(p+2)*(P*Z))*(N:ℝ)^(p+2-(k:ℝ)+A) := by
  classical
  let B := (18+8*z*Real.logb 2 N)*(((1+(k:ℝ))^R)^2*(2*(k:ℝ)^R))
  let D₀ := 2*(2:ℝ)^R
  let mask (i:marks) := i.val.primeFactors
  have hNp : 1≤(N:ℝ) := by exact_mod_cast hN
  have log0 := Real.logb_nonneg (show (1:ℝ)<2 by norm_num) hNp
  have pref : 0≤18+8*z*Real.logb 2 N := by positivity
  have hB : 0≤B := mul_nonneg pref (by positivity)
  apply classical_marked_conductor_step s marks bad mark mask k hc hdv hm hd
    (fun i q hq => Nat.prime_of_mem_primeFactors hq) (fun i=>hbadSet i.val i.property)
    N p h z θ D E A L P B C D₀ Z hNp hp hh hhp hD hL hP hB hC (by positivity)
    hmass hsize _ _ hlow hshort hexcept hZ hAh hAD
  · intro i
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (hR _ i.property)
  · intro i x
    let m := i.val
    have hm0 : 0<m := hm _ i.property
    have sub : scalarCoprime s (mask i)⊆coprimeBox N m := by
      intro n hn
      obtain ⟨hs,hcop⟩ := Finset.mem_filter.mp hn
      have cop : n.Coprime m := by
        by_contra hnc
        obtain ⟨q,hq,hqn,hqm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
        exact hcop q (Nat.mem_primeFactors.mpr ⟨hq,hqm,hm0.ne'⟩) hqn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hbox _ hs),cop⟩
    have hb (n:ℕ) (hn:n∈coprimeBox N m) := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hu (n:ℕ) (hn:n∈coprimeBox N m) : n.Coprime (m^k) :=
      ((Finset.mem_filter.mp hn).2).pow_right k
    have odd : ¬ 2∣m^k := fun h => hodd _ i.property (Nat.prime_two.dvd_of_dvd_pow h)
    have H := scalar_gram_from_rational_sums (coprimeBox N m) _ sub (m^k) k N (pow_pos hm0 _) odd hk hN hb hu
      err z σ herr hz hslack (hhigh _ i.property) x
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ pref
    have hR' : m.primeFactors.card≤R := hR _ i.property
    have hdiv : (((m^k).divisors.card:ℕ):ℝ)≤(1+(k:ℝ))^R := by
      calc
        _ ≤ ((k:ℝ)+1)^m.primeFactors.card := by exact_mod_cast squarefree_power_divisor_count m k (hsq _ i.property)
        _ ≤ _ := by rw [add_comm (k:ℝ) 1]; exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg k)) hR'
    have hpow : (k:ℝ)^(m^k).primeFactors.card≤(k:ℝ)^R := by
      rw [Nat.primeFactors_pow _ hk.ne']
      exact pow_le_pow_right₀ (by exact_mod_cast hk) hR'
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hdiv 2)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity) (by positivity)

#print axioms classical_conductor_shortening
end WaringLinear
