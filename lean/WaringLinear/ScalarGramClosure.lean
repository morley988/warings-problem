import WaringLinear.ScalarUnitOccupancy
import WaringLinear.ScalarDivisorBlocks

/-! # The complete rational Gram reduction to individual large-conductor sums -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear

/-- For a coprime box the only analytic input to a Gram fibre is the
bound on ordinary complete coprime-interval exponential sums at reduced
rational points of denominator exceeding N. The small moduli, including
the coprimality adjustment and exact Möbius factor, are handled here. -/
theorem scalar_gram_from_rational_sums
    (box s:Finset ℕ) (hs:s⊆box) (q k N : ℕ) (hq:0<q) (hodd:¬2∣q) (hk:0<k)
    (hN:1≤N) (hb:∀n∈box,1≤n ∧ n≤N) (hunit:∀n∈box,n.Coprime q)
    (E z σ : ℝ) (hE:0≤E) (hz:0≤z) (hslack:32*E≤(N:ℝ)^(σ-2*z))
    (hhigh:∀r:ℕ, r∣q → N<r → ∀a<r,a.Coprime r →
      ‖scalarPowerSum box k ((a/r:ℝ):ScalarTorus)‖≤E*(N:ℝ)^(1-σ))
    (x:ScalarTorus) :
    scalarFibreMass q hq N z (scalarPowerSum s k) x ≤
      ((18+8*z*Real.logb 2 N)*((q.divisors.card:ℝ)^2*(2*(k:ℝ)^q.primeFactors.card)))*(N:ℝ)^2 := by
  classical
  have hN' : 1≤(N:ℝ) := by exact_mod_cast hN
  have hc : (box.card:ℝ)≤N := by
    apply Nat.cast_le.mpr
    have hh : box⊆Finset.Icc 1 N := fun n hn => Finset.mem_Icc.mpr (hb n hn)
    simpa using Finset.card_le_card hh
  apply scalar_fibre_from_conductors box s hs q k N hq N _ E z σ hN' (by positivity)
    hE hz hc hslack _ _ x
  · intro d hd hM t w
    have hd0 : d≠0 := (Nat.pos_of_dvd_of_pos hd hq).ne'
    letI : NeZero d := ⟨hd0⟩
    have ord (r:ZMod d) := scalar_power_occupancy box N d k (fun n hn => (hb n hn).2)
      (fun n hn => (ZMod.isUnit_iff_coprime n d).mpr ((hunit n hn).coprime_dvd_right hd))
      (fun h => hodd (h.trans hd)) hk r
    have H := scalar_divisible_gram_bound (fun a:t => a.1.val)
      (fun i j h => Subtype.ext (Subtype.ext h)) box k d _ ord w
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have fac : d.primeFactors⊆q.primeFactors := by
      intro p hp
      obtain ⟨pp,pd,_⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨pp,pd.trans hd,hq.ne'⟩
    have le := Nat.pow_le_pow_right (n:=k) hk (Finset.card_le_card fac)
    have count : ((N/d+1)*k^d.primeFactors.card)*d≤(2*k^q.primeFactors.card)*N := by
      calc
        _ = (N/d*d+d)*k^d.primeFactors.card := by ring
        _ ≤ (N+N)*k^q.primeFactors.card :=
          Nat.mul_le_mul (Nat.add_le_add (Nat.div_mul_le_self ..) hM) le
        _ = _ := by ring
    exact_mod_cast count
  · intro a b h
    let v := a.val-b.val
    change ‖scalarPowerSum box k v‖≤_
    let r := addOrderOf v
    have hr : r∣q := kernel_difference_order_dvd q a b
    have hr0 := Nat.pos_of_dvd_of_pos hr hq
    obtain ⟨j,hj,hg,he⟩ := (AddCircle.addOrderOf_eq_pos_iff (u:=v) hr0).mp rfl
    have he' : ((j/r:ℝ):ScalarTorus)=v := by simpa only [mul_one] using he
    rw [←he']
    exact hhigh r hr h j hj hg

#print axioms scalar_gram_from_rational_sums
end WaringLinear
