import WaringLinear.PositiveRoots
import Waring.Representation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic

/-! # The classical positive Waring predicate over the rational field -/
noncomputable section
open scoped NumberField BigOperators
open WaringSiegel
namespace WaringLinear

theorem rational_integer_norm (n : ℕ) : absNorm (n:𝓞 ℚ)=(n:ℝ) := by
  have hd : Module.finrank ℤ (𝓞 ℚ)=1 :=
    Rat.ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.finrank_eq.trans (Module.finrank_self ℤ)
  unfold absNorm
  rw [show (n:𝓞 ℚ)=algebraMap ℤ (𝓞 ℚ) (n:ℤ) by simp,Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis ℚ),
    ←Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis ℚ),hd,pow_one]
  simp

theorem natural_eligible (K : Type*) [Field K] [NumberField K] (k n : ℕ) :
    Eligible k (n:𝓞 K) := by
  have hone : (1:𝓞 K)∈powerSubgroup k :=
    AddSubgroup.subset_closure (Set.mem_range.mpr ⟨1,one_pow k⟩)
  simpa only [nsmul_one] using (powerSubgroup k).nsmul_mem hone n

/-- Over Q the integral norm and strict positivity give exactly natural
positive roots. The fixed-field global threshold therefore gives the
classical eventual representation predicate. -/
theorem classical_of_rational_field (k s : ℕ) (hk : k≠0) (bound : WaringSiegelBound ℚ k s) :
    Waring.WaringBound k s := by
  obtain ⟨C,_,M,hM,H⟩ := bound
  refine ⟨⌈M⌉₊+1,?_⟩
  intro n hn
  have hn' : M<(n:ℝ) := (Nat.le_ceil M).trans_lt (by exact_mod_cast (show ⌈M⌉₊<n by omega))
  have hpos : TotallyPositive (n:𝓞 ℚ) := by
    intro σ
    have hnpos : 0<n := by omega
    change 0 < σ ((algebraMap (𝓞 ℚ) ℚ) (n:𝓞 ℚ))
    simpa only [map_natCast] using (Nat.cast_pos (α:=ℝ)).2 hnpos
  obtain ⟨t,ht,z,hz,hs,_⟩ := (positiveRepresentation_iff k s hk C (n:𝓞 ℚ)).2
    (H n hpos (natural_eligible ℚ k n) (by simpa only [rational_integer_norm] using hn'))
  have hp (i : Fin t) : 0<Rat.ringOfIntegersEquiv (z i) := by
    have Hr := (hz i).2 (algebraMap ℚ ℝ)
    change (0:ℝ)<((z i:ℚ):ℝ) at Hr
    have Hq : (0:ℚ)<(z i:ℚ) := by exact_mod_cast Hr
    change (0:ℚ)<algebraMap (𝓞 ℚ) ℚ (z i) at Hq
    rw [←Rat.coe_ringOfIntegersEquiv] at Hq
    exact_mod_cast Hq
  refine ⟨t,ht,fun i => (Rat.ringOfIntegersEquiv (z i)).toNat,fun i => Int.pos_iff_toNat_pos.mp (hp i),?_⟩
  have HH := congrArg Rat.ringOfIntegersEquiv hs
  simp only [map_sum,map_pow,map_natCast] at HH
  exact_mod_cast (show (∑ i, (((Rat.ringOfIntegersEquiv (z i)).toNat:ℕ):ℤ)^k)=(n:ℤ) by
    simpa only [Int.toNat_of_nonneg (le_of_lt (hp _))] using HH)

#print axioms classical_of_rational_field
end WaringLinear
