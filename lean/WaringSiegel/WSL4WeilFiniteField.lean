import WaringSiegel.WSL4WeilTraceCharacters
import WaringSiegel.WSL4WeilWeilBound

/-! # WSL4: the polynomial Weil bound over every finite field

The upstream prime-field endpoint is strengthened here to an arbitrary finite
field.  Orthogonality represents every additive character as a scaled trace
character.  The weak Stepanov estimate therefore applies over every extension
of the base field, and the checked power-sum transfer removes its constant.
-/

noncomputable section
namespace WaringSiegel.WSL4Weil
open Polynomial Finset

theorem norm_sum_addChar_eval_weak
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {f : F[X]}
    (hm : 1 ≤ f.natDegree) (hpm : ¬p ∣ f.natDegree) (h5 : 5 ≤ Fintype.card F) :
    ‖∑ x : F, ψ (f.eval x)‖ ≤ 4 * p * f.natDegree * √(Fintype.card F) := by
  obtain ⟨a, ha, hrep⟩ := exists_nonzero_trace_mul_representation p hψ
  have hd : (C a * f).natDegree = f.natDegree :=
    natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha) f
  have hb := norm_sum_addChar_trace_le (p := p) stdAddChar_ne_one
    (f := C a * f) (by rwa [hd]) (by rwa [hd]) h5
  simpa only [eval_mul, eval_C, hd, ← hrep] using hb

theorem norm_lPowerSum_finiteField_le
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {f : F[X]}
    (hm : 1 ≤ f.natDegree) (hpm : ¬p ∣ f.natDegree) {d : ℕ} (hd : 3 ≤ d) :
    ‖lPowerSum (addWeight ψ f) d‖ ≤
      4 * p * f.natDegree * √(Fintype.card F) ^ d := by
  letI : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp inferInstance
  letI : NeZero d := ⟨by omega⟩
  let E := Extension F p d
  letI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card F ^ d := by
    rw [← Nat.card_eq_fintype_card, natCard_extension, Nat.card_eq_fintype_card]
  have h5 : 5 ≤ Fintype.card E := by
    rw [hcard]
    calc
      5 ≤ 2 ^ 3 := by norm_num
      _ ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_left (Fintype.one_lt_card (α := F)) 3
      _ ≤ Fintype.card F ^ d := Nat.pow_le_pow_right Fintype.card_pos hd
  have hS := sum_addChar_trace_aeval (L := E) ψ f
  rw [finrank_extension] at hS
  have hb := norm_sum_addChar_eval_weak p
    (additiveCharacter_trace_ne_one (L := E) hψ)
    (f := f.map (algebraMap F E))
    (by rwa [natDegree_map]) (by rwa [natDegree_map]) h5
  simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
    eval_map_algebraMap, natDegree_map] at hb
  rw [← hS]
  refine hb.trans_eq ?_
  rw [hcard, Nat.cast_pow, sqrt_pow_eq_pow_sqrt (Nat.cast_nonneg _)]

theorem lCoeff_finiteField_addWeight_eq_zero
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {f : F[X]}
    (hm : 1 ≤ f.natDegree) (hpm : ¬p ∣ f.natDegree) (n : ℕ) (hn : f.natDegree ≤ n) :
    lCoeff (addWeight ψ f) n = 0 := by
  letI : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp inferInstance
  exact lCoeff_eq_zero hψ (by omega)
    (fun h => hpm ((CharP.cast_eq_zero_iff F p f.natDegree).mp h)) hn

/-- Weil's polynomial additive-character estimate over an arbitrary finite field. -/
theorem norm_sum_addChar_eval_finiteField_le
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {f : F[X]}
    (hm : 1 ≤ f.natDegree) (hpm : ¬p ∣ f.natDegree) :
    ‖∑ x : F, ψ (f.eval x)‖ ≤
      ((f.natDegree : ℝ) - 1) * √(Fintype.card F) := by
  have h1 := sum_addChar_trace_aeval (L := F) ψ f
  rw [Module.finrank_self] at h1
  simp only [Algebra.trace_self, LinearMap.id_apply, coe_aeval_eq_eval] at h1
  rw [h1]
  exact norm_lPowerSum_one_le (isMonicMul_addWeight ψ f) hm
    (lCoeff_finiteField_addWeight_eq_zero p hψ hm hpm)
    (Real.sqrt_nonneg _) (n₀ := 3) fun _ hd =>
      norm_lPowerSum_finiteField_le p hψ hm hpm hd

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.norm_sum_addChar_eval_weak
#print axioms WaringSiegel.WSL4Weil.norm_lPowerSum_finiteField_le
#print axioms WaringSiegel.WSL4Weil.norm_sum_addChar_eval_finiteField_le
