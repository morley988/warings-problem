import WaringSiegel.WSL2UnitNodeBoxes
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-! Uniformly approximate archimedean cube roots in a prescribed class modulo
six. After one approximation a height of order S^(3n) becomes S^(2n). -/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel

namespace WaringLinear.CubicArchRounding
variable {K : Type*} [Field K] [NumberField K]

def embed (K : Type*) [Field K] [NumberField K] : 𝓞 K →+* mixedSpace K :=
  (mixedEmbedding K).comp (algebraMap (𝓞 K) K)

theorem covering (K : Type*) [Field K] [NumberField K] :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (v : mixedSpace K) (a : 𝓞 K), ∃ m : 𝓞 K,
      ‖v - embed K (a+6*m)‖ ≤ D := by
  classical
  let b := latticeBasis K
  let M := ∑ i, ‖b i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨6*M+1,by linarith,?_⟩
  intro v a
  let z := (6 : ℝ)⁻¹ • (v-embed K a)
  obtain ⟨m, hm⟩ := (mem_span_latticeBasis K).mp (ZSpan.floor b z).property
  change embed K m = (ZSpan.floor b z : mixedSpace K) at hm
  refine ⟨m, ?_⟩
  have he : v - embed K (a+6*m) = (6:ℝ) • ZSpan.fract b z := by
    rw [ZSpan.fract, ← hm, smul_sub, map_add, map_mul, map_ofNat]
    have hvm : (6:ℝ) • z = v-embed K a := by
      dsimp [z]
      rw [smul_smul]
      norm_num
    rw [hvm]
    have hmul : (6:ℝ) • embed K m = 6 * embed K m := by
      rw [Algebra.smul_def, map_ofNat]
    rw [hmul]
    abel
  rw [he,_root_.norm_smul]
  have h := ZSpan.norm_fract_le b z
  change ‖ZSpan.fract b z‖ ≤ M at h
  norm_num
  linarith

theorem exists_mixed_cuberoot [IsTotallyComplex K] (Y : mixedSpace K) :
    ∃ v : mixedSpace K, v^3 = Y := by
  classical
  choose z hz using fun (w : {v : InfinitePlace K // IsComplex v}) =>
    IsAlgClosed.exists_pow_nat_eq (Y.2 w) (show 0 < 3 by decide)
  refine ⟨(0,z), Prod.ext ?_ ?_⟩
  · funext w
    exact False.elim ((not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2)
  · funext w
    exact hz w

private theorem norm_cube_diff {A : Type*} [NormedCommRing A] (v z : A) :
    ‖v^3-z^3‖ ≤ ‖v-z‖ * (‖v‖^2+‖v‖*‖z‖+‖z‖^2) := by
  rw [show v^3-z^3=(v-z)*(v^2+v*z+z^2) by ring]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖v^2+v*z‖+‖z^2‖ := norm_add_le _ _
    _ ≤ (‖v^2‖+‖v*z‖)+‖z^2‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      rw [pow_two v, pow_two z, pow_two ‖v‖, pow_two ‖z‖]
      exact add_le_add (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (norm_mul_le _ _)

/-- Explicit constants in a single archimedean rounding. -/
theorem round_step [IsTotallyComplex K]
    {D B S : ℝ} (hD : 1 ≤ D)
    (hcover : ∀ (v : mixedSpace K) (a : 𝓞 K), ∃ m : 𝓞 K,
      ‖v-embed K (a+6*m)‖ ≤ D)
    (hB : 1 ≤ B) (hS : 1 ≤ S) (n : ℕ) (Y a : 𝓞 K)
    (hY : ‖embed K Y‖ ≤ B*S^(3*n)) :
    ∃ m : 𝓞 K, ‖embed K (a+6*m)‖ ≤ (B+D)*S^n ∧
      ‖embed K (Y-(a+6*m)^3)‖ ≤ (3*D*(B+D)^2)*S^(2*n) := by
  obtain ⟨v,hv⟩ := exists_mixed_cuberoot (embed K Y)
  have hn : 1 ≤ S^n := one_le_pow₀ hS
  have hB' : 0 ≤ B := by linarith
  have hSn : 0 ≤ S^n := by linarith
  have hbn : 0 ≤ B*S^n := mul_nonneg hB' hSn
  have hb3 : B ≤ B^3 := by nlinarith [mul_self_nonneg (B-1), mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg B)]
  have hvbound : ‖v‖ ≤ B*S^n := by
    apply (mixed_norm_le_iff _ _).mpr
    intro w
    apply le_of_pow_le_pow_left₀ (n:=3) (by decide) hbn
    calc
      (normAtPlace w v)^3 = normAtPlace w (v^3) := (map_pow _ _ _).symm
      _ ≤ ‖embed K Y‖ := hv ▸ normAtPlace_le_mixed_norm _ w
      _ ≤ B*(S^n)^3 := by simpa [←pow_mul,Nat.mul_comm] using hY
      _ ≤ (B*S^n)^3 := by rw [mul_pow]; gcongr
  obtain ⟨m,hm⟩ := hcover v a
  let z := embed K (a+6*m)
  have hz : ‖z‖ ≤ (B+D)*S^n := by
    calc
      _ ≤ ‖v‖+‖v-z‖ := by
        calc
          ‖z‖ = ‖(z-v)+v‖ := by rw [sub_add_cancel]
          _ ≤ ‖z-v‖+‖v‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev,add_comm]
      _ ≤ B*S^n+D := add_le_add hvbound hm
      _ ≤ _ := by nlinarith [mul_nonneg (by linarith : 0≤D) (sub_nonneg.mpr hn)]
  refine ⟨m,hz,?_⟩
  have hv' : ‖v‖ ≤ (B+D)*S^n := hvbound.trans (by nlinarith [mul_nonneg (by linarith : 0≤D) hSn])
  rw [map_sub,map_pow,← hv]
  calc
    _ ≤ ‖v-z‖*(‖v‖^2+‖v‖*‖z‖+‖z‖^2) := norm_cube_diff v z
    _ ≤ D*(((B+D)*S^n)^2+((B+D)*S^n)*((B+D)*S^n)+((B+D)*S^n)^2) := by
      gcongr
    _ = _ := by rw [Nat.mul_comm 2 n,pow_mul]; ring

#print axioms covering
#print axioms round_step
end WaringLinear.CubicArchRounding
