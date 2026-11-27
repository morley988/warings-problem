import WaringLinear.CubicArchRounding
import WaringLinear.CubicResidueSix
import WaringLinear.CubicTernaryPairing
import WaringLinear.PositiveRoots

/-! Seven norm-bounded cubes represent all sufficiently large eligible
integers in a totally imaginary number field. The roots are nonzero after unused summands are removed. -/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
open WaringSiegel WaringSiegel.WSL2 WaringLinear.CubicArchRounding

namespace WaringLinear.CubicImaginary

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

theorem bounded_residual (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : ℝ) (_ : 1 ≤ S) (ν : 𝓞 K),
      Eligible 3 ν → ‖embed K ν‖ ≤ B*S^27 →
      ∃ a b c y : 𝓞 K, ν=a^3+b^3+c^3+6*y ∧
        ‖embed K a‖ ≤ C*S^9 ∧ ‖embed K b‖ ≤ C*S^9 ∧
        ‖embed K c‖ ≤ C*S^9 ∧ ‖embed K y‖ ≤ C*S^9 := by
  obtain ⟨D,hD,hcover⟩ := covering K
  let B₁ := 3*D*(B+D)^2
  let B₂ := 3*D*(B₁+D)^2
  let B₃ := 3*D*(B₂+D)^2
  have next_ge {b : ℝ} (hb : 1≤b) : 1≤3*D*(b+D)^2 := by
    calc
      (1:ℝ) ≤ 3*1*(1+1)^2 := by norm_num
      _ ≤ _ := by gcongr
  have h₁ : 1 ≤ B₁ := next_ge hB
  have h₂ : 1 ≤ B₂ := next_ge h₁
  have h₃ : 1 ≤ B₃ := next_ge h₂
  let C := B+B₁+B₂+B₃+3*D
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro S hS ν he hn
  obtain ⟨t₁,t₂,t₃,hres⟩ := CubicResidueSix.residue_three_cubes he
  obtain ⟨m₁,ha,hr₁⟩ := round_step hD hcover hB hS 9 ν t₁ hn
  let a := t₁+6*m₁
  change ‖embed K (ν-a^3)‖ ≤ B₁*S^18 at hr₁
  obtain ⟨m₂,hb,hr₂⟩ := round_step hD hcover h₁ hS 6 (ν-a^3) t₂ hr₁
  let b := t₂+6*m₂
  change ‖embed K (ν-a^3-b^3)‖ ≤ B₂*S^12 at hr₂
  obtain ⟨m₃,hc,hr₃⟩ := round_step hD hcover h₂ hS 4 (ν-a^3-b^3) t₃ hr₂
  let c := t₃+6*m₃
  change ‖embed K (ν-a^3-b^3-c^3)‖ ≤ B₃*S^8 at hr₃
  obtain ⟨y,hy⟩ := CubicResidueSix.preserve_residue hres m₁ m₂ m₃
  change ν-a^3-b^3-c^3=6*y at hy
  rw [hy] at hr₃
  have hsmul : (6:ℝ) • embed K y = embed K (6*y) := by rw [map_mul,map_ofNat,Algebra.smul_def,map_ofNat]
  rw [← hsmul,_root_.norm_smul] at hr₃
  norm_num at hr₃
  refine ⟨a,b,c,y,by linear_combination hy,?_,?_,?_,?_⟩
  · exact ha.trans (by gcongr; dsimp [C]; linarith)
  · exact hb.trans (by gcongr <;> dsimp [C] <;> linarith)
  · exact hc.trans (by gcongr <;> dsimp [C] <;> linarith)
  · have hy' : ‖embed K y‖ ≤ B₃*S^8 := by linarith [norm_nonneg (embed K y)]
    exact hy'.trans (by gcongr <;> dsimp [C] <;> linarith)

def CubeWord (s : ℕ) (ν : 𝓞 K) (R : ℝ) : Prop :=
  ∃ x : Fin s → 𝓞 K, ∑ i, (x i)^3=ν ∧ ∀ i, ‖embed K (x i)‖ ≤ R

theorem transport (s : ℕ) (hword : ∀ B : ℝ, 1≤B →
    ∃ C : ℝ, 1≤C ∧ ∀ (S : ℝ) (_ : 1≤S) (ν : 𝓞 K),
      Eligible 3 ν → ‖embed K ν‖ ≤ B*S^27 → CubeWord s ν (C*S^9)) :
    WaringSiegelBound K 3 s := by
  obtain ⟨B,hB,hbal⟩ := exists_positive_unit_balance_integer K 3 (by decide)
  obtain ⟨C,hC,hwords⟩ := hword B hB
  let d := Module.finrank ℚ K
  refine ⟨C^d, pow_pos (by linarith) _, 1, zero_lt_one, ?_⟩
  intro ν _ hel hlarge
  have hn : ν≠0 := by rintro rfl; norm_num [absNorm] at hlarge
  obtain ⟨u,hu,hplaces⟩ := hbal ν hn
  let μ := (u : 𝓞 K)^3*ν
  let S := rootScale 27 ν
  have hS : 1 ≤ S := Real.one_le_rpow hlarge.le (by positivity)
  have hμ : ‖embed K μ‖ ≤ B*S^27 := by
    rw [show S^27=normScale ν from rootScale_pow 27 (by decide) ν]
    apply (mixed_norm_le_iff _ _).mpr
    intro w
    change normAtPlace w (mixedEmbedding K (μ : K)) ≤ _
    rw [normAtPlace_apply]
    exact (hplaces w).2
  have hμe : Eligible 3 μ := eligible_mul_power hel (u : 𝓞 K)
  obtain ⟨x,hx,hs⟩ := hwords S hS μ hμe hμ
  apply (representable_unit_pow_iff u hu 3 s (C^d) ν).mp
  refine ⟨s,le_rfl,x,?_,hx,?_⟩
  · intro i σ
    have hpos : TotallyPositive (x i) := (totallyPositive_iff_mixedPositive _).mpr (by
      intro w
      exact False.elim ((InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.1)) w.2))
    exact (hpos σ).le
  · intro i
    rw [absNorm_unit_pow_mul]
    have hSexp : (S^9)^d = absNorm ν ^ (1 / (3:ℝ)) := by
      rw [← pow_mul,Nat.mul_comm 9 d,pow_mul]
      change (rootScale 27 ν^Module.finrank ℚ K)^9=_
      rw [rootScale_pow_degree 27 (by decide), ← Real.rpow_natCast, ← Real.rpow_mul (absNorm_nonneg ν)]
      norm_num
    calc
      absNorm (x i) = NumberField.mixedEmbedding.norm (embed K (x i)) := (mixedNorm_integer _).symm
      _ ≤ ‖embed K (x i)‖^d := mixed_productNorm_le_norm_pow _
      _ ≤ (C*S^9)^d := pow_le_pow_left₀ (norm_nonneg _) (hs i) _
      _ = _ := by rw [mul_pow,hSexp]; norm_num

set_option maxHeartbeats 2000000 in
/-- Unconditional global Waring–Siegel bound in degree three over every totally imaginary
number field. The norm constant is uniform in the eligible target. -/
theorem seven_cubes (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    WaringSiegelBound K 3 7 := by
  apply transport
  intro B hB
  obtain ⟨C,hC,hres⟩ := bounded_residual (K:=K) B hB
  let D := C+‖embed K 1‖
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg (embed K 1)]
  refine ⟨D,hD,?_⟩
  intro S hS ν he hn
  obtain ⟨a,b,c,y,hy,ha,hb,hc,hyb⟩ := hres S hS ν he hn
  let X : Fin 7 → 𝓞 K := ![a,b,c,y+1,y-1,-y,-y]
  refine ⟨X,?_,?_⟩
  · simp [X,Fin.sum_univ_succ]
    linear_combination CubicTernaryPairing.four_signed_cubes y - hy
  · have hbase : C*S^9 ≤ D*S^9 := by
      gcongr; dsimp [D]; linarith [norm_nonneg (embed K 1)]
    have hplus : ‖embed K (y+1)‖ ≤ D*S^9 := by
      rw [map_add]
      refine (norm_add_le _ _).trans ?_
      dsimp [D]; nlinarith [mul_nonneg (norm_nonneg (embed K 1))
        (sub_nonneg.mpr (one_le_pow₀ (n:=9) hS))]
    have hminus : ‖embed K (y-1)‖ ≤ D*S^9 := by
      rw [map_sub]
      refine (norm_sub_le _ _).trans ?_
      dsimp [D]; nlinarith [mul_nonneg (norm_nonneg (embed K 1))
        (sub_nonneg.mpr (one_le_pow₀ (n:=9) hS))]
    have hneg : ‖embed K (-y)‖ ≤ D*S^9 := by simpa using hyb.trans hbase
    intro i
    have ha' := ha.trans hbase
    have hb' := hb.trans hbase
    have hc' := hc.trans hbase
    fin_cases i <;> dsimp [X] <;> assumption

/-- The seven summands may all be taken nonzero, with the same norm bound. -/
theorem seven_positive_cubes (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℝ, 0<N₀ ∧ ∀ ν : 𝓞 K, TotallyPositive ν →
      Eligible 3 ν → N₀<absNorm ν → PositiveRepresentation 3 7 C ν := by
  obtain ⟨C,hC,N₀,hN,h⟩ := seven_cubes K
  exact ⟨C,hC,N₀,hN,fun ν hp he hd =>
    (positiveRepresentation_iff 3 7 (by decide) C ν).mpr (h ν hp he hd)⟩

#print axioms seven_cubes
#print axioms seven_positive_cubes
end WaringLinear.CubicImaginary
