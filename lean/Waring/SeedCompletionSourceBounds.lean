import Waring.RestrictedSmoothUniformity
import Waring.SeedCompletionSmoothDensity

/-!
# Uniform power bounds at every sufficiently small fixed smoothness power

The constants may depend on the chosen positive smoothness exponent, as
they do in the source absorption argument. The upper threshold is chosen
first. This permits simultaneous choices for all lower smooth moments,
coefficient resources and actual recurrence stages. For pure even smooth
moments, the final bound extends to every smaller cutoff by finite counts.
-/

noncomputable section
namespace Waring.SeedCompletionSourceBounds
open SmoothMoments

def SourcePowerBound (F : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ,0 < ε → ∃ η₀ : ℝ,0 < η₀ ∧ ∀ η : ℝ,0 < η → η ≤ η₀ →
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      |F P (P^η)| ≤ C*P^(a+ε)

theorem SourcePowerBound.congr {F G : ℝ → ℝ → ℝ} {a : ℝ}
    (hF : SourcePowerBound F a) (heq : ∀ P R : ℝ,1 ≤ P → 1 ≤ R → F P R=G P R) :
    SourcePowerBound G a := by
  intro ε hε
  obtain ⟨η₀,hη₀,hbound⟩ := hF ε hε
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₀,hP₀,hP⟩ := hbound η hη hηle
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP
  have hP1 : 1 ≤ P := hP₀.trans hPP
  rw [← heq P (P^η) hP1 (Real.one_le_rpow hP1 hη.le)]
  exact hP P hPP

theorem constant (c : ℝ) : SourcePowerBound (fun _ _ => c) 0 := by
  intro ε hε
  refine ⟨1,by norm_num,?_⟩
  intro η hη hηle
  refine ⟨|c|+1,by positivity,1,le_rfl,?_⟩
  intro P hP
  simp only [zero_add]
  have hpow := Real.one_le_rpow hP hε.le
  nlinarith [abs_nonneg c]

theorem ambient_power (a : ℝ) : SourcePowerBound (fun P _ => P^a) a := by
  intro ε hε
  refine ⟨1,by norm_num,?_⟩
  intro η hη hηle
  refine ⟨1,by norm_num,1,le_rfl,?_⟩
  intro P hP
  rw [abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hP) _),one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)

theorem smoothness_power : SourcePowerBound (fun _ R => R) 0 := by
  intro ε hε
  refine ⟨ε,hε,?_⟩
  intro η hη hηle
  refine ⟨1,by norm_num,1,le_rfl,?_⟩
  intro P hP
  rw [abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hP) _),one_mul,zero_add]
  exact Real.rpow_le_rpow_of_exponent_le hP hηle

theorem SourcePowerBound.weaken {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : SourcePowerBound F a) (hab : a ≤ b) : SourcePowerBound F b := by
  intro ε hε
  obtain ⟨η₀,hη₀,hbound⟩ := hF ε hε
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₀,hP₀,hP⟩ := hbound η hη hηle
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP
  exact (hP P hPP).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hP₀.trans hPP) (by linarith)) hC.le)

theorem SourcePowerBound.add {F G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : SourcePowerBound F a) (hG : SourcePowerBound G b) :
    SourcePowerBound (fun P R => F P R+G P R) (max a b) := by
  intro ε hε
  obtain ⟨η₁,hη₁,hF⟩ := hF ε hε
  obtain ⟨η₂,hη₂,hG⟩ := hG ε hε
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₁,hP₁,hF⟩ := hF η hη (hηle.trans (min_le_left _ _))
  obtain ⟨D,hD,P₂,hP₂,hG⟩ := hG η hη (hηle.trans (min_le_right _ _))
  refine ⟨C+D,by positivity,max P₁ P₂,hP₁.trans (le_max_left _ _),?_⟩
  intro P hPP
  have hPP₁ := (le_max_left P₁ P₂).trans hPP
  have hPP₂ := (le_max_right P₁ P₂).trans hPP
  have hP : 1 ≤ P := hP₁.trans hPP₁
  calc
    _ ≤ |F P (P^η)|+|G P (P^η)| := abs_add_le _ _
    _ ≤ C*P^(a+ε)+D*P^(b+ε) := add_le_add (hF P hPP₁) (hG P hPP₂)
    _ ≤ C*P^(max a b+ε)+D*P^(max a b+ε) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP
        (add_le_add_right (le_max_left a b) ε)) hC.le)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP
        (add_le_add_right (le_max_right a b) ε)) hD.le)
    _ = _ := by ring

theorem SourcePowerBound.mul {F G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : SourcePowerBound F a) (hG : SourcePowerBound G b) :
    SourcePowerBound (fun P R => F P R*G P R) (a+b) := by
  intro ε hε
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨η₁,hη₁,hF⟩ := hF (ε/2) hδ
  obtain ⟨η₂,hη₂,hG⟩ := hG (ε/2) hδ
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₁,hP₁,hF⟩ := hF η hη (hηle.trans (min_le_left _ _))
  obtain ⟨D,hD,P₂,hP₂,hG⟩ := hG η hη (hηle.trans (min_le_right _ _))
  refine ⟨C*D,by positivity,max P₁ P₂,hP₁.trans (le_max_left _ _),?_⟩
  intro P hPP
  have hPP₁ := (le_max_left P₁ P₂).trans hPP
  have hPP₂ := (le_max_right P₁ P₂).trans hPP
  have hP : 0 < P := zero_lt_one.trans_le (hP₁.trans hPP₁)
  calc
    _ = |F P (P^η)| * |G P (P^η)| := abs_mul _ _
    _ ≤ (C*P^(a+ε/2))*(D*P^(b+ε/2)) := mul_le_mul
      (hF P hPP₁) (hG P hPP₂) (abs_nonneg _) (by positivity)
    _ = C*D*(P^(a+ε/2)*P^(b+ε/2)) := by ring
    _ = C*D*P^((a+ε/2)+(b+ε/2)) := by rw [← Real.rpow_add hP]
    _ = _ := by congr 2; ring

#print axioms SourcePowerBound.add
#print axioms SourcePowerBound.mul

theorem SourcePowerBound.rpow_abs {F : ℝ → ℝ → ℝ} {a t : ℝ}
    (hF : SourcePowerBound F a) (ht : 0 ≤ t) :
    SourcePowerBound (fun P R => |F P R|^t) (a*t) := by
  intro ε hε
  let δ : ℝ := ε/(t+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδt : δ*t ≤ ε := by
    have he : δ*(t+1)=ε := by dsimp [δ]; exact div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨η₀,hη₀,hbound⟩ := hF δ hδ
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hbound η hη hηle
  refine ⟨C^t,Real.rpow_pos_of_pos hC _,P₀,hP₀,?_⟩
  intro P hPP
  have hP := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  calc
    _ ≤ (C*P^(a+δ))^t := Real.rpow_le_rpow (abs_nonneg _) (hbound P hPP) ht
    _ = C^t*P^((a+δ)*t) := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hPp.le _),← Real.rpow_mul hPp.le]
    _ ≤ C^t*P^(a*t+ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)) (Real.rpow_nonneg hC.le _)

theorem SourcePowerBound.rpow {F : ℝ → ℝ → ℝ} {a t : ℝ}
    (hF : SourcePowerBound F a) (ht : 0 ≤ t)
    (hF0 : ∀ P R : ℝ,1 ≤ P → 1 ≤ R → 0 ≤ F P R) :
    SourcePowerBound (fun P R => (F P R)^t) (a*t) := by
  apply (hF.rpow_abs ht).congr
  intro P R hP hR
  rw [abs_of_nonneg (hF0 P R hP hR)]

theorem SourcePowerBound.natPow {F : ℝ → ℝ → ℝ} {a : ℝ}
    (hF : SourcePowerBound F a) (n : ℕ) :
    SourcePowerBound (fun P R => (F P R)^n) (a*(n : ℝ)) := by
  intro ε hε
  obtain ⟨η₀,hη₀,hbound⟩ := hF.rpow_abs (Nat.cast_nonneg n) ε hε
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hbound η hη hηle
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP
  simpa only [Real.rpow_natCast,abs_pow,abs_abs] using hbound P hPP

/-- An actual uniform inequality with an arbitrarily small ambient power
loss transports a proved source power bound. -/
theorem SourcePowerBound.of_epsilon_domination {F G : ℝ → ℝ → ℝ} {a : ℝ}
    (hG : SourcePowerBound G a)
    (hdom : ∀ δ : ℝ,0 < δ → ∃ η₀ : ℝ,0 < η₀ ∧
      ∀ η : ℝ,0 < η → η ≤ η₀ → ∃ K : ℝ,0 < K ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧
        ∀ P : ℝ,P₀ ≤ P → |F P (P^η)| ≤ K*P^δ*|G P (P^η)|) :
    SourcePowerBound F a := by
  intro ε hε
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨η₁,hη₁,hG⟩ := hG (ε/2) hδ
  obtain ⟨η₂,hη₂,hdom⟩ := hdom (ε/2) hδ
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro η hη hηle
  obtain ⟨C,hC,P₁,hP₁,hG⟩ := hG η hη (hηle.trans (min_le_left _ _))
  obtain ⟨K,hK,P₂,hP₂,hdom⟩ := hdom η hη (hηle.trans (min_le_right _ _))
  refine ⟨K*C,by positivity,max P₁ P₂,hP₁.trans (le_max_left _ _),?_⟩
  intro P hPP
  have hPP₁ := (le_max_left P₁ P₂).trans hPP
  have hPP₂ := (le_max_right P₁ P₂).trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le (hP₁.trans hPP₁)
  calc
    _ ≤ K*P^(ε/2)*|G P (P^η)| := hdom P hPP₂
    _ ≤ K*P^(ε/2)*(C*P^(a+ε/2)) := mul_le_mul_of_nonneg_left (hG P hPP₁) (by positivity)
    _ = K*C*(P^(ε/2)*P^(a+ε/2)) := by ring
    _ = K*C*P^(ε/2+(a+ε/2)) := by rw [← Real.rpow_add hPp]
    _ = _ := by congr 2; ring

/-- Any available admissible smooth moment is uniform at every fixed
shorter power scale, including the harmless constant rescalings introduced
by centered differencing. -/
theorem admissible_shorter_source_bound {k p : ℕ} {lam L q : ℝ}
    (hlam : AdmissibleExponent k p lam) (hL : 1 ≤ L) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    SourcePowerBound (fun P R => smoothMoment k p (L*P^q) R) (q*lam) := by
  intro ε hε
  obtain ⟨η₀,hη₀,C,hC,hbound⟩ := admissibleExponent_uniform_shorter hlam hε
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  refine ⟨C*L^(ε+lam),by positivity,1,le_rfl,?_⟩
  intro P hP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hPL : P ≤ L*P := le_mul_of_one_le_left hPp.le hL
  have hLP : 1 ≤ L*P := hP.trans hPL
  have hY : 1 ≤ L*P^q := one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow hP hq0)
  have hYP : L*P^q ≤ L*P := mul_le_mul_of_nonneg_left
    ((Real.rpow_le_rpow_of_exponent_le hP hq1).trans_eq (Real.rpow_one _)) hLp.le
  have hR : P^η ≤ (L*P)^η₀ :=
    (Real.rpow_le_rpow_of_exponent_le hP hηle).trans (Real.rpow_le_rpow hPp.le hPL hη₀.le)
  rw [abs_of_nonneg (smoothMoment_nonneg ..)]
  calc
    _ ≤ C*(L*P)^ε*(L*P^q)^lam := hbound (L*P) hLP (P^η)
      (Real.one_le_rpow hP hη.le) hR (L*P^q) hY hYP
    _ = C*(L^ε*P^ε)*(L^lam*P^(q*lam)) := by
      rw [Real.mul_rpow hLp.le hPp.le,
        Real.mul_rpow hLp.le (Real.rpow_nonneg hPp.le _),← Real.rpow_mul hPp.le]
    _ = C*(L^ε*L^lam)*(P^(q*lam)*P^ε) := by ring
    _ = C*L^(ε+lam)*P^(q*lam+ε) := by rw [← Real.rpow_add hLp,← Real.rpow_add hPp]

theorem admissible_of_source_bound {k s : ℕ} {lam : ℝ}
    (h : SourcePowerBound (fun P R => smoothMoment k (2*s) P R) lam) :
    AdmissibleExponent k (2*s) lam := by
  intro ε hε
  obtain ⟨η,hη,hbound⟩ := h ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hbound η hη le_rfl
  refine ⟨η,hη,C,hC,P₀,hP₀,?_⟩
  intro P hPP R hR hRP
  exact (smoothMoment_even_mono_cutoff k s P hRP).trans
    ((le_abs_self _).trans (hbound P hPP))

#print axioms SourcePowerBound.rpow
#print axioms SourcePowerBound.of_epsilon_domination
#print axioms admissible_shorter_source_bound
#print axioms admissible_of_source_bound
end Waring.SeedCompletionSourceBounds
