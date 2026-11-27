import Waring.PolicyCompletionMajorFamily
import Waring.AuxiliaryMajorArcs

/-! # The actual auxiliary family at the intrinsic rational height -/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMajorHeight
open Polynomial IntegerDifferencePolynomial PolicyCompletionMajorFamily
open PolicyCompletionSourceMajor ProductMultiplicity RationalHeight

/-- The harmless conductor comparison is retained as a fixed constant.
The approximation is allowed to be unreduced in this algebraic lemma. -/
theorem rational_weight_le_height {P V c θ β : ℝ} {d N q : ℕ}
    (hP : 0<P) (hV : 0≤V) (hc : 1≤c) (hθ : 0≤θ) (hθ1 : θ≤1)
    (hq : 0<q) (hVup : V≤c*P^d*(N:ℝ)) (a : ℤ) :
    (q:ℝ)^(-θ)*(1+|β| *P^d*(N:ℝ))^(-θ) ≤
      c*(height V ((a:ℝ)/q+β))^(-θ) := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hcpos : 0<c := zero_lt_one.trans_le hc
  let W : ℝ := (q:ℝ)*(1+|β| *P^d*(N:ℝ))
  have hW : 0<W := by dsimp [W]; positivity
  have hcost : height V ((a:ℝ)/q+β)≤c*W := by
    apply (height_le_unreduced hV a hq).trans
    apply max_le
    · have hw : (q:ℝ)≤W := by
        dsimp [W]
        exact le_mul_of_one_le_right hqR.le (by
          have ht : 0≤|β| *P^d*(N:ℝ) := by positivity
          linarith)
      exact hw.trans (le_mul_of_one_le_left hW.le hc)
    · have heq : |(q:ℝ)*((a:ℝ)/q+β)-(a:ℝ)|=(q:ℝ)*|β| := by
        rw [show (q:ℝ)*((a:ℝ)/q+β)-(a:ℝ)=(q:ℝ)*β by field_simp; ring]
        rw [abs_mul,abs_of_pos hqR]
      rw [heq]
      have hh := mul_le_mul_of_nonneg_right hVup (mul_nonneg hqR.le (abs_nonneg β))
      dsimp [W]
      nlinarith
  have hweight := Real.rpow_le_rpow_of_exponent_nonpos
    (height_pos V ((a:ℝ)/q+β)) hcost (neg_nonpos.mpr hθ)
  have hid : (c*W)^(-θ)=c^(-θ)*W^(-θ) := Real.mul_rpow hcpos.le hW.le
  rw [hid] at hweight
  have hm := mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg hcpos.le θ)
  have hcancel : c^θ*c^(-θ)=1 := by rw [← Real.rpow_add hcpos]; simp
  have hh : W^(-θ)≤c^θ*(height V ((a:ℝ)/q+β))^(-θ) := by
    calc
      _ = c^θ*(c^(-θ)*W^(-θ)) := by rw [←mul_assoc,hcancel,one_mul]
      _ ≤ _ := hm
  have hcθ : c^θ≤c := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc hθ1
  calc
    _ = W^(-θ) := (Real.mul_rpow hqR.le (by positivity)).symm
    _ ≤ c^θ*(height V ((a:ℝ)/q+β))^(-θ) := hh
    _ ≤ _ := mul_le_mul_of_nonneg_right hcθ (Real.rpow_nonneg (height_pos _ _).le _)

/-- A genuine pointwise major estimate for the entire finite source family.
Only actual parameter/arc ranges remain; the exponential-sum estimate and
the gcd-weight average have both been proved in the imported modules. -/
theorem source_family_intrinsic_majorant (k j : ℕ) (hj : j+2≤k)
    {B ε c : ℝ} (hB : 0≤B) (hε : 0<ε) (hc : 1≤c) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (P : ℝ), 1≤P → ∀ (q : ℕ) [NeZero q] (N : ℕ),
      0<N → (q:ℝ)≤P → (q:ℝ)≤P^B → (N:ℝ)≤P^B →
      ∀ (a : ℤ) (S T : Finset (Fin j → ℕ)) (V β : ℝ),
      0≤V → V≤c*P^(k-j)*(N:ℝ) → IsCoprime (q:ℤ) a →
      (∀ h ∈ S, ∀ i, 0<h i) → (∀ m ∈ T, ∀ i, 0<m i) →
      (∀ h ∈ S, tupleProduct h ∈ Finset.Icc 1 N) →
      (∀ h ∈ S, ∀ m ∈ T,
        |β| *((powerPolynomial k (naturalParameters h m)).map (Int.castRingHom ℝ)).derivative.eval P
          ≤1/(2*(q:ℝ))) →
      ‖sourceFamily k S T P ((a:ℝ)/q+β)‖ ≤
        C₀*P^ε*(T.card:ℝ)*(N:ℝ)*P*
          ((height V ((a:ℝ)/q+β))^(-1/((k-j:ℕ):ℝ))+P^(-1/((k-j:ℕ):ℝ))) := by
  obtain ⟨C₁,hC₁,hfamily⟩ := source_family_height_majorant k j hj hB hε
  refine ⟨C₁*c,by positivity,?_⟩
  intro P hP q _ N hN hqP hqPB hNP a S T V β hV hVup ha hS hT hmap hsmall
  have h := hfamily P hP q N hN hqPB hNP a S T β ha hS hT hmap hsmall
  let θ : ℝ := 1/((k-j:ℕ):ℝ)
  have hD : (1:ℝ)≤(k-j:ℕ) := by exact_mod_cast (show 1≤k-j by omega)
  have hθ : 0≤θ := by dsimp [θ]; positivity
  have hθ1 : θ≤1 := (div_le_one (zero_lt_one.trans_le hD)).mpr hD
  have hPpos : 0<P := zero_lt_one.trans_le hP
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hw := rational_weight_le_height (β := β) hPpos hV hc hθ hθ1 hq hVup a
  have he : (q:ℝ)^(1-θ)≤P*P^(-θ) := by
    calc
      _ ≤ P^(1-θ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hqP (by linarith)
      _ = P*P^(-θ) := by rw [sub_eq_add_neg,Real.rpow_add hPpos,Real.rpow_one]
  simp only [neg_div] at h ⊢
  change ‖sourceFamily k S T P ((a:ℝ)/q+β)‖ ≤
    (C₁*c)*P^ε*(T.card:ℝ)*(N:ℝ)*P*
      ((height V ((a:ℝ)/q+β))^(-θ)+P^(-θ))
  apply h.trans
  have hsum : P*(q:ℝ)^(-θ)*(1+|β| *P^(k-j)*(N:ℝ))^(-θ)+(q:ℝ)^(1-θ) ≤
      c*P*((height V ((a:ℝ)/q+β))^(-θ)+P^(-θ)) := by
    have hm := mul_le_mul_of_nonneg_left hw hPpos.le
    have hcP := le_mul_of_one_le_left (by positivity : 0≤P*P^(-θ)) hc
    nlinarith only [hm,he,hcP]
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0≤C₁*P^ε*(T.card:ℝ)*(N:ℝ))
  convert hh using 1 <;> ring

#print axioms rational_weight_le_height
#print axioms source_family_intrinsic_majorant
end Waring.PolicyCompletionMajorHeight
