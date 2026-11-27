import Waring.PolicyCompletionSourceMajorNorm
import Waring.PolicyCompletionSourceMajorSize

/-! # Exact Cartesian source family majorants before scale normalization -/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMajorFamily
open Polynomial IntegerDifferencePolynomial PolicyCompletionPhaseContent
open PolicyCompletionSourceMajor PolicyCompletionSourceMajorNorm
open PolicyCompletionMajorAverage ProductMultiplicity

def naturalParameters {j : ℕ} (h m : Fin j → ℕ) : List (ℤ × ℤ) :=
  List.ofFn (fun i => ((h i:ℤ),(m i:ℤ)))

@[simp] theorem naturalParameters_length {j : ℕ} (h m : Fin j → ℕ) :
    (naturalParameters h m).length=j := by simp [naturalParameters]

theorem naturalParameters_pos {j : ℕ} (h m : Fin j → ℕ)
    (hh : ∀ i, 0<h i) (hm : ∀ i, 0<m i) :
    ∀ p ∈ naturalParameters h m, 0<p.1 ∧ 0<p.2 := by
  simp only [naturalParameters, List.forall_mem_ofFn_iff]
  intro i
  constructor <;> exact_mod_cast (by first | exact hh i | exact hm i)

@[simp] theorem naturalParameters_heightProduct {j : ℕ} (h m : Fin j → ℕ) :
    heightProduct (naturalParameters h m)=(tupleProduct h:ℤ) := by
  simp [heightProduct, naturalParameters, List.map_ofFn, Function.comp_def,
    List.prod_ofFn, tupleProduct, Nat.cast_prod]

def sourceFamily {j : ℕ} (k : ℕ) (S T : Finset (Fin j → ℕ)) (P α : ℝ) : ℂ :=
  ∑ h ∈ S, ∑ m ∈ T, integerPolynomialWeyl (powerPolynomial k (naturalParameters h m)) P α

theorem source_family_majorant (k j : ℕ) (hj : j+2≤k) {ε : ℝ} (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ)
      (S T : Finset (Fin j → ℕ)) (P β : ℝ),
      IsCoprime (q:ℤ) a → (∀ h ∈ S, ∀ i, 0<h i) → (∀ m ∈ T, ∀ i, 0<m i) → 0<P →
      (∀ h ∈ S, ∀ m ∈ T,
        |β| *((powerPolynomial k (naturalParameters h m)).map (Int.castRingHom ℝ)).derivative.eval P
          ≤1/(2*(q:ℝ))) →
      ‖sourceFamily k S T P ((a:ℝ)/q+β)‖ ≤
        C₀*(T.card:ℝ)*(P*(q:ℝ)^(-1/((k-j:ℕ):ℝ)+ε)*
          (∑ h ∈ S, (Nat.gcd q (tupleProduct h):ℝ)^(1/((k-j:ℕ):ℝ))*
            (1+|β| *(tupleProduct h:ℝ)*P^(k-j))^(-1/((k-j:ℕ):ℝ)))+
          (S.card:ℝ)*(q:ℝ)^(1-1/((k-j:ℕ):ℝ)+ε)) := by
  obtain ⟨C₀,hC₀,hbound⟩ := source_single_phase_majorant k j hj hε
  refine ⟨C₀,hC₀,?_⟩
  intro q _ a S T P β ha hS hT hP hsmall
  have hs (h : Fin j → ℕ) (hh : h∈S) (m : Fin j → ℕ) (hm : m∈T) :=
    hbound q a (naturalParameters h m) P β ha (naturalParameters_length h m)
      (naturalParameters_pos h m (hS h hh) (hT m hm)) hP (hsmall h hh m hm)
  simp only [naturalParameters_heightProduct, Int.natAbs_natCast, Int.cast_natCast] at hs
  calc
    _ ≤ ∑ h ∈ S, ‖∑ m ∈ T,
        integerPolynomialWeyl (powerPolynomial k (naturalParameters h m)) P ((a:ℝ)/q+β)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ S, ∑ m ∈ T,
        ‖integerPolynomialWeyl (powerPolynomial k (naturalParameters h m)) P ((a:ℝ)/q+β)‖ :=
      Finset.sum_le_sum (fun h _ => norm_sum_le _ _)
    _ ≤ ∑ h ∈ S, ∑ m ∈ T,
        C₀*(P*(q:ℝ)^(-1/((k-j:ℕ):ℝ)+ε)*
          (Nat.gcd q (tupleProduct h):ℝ)^(1/((k-j:ℕ):ℝ))*
            (1+|β| *(tupleProduct h:ℝ)*P^(k-j))^(-1/((k-j:ℕ):ℝ))+
          (q:ℝ)^(1-1/((k-j:ℕ):ℝ)+ε)) :=
      Finset.sum_le_sum (fun h hh => Finset.sum_le_sum (fun m hm => hs h hh m hm))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro h hh
        ring
      · ring

theorem source_family_height_majorant (k j : ℕ) (hj : j+2≤k)
    {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (P : ℝ), 1≤P → ∀ (q : ℕ) [NeZero q] (N : ℕ),
      0<N → (q:ℝ)≤P^B → (N:ℝ)≤P^B → ∀ (a : ℤ) (S T : Finset (Fin j → ℕ)) (β : ℝ),
      IsCoprime (q:ℤ) a → (∀ h ∈ S, ∀ i, 0<h i) → (∀ m ∈ T, ∀ i, 0<m i) →
      (∀ h ∈ S, tupleProduct h ∈ Finset.Icc 1 N) →
      (∀ h ∈ S, ∀ m ∈ T,
        |β| *((powerPolynomial k (naturalParameters h m)).map (Int.castRingHom ℝ)).derivative.eval P
          ≤1/(2*(q:ℝ))) →
      ‖sourceFamily k S T P ((a:ℝ)/q+β)‖ ≤
        C₀*P^ε*(T.card:ℝ)*(N:ℝ)*
          (P*(q:ℝ)^(-1/((k-j:ℕ):ℝ))*(1+|β| *P^(k-j)*(N:ℝ))^(-1/((k-j:ℕ):ℝ))+
            (q:ℝ)^(1-1/((k-j:ℕ):ℝ))) := by
  let δ : ℝ := ε/(2*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hhalf : 0<ε/2 := by positivity
  have hBδ : B*δ≤ε/2 := by
    have hh : δ*(2*(B+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨Cf,hCf,hfamily⟩ := source_family_majorant k j hj hδ
  obtain ⟨Ca,hCa,havg⟩ := height_product_major_average j hB hhalf
  refine ⟨Cf*Ca, by positivity, ?_⟩
  intro P hP q _ N hN hqP hNP a S T β ha hS hT hmap hsmall
  let θ : ℝ := 1/((k-j:ℕ):ℝ)
  have hD : (1:ℝ)≤(k-j:ℕ) := by exact_mod_cast (show 1≤k-j by omega)
  have hθ : 0≤θ := by dsimp [θ]; positivity
  have hθ1 : θ≤1 := (div_le_one (zero_lt_one.trans_le hD)).mpr hD
  have hPpos : 0<P := zero_lt_one.trans_le hP
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hqδ : (q:ℝ)^δ≤P^(ε/2) := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow hqR.le hqP hδ.le
      _ = P^(B*δ) := (Real.rpow_mul hPpos.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hBδ
  have hmain := havg P hP q N hq hN hqP hNP S (|β| *P^(k-j)) θ hmap (by positivity) hθ hθ1
  have hcard := havg P hP q N hq hN hqP hNP S 0 0 hmap (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_zero, mul_zero, zero_mul, add_zero, mul_one, Finset.sum_const,
    nsmul_eq_mul, neg_zero] at hcard
  have hinner : (∑ h ∈ S, (Nat.gcd q (tupleProduct h):ℝ)^θ*
      (1+|β| *(tupleProduct h:ℝ)*P^(k-j))^(-θ)) ≤
      Ca*P^(ε/2)*(N:ℝ)*(1+|β| *P^(k-j)*(N:ℝ))^(-θ) := by
    simpa only [mul_right_comm (|β|) (P^(k-j))] using hmain
  have hfam := hfamily q a S T P β ha hS hT hPpos hsmall
  simp only [neg_div] at hfam ⊢
  change ‖sourceFamily k S T P ((a:ℝ)/q+β)‖ ≤
    (Cf*Ca)*P^ε*(T.card:ℝ)*(N:ℝ)*(P*(q:ℝ)^(-θ)*
      (1+|β| *P^(k-j)*(N:ℝ))^(-θ)+(q:ℝ)^(1-θ))
  apply hfam.trans
  have hpow (x : ℝ) : (q:ℝ)^(x+δ)=(q:ℝ)^x*(q:ℝ)^δ := Real.rpow_add hqR x δ
  change Cf*(T.card:ℝ)*(P*(q:ℝ)^(-θ+δ)*
    (∑ h ∈ S, (Nat.gcd q (tupleProduct h):ℝ)^θ*(1+|β| *(tupleProduct h:ℝ)*P^(k-j))^(-θ))+
    (S.card:ℝ)*(q:ℝ)^(1-θ+δ)) ≤ _
  rw [hpow (-θ), hpow (1-θ)]
  have hestimate := add_le_add
    (mul_le_mul (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hqδ (Real.rpow_nonneg hqR.le (-θ))) hPpos.le) hinner
      (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity))
    (mul_le_mul hcard (mul_le_mul_of_nonneg_left hqδ (Real.rpow_nonneg hqR.le (1-θ)))
      (by positivity) (by positivity))
  apply (mul_le_mul_of_nonneg_left hestimate (by positivity : 0≤Cf*(T.card:ℝ))).trans_eq
  have hp : P^ε=P^(ε/2)*P^(ε/2) := by rw [← Real.rpow_add hPpos]; congr 1; ring
  rw [hp]
  ring

#print axioms source_family_majorant
#print axioms source_family_height_majorant
end Waring.PolicyCompletionMajorFamily
