import Waring.PolicyCompletionBasicLinear
import Waring.PolicyCompletionPowerHeight

/-!
# Composition of the actual basic coefficient height sums
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicHeight
open RationalHeight PolicyCompletionBasicMoment PolicyCompletionBasicGcd
open PolicyCompletionBasicBinomial PolicyCompletionBasicLinear
open PolicyCompletionPowerClasses PolicyCompletionPowerHeight

theorem assembly_algebra {N Y K L E : ℝ} (hN : 1≤N) (hY : 0<Y) (hYN : Y≤N)
    (hK : 1≤K) (hL : 1≤L) (hE : 0≤E) :
    2*N^2/Y+K*(2*N^2*L/Y+2*K*N^2*L*(L/Y+K*E)+N*L)≤
      7*K^3*N^2*L^2*(1/Y+E) := by
  let A := 1/Y+E
  let T := N^2*L^2*A
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hAp : 0<A := by dsimp [A]; positivity
  have hTp : 0<T := by dsimp [T]; positivity
  have hLA : L/Y+K*E≤K*L*A := by
    have h1 : L/Y≤K*(L/Y) := le_mul_of_one_le_left (by positivity) hK
    have h2 : K*E≤L*(K*E) := le_mul_of_one_le_left (by positivity) hL
    calc
      _ ≤ K*(L/Y)+L*(K*E) := add_le_add h1 h2
      _ = _ := by dsimp [A]; ring
  have hLsq : L≤L^2 := by nlinarith
  have hKcube : K≤K^3 := by
    calc
      _ = K^1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hK (by norm_num)
  have hKcube1 : 1≤K^3 := one_le_pow₀ hK
  have hbase : N^2/Y≤T := by
    have hi : 1/Y≤A := by dsimp [A]; linarith
    have hA : A≤L^2*A := le_mul_of_one_le_left hAp.le (one_le_pow₀ hL)
    calc
      _ = N^2*(1/Y) := by ring
      _ ≤ N^2*(L^2*A) := mul_le_mul_of_nonneg_left (hi.trans hA) (sq_nonneg _)
      _ = _ := by dsimp [T]; ring
  have hmid : N^2*L/Y≤T := by
    calc
      _ = N^2*L*(1/Y) := by ring
      _ ≤ N^2*L^2*A := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hLsq (sq_nonneg _))
          (show 1/Y≤A by dsimp [A]; linarith) (by positivity) (by positivity)
      _ = _ := rfl
  have hlast : N*L≤T := by
    have hNdiv : N≤N^2/Y := by
      apply (le_div_iff₀ hY).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hYN hNp.le]
    exact (mul_le_mul_of_nonneg_right hNdiv hLp.le).trans_eq
      (by ring : N^2/Y*L=N^2*L/Y) |>.trans hmid
  have h1 : 2*N^2/Y≤2*K^3*T := by
    calc
      _ = 2*(N^2/Y) := by ring
      _ ≤ 2*(K^3*T) := mul_le_mul_of_nonneg_left
        (hbase.trans (le_mul_of_one_le_left hTp.le hKcube1)) (by norm_num)
      _ = _ := by ring
  have h2 : K*(2*N^2*L/Y)≤2*K^3*T := by
    calc
      _ = 2*(K*(N^2*L/Y)) := by ring
      _ ≤ 2*(K^3*T) := mul_le_mul_of_nonneg_left
        (mul_le_mul hKcube hmid (by positivity) (by positivity)) (by norm_num)
      _ = _ := by ring
  have h3 : K*(2*K*N^2*L*(L/Y+K*E))≤2*K^3*T := by
    calc
      _ ≤ K*(2*K*N^2*L*(K*L*A)) := by gcongr
      _ = _ := by dsimp [T]; ring
  have h4 : K*(N*L)≤K^3*T := mul_le_mul hKcube hlast (by positivity) (by positivity)
  calc
    _ = 2*N^2/Y+K*(2*N^2*L/Y)+K*(2*K*N^2*L*(L/Y+K*E))+K*(N*L) := by ring
    _ ≤ 2*K^3*T+2*K^3*T+2*K^3*T+K^3*T := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [T,A]; ring

#print axioms assembly_algebra

theorem sum_Icc_reciprocal_square (N : ℕ) :
    (∑j∈Finset.Icc 1 N,1/(j : ℝ)^2)≤2 := by
  have hset : Finset.Icc 1 N=(Finset.range N).image (fun n=>n+1) := by
    simpa using CubicDivisorClasses.positive_multiples_eq_image N 1 (by norm_num)
  rw [hset,Finset.sum_image (fun _ _ _ _ h=>by omega)]
  simpa only [Nat.cast_add,Nat.cast_one] using finite_reciprocal_squares N

theorem sum_Icc_reciprocal (N : ℕ) (hN : 0<N) :
    (∑j∈Finset.Icc 1 N,1/(j : ℝ))≤1+Real.log (2*(N : ℝ)) := by
  have hset : Finset.Icc 1 N=(Finset.range N).image (fun n=>n+1) := by
    simpa using CubicDivisorClasses.positive_multiples_eq_image N 1 (by norm_num)
  rw [hset,Finset.sum_image (fun _ _ _ _ h=>by omega)]
  calc
    _ = (harmonic N : ℝ) := by simp [harmonic,one_div]
    _ ≤ 1+Real.log (N : ℝ) := harmonic_le_one_add_log N
    _ ≤ _ := by
      apply add_le_add_left
      exact Real.log_le_log (by exact_mod_cast hN) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

theorem finite_height_assembly (A : Finset ℕ) (d N : ℕ) (M V Y α K : ℝ)
    (hN : 0<N) (hA : A⊆Finset.Icc 1 N) (hY : 0<Y) (hYN : Y≤N) (hK : 1≤K)
    (hbin : ∀j∈Finset.Icc 1 N,∀l∈Finset.Icc 1 (N/j),
      (∑n∈quotientDomain A N j l,
        1/(height V ((α*(j : ℝ)^d*l)*(PolicyCompletionBinomialArithmetic.natQuotient d n l : ℝ)))^(1/3 : ℝ))≤
      ((N : ℝ)/j)/Y+K*
        (((N : ℝ)/j)/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1))
    (hlin : ∀j∈Finset.Icc 1 N,
      (∑l∈Finset.Icc 1 (N/j),
        1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ))≤
      2*(N : ℝ)/Y+K*((2*(N : ℝ)/j)/
        (height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))*(1+Real.log (2*(N : ℝ))))
    (hpow : weightedPowerSum N d (V*M^d) α≤
      (1+Real.log (2*(N : ℝ)))/Y+K/(height (V*M^d) α)^(2/(d : ℝ))) :
    (∑p∈offPairs A,1/(height V (α*pairDifference d p))^(1/3 : ℝ))≤
      14*K^3*(N : ℝ)^2*(1+Real.log (2*(N : ℝ)))^2*
        (1/Y+1/(height (V*M^d) α)^(2/(d : ℝ))) := by
  let L := 1+Real.log (2*(N : ℝ))
  let E := 1/(height (V*M^d) α)^(2/(d : ℝ))
  let S (j : ℕ) := ∑l∈Finset.Icc 1 (N/j),
    1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ)
  let B (j : ℕ) := ∑l∈Finset.Icc 1 (N/j),∑n∈quotientDomain A N j l,
    1/(height V ((α*(j : ℝ)^d*l)*(PolicyCompletionBinomialArithmetic.natQuotient d n l : ℝ)))^(1/3 : ℝ)
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hL : 1≤L := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    dsimp [L]
    linarith
  have hEp : 0<E := one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)
  have hSp (j : ℕ) : 0≤S j := Finset.sum_nonneg fun _ _=>
    (one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)).le
  have hlocal (j : ℕ) (hj : j∈Finset.Icc 1 N) :
      B j≤((N : ℝ)/j)^2/Y+K*(((N : ℝ)/j)*S j+(N : ℝ)/j) := by
    have hjp : 0<j := (Finset.mem_Icc.mp hj).1
    have hjR : (0 : ℝ)<j := by exact_mod_cast hjp
    let v := (N : ℝ)/j
    have hv : 0≤v := by dsimp [v]; positivity
    have hnum : ((N/j : ℕ) : ℝ)≤v := nat_div_cast_le N j hjp
    calc
      B j ≤ ∑l∈Finset.Icc 1 (N/j),
          (v/Y+K*(v/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1)) :=
        Finset.sum_le_sum fun l hl=>hbin j hj l hl
      _ = ((N/j : ℕ) : ℝ)*v/Y+K*(v*S j+((N/j : ℕ) : ℝ)) := by
        have hid (l : ℕ) : v/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)=
            v*(1/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)) := by ring
        simp_rw [hid]
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
        simp only [Nat.card_Icc,Nat.add_sub_cancel]
        dsimp [S]
        ring
      _ ≤ v*v/Y+K*(v*S j+v) := by gcongr
      _ = _ := by dsimp [v]; ring
  let F (j : ℕ) := ((N : ℝ)/j)^2/Y+K*(((N : ℝ)/j)*
    (2*(N : ℝ)/Y+K*((2*(N : ℝ)/j)/
      (height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))*L)+(N : ℝ)/j)
  have hBF (j : ℕ) (hj : j∈Finset.Icc 1 N) : B j≤F j := by
    apply (hlocal j hj).trans
    dsimp [F]
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ hKp.le
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left (hlin j hj)
    positivity
  have hF (j : ℕ) :
      F j=((N : ℝ)^2/Y)*(1/(j : ℝ)^2)+K*
        ((2*(N : ℝ)^2/Y)*(1/(j : ℝ))+
          (2*K*(N : ℝ)^2*L)*(1/((j : ℝ)^2*
            (height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ)))+
          (N : ℝ)*(1/(j : ℝ))) := by
    dsimp [F]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  have hsumF : (∑j∈Finset.Icc 1 N,F j)=
      ((N : ℝ)^2/Y)*(∑j∈Finset.Icc 1 N,1/(j : ℝ)^2)+K*
        ((2*(N : ℝ)^2/Y)*(∑j∈Finset.Icc 1 N,1/(j : ℝ))+
          (2*K*(N : ℝ)^2*L)*weightedPowerSum N d (V*M^d) α+
          (N : ℝ)*(∑j∈Finset.Icc 1 N,1/(j : ℝ))) := by
    simp_rw [hF]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,weightedPowerSum]
  have hsum : (∑j∈Finset.Icc 1 N,B j)≤
      2*(N : ℝ)^2/Y+K*(2*(N : ℝ)^2*L/Y+
        2*K*(N : ℝ)^2*L*(L/Y+K*E)+(N : ℝ)*L) := by
    calc
      _ ≤ ∑j∈Finset.Icc 1 N,F j := Finset.sum_le_sum hBF
      _ = _ := hsumF
      _ ≤ ((N : ℝ)^2/Y)*2+K*((2*(N : ℝ)^2/Y)*L+
          (2*K*(N : ℝ)^2*L)*(L/Y+K*E)+(N : ℝ)*L) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (sum_Icc_reciprocal_square N) (by positivity)
        · apply mul_le_mul_of_nonneg_left _ hKp.le
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul_of_nonneg_left (sum_Icc_reciprocal N hN) (by positivity)
            · exact mul_le_mul_of_nonneg_left (by simpa only [L,E,mul_one_div] using hpow) (by positivity)
          · exact mul_le_mul_of_nonneg_left (sum_Icc_reciprocal N hN) (by positivity)
      _ = _ := by ring
  have hmain := hsum.trans (assembly_algebra hNR hY hYN hK hL hEp.le)
  rw [offPairs_height_gcd A hA d V α (1/3)]
  calc
    _ = 2*∑j∈Finset.Icc 1 N,B j := rfl
    _ ≤ 2*(7*K^3*(N : ℝ)^2*L^2*(1/Y+E)) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = _ := by dsimp [L,E]; ring

#print axioms finite_height_assembly

/-- The full actual off-diagonal height bound, with every counting and
divisor input discharged and a uniform arbitrarily small power loss. -/
theorem off_diagonal_height_bound {d : ℕ} (hd : 6≤d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(A : Finset ℕ) (N : ℕ) (M V Y α : ℝ),
      0<N→A⊆Finset.Icc 1 N→1≤M→M≤N→1≤V→0<Y→Y≤M→
      (∀m∈A,M<(m : ℝ))→
      2*Y^3*Real.sqrt (V*((d : ℝ)*(N : ℝ)^(d-1)))/V<1→
      2*Y^d<Real.sqrt (V*M^d)→
      (∑p∈offPairs A,1/(height V (α*pairDifference d p))^(1/3 : ℝ))≤
        C*(N : ℝ)^2*(denominatorScale d N V)^ε*(1+Real.log (2*(N : ℝ)))^2*
          (1/Y+1/(height (V*M^d) α)^(2/(d : ℝ))) := by
  let δ := ε/3
  have hδ : 0<δ := by dsimp [δ]; linarith
  obtain ⟨Cb,hCb,hbin⟩ := binomial_block_bound (by omega : 0<d) hδ
  obtain ⟨Cl,hCl,hlin⟩ := linear_block_bound hδ
  obtain ⟨Cd,hCd,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  let Cp := (2*2^(1/3 : ℝ))*Cd
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  let D := 1+Cb+Cl+Cp
  have hD : 1≤D := by dsimp [D]; linarith
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hCbD : Cb≤D := by dsimp [D]; linarith
  have hClD : Cl≤D := by dsimp [D]; linarith
  have hCpD : Cp≤D := by dsimp [D]; linarith
  refine ⟨14*D^3,by positivity,?_⟩
  intro A N M V Y α hN hA hM hMN hV hY hYM hAlower hsize hpower
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hVp : 0<V := zero_lt_one.trans_le hV
  have hscale := denominatorScale_ge (by omega : 0<d) hN hV
  have hscalePos : 0<denominatorScale d N V := zero_lt_one.trans_le hscale.1
  let K := D*(denominatorScale d N V)^δ
  have hScalePow : 1≤(denominatorScale d N V)^δ := Real.one_le_rpow hscale.1 hδ.le
  have hK : 1≤K := one_le_mul_of_one_le_of_one_le hD hScalePow
  have hCbK : Cb*(denominatorScale d N V)^δ≤K := mul_le_mul_of_nonneg_right hCbD (by positivity)
  have hClK : Cl*(denominatorScale d N V)^δ≤K := mul_le_mul_of_nonneg_right hClD (by positivity)
  have hCpK : Cp*(denominatorScale d N V)^δ≤K := mul_le_mul_of_nonneg_right hCpD (by positivity)
  have hb : ∀j∈Finset.Icc 1 N,∀l∈Finset.Icc 1 (N/j),
      (∑n∈quotientDomain A N j l,
        1/(height V ((α*(j : ℝ)^d*l)*(PolicyCompletionBinomialArithmetic.natQuotient d n l : ℝ)))^(1/3 : ℝ))≤
      ((N : ℝ)/j)/Y+K*
        (((N : ℝ)/j)/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1) := by
    intro j hj l hl
    apply (hbin A N M V Y α hN hMp hV hY hAlower hsize j hj l hl).trans
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_right hCbK (by
      have hh := height_pos (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l)
      positivity)
  have hl : ∀j∈Finset.Icc 1 N,
      (∑l∈Finset.Icc 1 (N/j),
        1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ))≤
      2*(N : ℝ)/Y+K*((2*(N : ℝ)/j)/
        (height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))*(1+Real.log (2*(N : ℝ))) := by
    intro j hj
    apply (hlin d N (by omega) hN M V Y α hM hMN hV hY hYM hsize j hj).trans
    apply add_le_add_left
    have hlog : 0≤1+Real.log (2*(N : ℝ)) := by
      have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
      have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
      linarith
    apply mul_le_mul_of_nonneg_right _ hlog
    exact mul_le_mul_of_nonneg_right hClK (by
      have hh := height_pos (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d)
      positivity)
  have hVM : 1≤V*M^d := one_le_mul_of_one_le_of_one_le hV (one_le_pow₀ hM)
  have hVMscale : V*M^d≤denominatorScale d N V := by
    have hdR : (1 : ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
    calc
      _ ≤ V*(N : ℝ)^d := by gcongr
      _ ≤ denominatorScale d N V := by
        have hh : 1≤2*(d : ℝ) := by linarith
        have hg := mul_le_mul_of_nonneg_right hh (show 0≤V*(N : ℝ)^d by positivity)
        dsimp [denominatorScale]
        nlinarith only [hg]
  obtain ⟨r,hr,hq,hp⟩ := weighted_power_height_bound N d hd hVM hY hpower (α := α)
  have hqScale : (r.den : ℝ)≤denominatorScale d N V := by
    apply hq.trans
    apply le_trans _ hVMscale
    have hs := Real.sq_sqrt (show 0≤V*M^d by positivity)
    have hs0 := Real.sqrt_nonneg (V*M^d)
    nlinarith [sq_nonneg (V*M^d-1)]
  have hdivisor := hdiv (denominatorScale d N V) hscale.1 r.den r.pos hqScale
  have hpcoef : (2*2^(1/3 : ℝ))*(r.den.divisors.card : ℝ)≤K := by
    calc
      _ ≤ (2*2^(1/3 : ℝ))*(Cd*(denominatorScale d N V)^δ) :=
        mul_le_mul_of_nonneg_left hdivisor (by positivity)
      _ = Cp*(denominatorScale d N V)^δ := by dsimp [Cp]; ring
      _ ≤ K := hCpK
  have hp' : weightedPowerSum N d (V*M^d) α≤
      (1+Real.log (2*(N : ℝ)))/Y+K/(height (V*M^d) α)^(2/(d : ℝ)) := by
    apply hp.trans
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hY.le
      apply add_le_add_left
      exact Real.log_le_log (by exact_mod_cast hN)
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    · exact div_le_div_of_nonneg_right hpcoef (Real.rpow_pos_of_pos (height_pos _ _) _).le
  have hmain := finite_height_assembly A d N M V Y α K hN hA hY (hYM.trans hMN) hK hb hl hp'
  have hKcube : K^3=D^3*(denominatorScale d N V)^ε := by
    dsimp [K]
    rw [mul_pow,← Real.rpow_mul_natCast hscalePos.le]
    congr 2
    dsimp [δ]
    norm_num
  rw [hKcube] at hmain
  convert hmain using 1 <;> ring

#print axioms off_diagonal_height_bound
end Waring.PolicyCompletionBasicHeight
