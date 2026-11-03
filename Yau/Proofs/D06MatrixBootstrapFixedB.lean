import Yau.Proofs.D06MatrixBootstrapCalculus

/-! The fixed logarithmic derivative B=(D h)p.  The strictly positive
projection recovers this same B from pᴴ(D L)p; no regularity of B is assumed. -/

open MeasureTheory
open scoped ComplexConjugate Matrix

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleCoeff_finsetSum {ι : Type*} (s : Finset ι) (f : ι → CircleL2) (n : ℤ) :
    circleCoeff (∑ i ∈ s, f i) n = ∑ i ∈ s, circleCoeff (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, circleCoeff_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, circleCoeff_add, ih]

theorem circleWeakDerivative_eq_zero_of_constant {f df : CircleL2} (c : ℂ)
    (hD : CircleWeakDerivative f df) (hf : (f : HardyCircle → ℂ) =ᵐ[hardyCircleMeasure] fun _ => c) :
    df = 0 := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  ext n
  change circleCoeff df n = circleCoeff 0 n
  rw [circleCoeff_zero, hD n, circleCoeff_eq_fourierCoeff,
    congrFun (fourierCoeff_congr_ae hf) n, hardy_fourierCoeff_const]
  by_cases hn : n = 0 <;> simp [hn]

theorem circlePositiveProjection_pair_recover (B E C : CircleL2)
    (hB : ∀ n : ℤ, n ≤ 0 → circleCoeff B n = 0)
    (hE : ∀ n : ℤ, n ≤ 0 → circleCoeff E n = 0) (hC : C = B + star E) :
    circlePositiveProjection C = B := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  ext n
  change circleCoeff (circlePositiveProjection C) n = circleCoeff B n
  rw [circlePositiveProjection_coeff, hC, circleCoeff_add, circleCoeff_star]
  by_cases hn : 0 < n
  · rw [ite_eq_left hn, hE (-n) (by omega), map_zero, add_zero]
  · rw [ite_eq_right hn, hB n (by omega)]

theorem circleMatrix_fixedB_positive {r : ℕ} (h p : CircleMatrix r)
    (hh1 : CircleMatrixSobolev 1 h) (hp1 : CircleMatrixSobolev 1 p)
    (hh : CircleMatrixHardy h) (hp : CircleMatrixHardy p) :
    ∀ i j (n : ℤ), n ≤ 0 →
      circleCoeff (circleMatrixProduct (circleMatrixDerivative h hh1) p i j) n = 0 := by
  intro i j n hn
  rw [circleMatrixProduct, circleCoeff_finsetSum]
  apply Finset.sum_eq_zero
  intro k _
  rw [circleProduct_coeff _ _ (hp1 k j)]
  have hz (a : ℤ) : circleCoeff (p k j) a *
      circleCoeff (circleMatrixDerivative h hh1 i k) (n - a) = 0 := by
    by_cases ha : a < 0
    · rw [hp k j a ha, zero_mul]
    · change circleCoeff (p k j) a * circleCoeff (circleDerivative (h i k) (hh1 i k)) (n - a) = 0
      rw [circleDerivative_weak]
      by_cases hna : n - a < 0
      · rw [hh i k (n - a) hna, mul_zero, mul_zero]
      · have heq : n - a = 0 := by omega
        rw [heq]
        simp
  simp only [hz, tsum_zero]

theorem circleMatrix_fixedPair_derivative_identities {r : ℕ} (L h p : CircleMatrix r)
    (hL1 : CircleMatrixSobolev 1 L)
    (hh1 : CircleMatrixSobolev 1 h) (hp1 : CircleMatrixSobolev 1 p)
    (hInv : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval h t * circleMatrixEval p t = 1 ∧
        circleMatrixEval p t * circleMatrixEval h t = 1)
    (hGram : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval L t = (circleMatrixEval h t)ᴴ * circleMatrixEval h t) :
    let dh := circleMatrixDerivative h hh1
    let dp := circleMatrixDerivative p hp1
    let dl := circleMatrixDerivative L hL1
    let B := circleMatrixProduct dh p
    (∀ᵐ t ∂hardyCircleMeasure,
      (circleMatrixEval p t)ᴴ * circleMatrixEval dl t * circleMatrixEval p t =
        circleMatrixEval B t + (circleMatrixEval B t)ᴴ) ∧
    (∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval dh t = circleMatrixEval B t * circleMatrixEval h t ∧
      circleMatrixEval dp t = -(circleMatrixEval p t * circleMatrixEval B t)) := by
  dsimp only
  let dh := circleMatrixDerivative h hh1
  let dp := circleMatrixDerivative p hp1
  let dl := circleMatrixDerivative L hL1
  let B := circleMatrixProduct dh p
  have hdH : CircleMatrixWeakDerivative h dh := circleMatrixDerivative_weak h hh1
  have hdP : CircleMatrixWeakDerivative p dp := circleMatrixDerivative_weak p hp1
  have hdL : CircleMatrixWeakDerivative L dl := circleMatrixDerivative_weak L hL1
  have hstar : CircleMatrixSobolev 1 (circleMatrixStar h) := circleMatrixSobolev_star hh1
  have hGramClass : L = circleMatrixProduct (circleMatrixStar h) h := by
    apply circleMatrix_ext_ae
    filter_upwards [hGram, circleMatrixProduct_ae (circleMatrixStar h) h hh1,
      circleMatrixStar_ae h] with t hg hprod hs
    exact hg.trans (by rw [hprod, hs])
  have hDL : dl = circleMatrixLeibniz (circleMatrixStar h) h (circleMatrixStar dh) dh := by
    funext i j
    apply circleWeakDerivative_unique (hdL i j)
    rw [hGramClass]
    exact circleMatrixWeakDerivative_product hstar hh1 (circleMatrixWeakDerivative_star hdH) hdH i j
  have hDInv : circleMatrixLeibniz h p dh dp = 0 := by
    funext i j
    apply circleWeakDerivative_eq_zero_of_constant ((1 : Matrix (Fin r) (Fin r) ℂ) i j)
      (circleMatrixWeakDerivative_product hh1 hp1 hdH hdP i j)
    filter_upwards [circleMatrixProduct_ae h p hp1, hInv] with t hprod hi
    exact congrFun (congrFun (hprod.trans hi.1) i) j
  have hDL_eval : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval dl t = (circleMatrixEval dh t)ᴴ * circleMatrixEval h t +
        (circleMatrixEval h t)ᴴ * circleMatrixEval dh t := by
    rw [hDL]
    filter_upwards [circleMatrixLeibniz_ae (circleMatrixStar h) h (circleMatrixStar dh) dh hstar hh1,
      circleMatrixStar_ae h, circleMatrixStar_ae dh] with t ht hs hds
    exact ht.trans (by rw [hs, hds])
  have hInv_eval : ∀ᵐ t ∂hardyCircleMeasure,
      circleMatrixEval dh t * circleMatrixEval p t +
        circleMatrixEval h t * circleMatrixEval dp t = 0 := by
    have hzero : ∀ᵐ t ∂hardyCircleMeasure, circleMatrixEval (0 : CircleMatrix r) t = 0 := by
      have hz : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j, (0 : CircleL2) t = (0 : ℂ) :=
        ae_all_iff.mpr (fun _ : Fin r => ae_all_iff.mpr (fun _ : Fin r => Lp.coeFn_zero _ _ _))
      filter_upwards [hz] with t ht
      funext i j
      exact ht i j
    filter_upwards [circleMatrixLeibniz_ae h p dh dp hh1 hp1, hzero] with t ht hz
    rw [hDInv, hz] at ht
    exact ht.symm
  have hB_eval := circleMatrixProduct_ae dh p hp1
  constructor
  · filter_upwards [hInv, hDL_eval, hB_eval] with t hi hdl hb
    rw [hdl, hb, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul]
    have hstarinv : (circleMatrixEval p t)ᴴ * (circleMatrixEval h t)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi.1, Matrix.conjTranspose_one]
    calc
      _ = ((circleMatrixEval p t)ᴴ * (circleMatrixEval dh t)ᴴ) *
            (circleMatrixEval h t * circleMatrixEval p t) +
          ((circleMatrixEval p t)ᴴ * (circleMatrixEval h t)ᴴ) *
            (circleMatrixEval dh t * circleMatrixEval p t) := by noncomm_ring
      _ = _ := by rw [hi.1, hstarinv, mul_one, one_mul, add_comm]
  · filter_upwards [hInv, hInv_eval, hB_eval] with t hi hd hb
    constructor
    · rw [hb, mul_assoc, hi.2, mul_one]
    · apply eq_neg_of_add_eq_zero_right
      calc
        circleMatrixEval p t * circleMatrixEval B t + circleMatrixEval dp t =
          circleMatrixEval p t * (circleMatrixEval dh t * circleMatrixEval p t +
            circleMatrixEval h t * circleMatrixEval dp t) := by
              rw [hb, Matrix.mul_add, ← mul_assoc (circleMatrixEval p t) (circleMatrixEval h t),
                hi.2, one_mul]
        _ = 0 := by rw [hd, mul_zero]

end Yau.NodeProofs.D06Aux
