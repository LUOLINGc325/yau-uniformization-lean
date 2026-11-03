import Yau.Proofs.P07DistanceLeviCalculus

noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L18Aux L22Aux

/-- Cauchy--Schwarz with the actual inverse metric on a real covector. -/
theorem real_covector_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (d v : ι → ℝ) :
    (d ⬝ᵥ v) ^ 2 ≤ (d ⬝ᵥ (G⁻¹ *ᵥ d)) * (v ⬝ᵥ (G *ᵥ v)) := by
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  have hv : G⁻¹ *ᵥ (G *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have H := hG.inv.star_dotProduct_mulVec_mul_le d (G *ᵥ v)
  simpa only [star_trivial, hv, pow_two, dotProduct_comm (G *ᵥ v) v] using H

variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricInChart_eq_quadratic (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    realMetricInChart h x z v v =
      realCoord v ⬝ᵥ (realMetricFn h x z *ᵥ realCoord v) := by
  rw [realBilin_eq_sum]
  simp only [realMetricInChart_basis h x z hz, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem fderiv_eq_realCoord_dot (f : ComplexVector n → ℝ) (z v : ComplexVector n) :
    fderiv ℝ f z v = (fun a => rDeriv f z a) ⬝ᵥ realCoord v := by
  conv_lhs => rw [← sum_realCoord_realVec v]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, rDeriv]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem fderiv_sq_le_chartGradientPair (h : HermitianField M) (x : M.Carrier)
    (f : ComplexVector n → ℝ) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    (fderiv ℝ f z v) ^ 2 ≤
      chartGradientPair h x f f z * realMetricInChart h x z v v := by
  rw [fderiv_eq_realCoord_dot, realMetricInChart_eq_quadratic h x hz]
  have H := real_covector_quadratic_le (realMetricFn h x z)
    (realMetricFn_posDef h x z hz) (fun a => rDeriv f z a) (realCoord v)
  simpa only [chartGradientPair, Matrix.toBilin'_apply', star_trivial] using H

theorem hMat_quadratic_chartVec (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) :
    leviDirection (hMat h x z) v =
      ((h (chartInv x z)).toFun (chartVec x (chartInv x z) v)
        (chartVec x (chartInv x z) v)).re := by
  have heq : ∑ i, (WithLp.ofLp v) i • stdVec i = v := by
    ext i
    simp [stdVec, Pi.single_apply]
  rw [leviDirection, L18Aux.hMat_quadratic]
  simp_rw [← chartVec_smul]
  rw [← L18Aux.chartVec_sum, heq]

theorem realMetricInChart_eq_twice_leviDirection (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    realMetricInChart h x z v v = 2 * leviDirection (hMat h x z) v := by
  rw [realMetricInChart_apply_complex h x hz, hMat_quadratic_chartVec]

theorem realMetricInChart_I (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    realMetricInChart h x z (Complex.I • v) (Complex.I • v) =
      realMetricInChart h x z v v := by
  rw [realMetricInChart_apply_complex h x hz, realMetricInChart_apply_complex h x hz,
    chartVec_smul, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right]
  congr 1
  congr 1
  simp only [Complex.star_def, Complex.conj_I]
  ring_nf
  simp

/-- A safe rank-one bound valid for a local coordinate germ; no global
smoothness of the scalar is used. The physical metric is `2 Re h`. -/
theorem directionalRankOne_le_chartGradientPair (h : HermitianField M) (x : M.Carrier)
    (f : ComplexVector n → ℝ) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    directionalRankOne f z v ≤
      chartGradientPair h x f f z * leviDirection (hMat h x z) v := by
  have h₁ := fderiv_sq_le_chartGradientPair h x f hz v
  have h₂ := fderiv_sq_le_chartGradientPair h x f hz (Complex.I • v)
  rw [realMetricInChart_I h x hz] at h₂
  rw [realMetricInChart_eq_twice_leviDirection h x hz] at h₁ h₂
  unfold directionalRankOne
  linarith

/-- The corresponding global smooth scalar statement uses the frozen
complex gradient norm and the original metric matrix. -/
theorem directionalRankOne_inChart_le (h : HermitianField M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) (v : ComplexVector n) :
    directionalRankOne (inChart x u) (chartPt x x) v ≤
      2 * gradNormSq h u x * leviDirection (gMat h x) v := by
  have H := directionalRankOne_le_chartGradientPair h x (inChart x u)
    (mem_extChartAt_target x) v
  change directionalRankOne (inChart x u) (chartPt x x) v ≤
    scalarGradientPair h u u x * leviDirection (gMat h x) v at H
  rwa [scalarGradientPair_eq_twice_gradNormSq h hu] at H

end Yau.NodeProofs.P07DistanceLevi
