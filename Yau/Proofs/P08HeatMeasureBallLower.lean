import Yau.Proofs.P08HeatMeasureGaussianVolume
import Yau.Proofs.P08HeatMeasureMoments

/-! The ball lower pairing obtained from actual self-adjoint heat and Harnack. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P08Aux.HeatMeasure
open LeafProofs LeafProofs.L19Aux LeafProofs.L18Aux LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- A dimensional constant fixed before the manifold, volume, radius and datum. -/
def ballHeatConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * gaussianVolumeConstant n * Real.exp ((2 * n : ℕ) + 1)

theorem ballHeatConstant_pos (n : ℕ) : 0 < ballHeatConstant n :=
  mul_pos (mul_pos (pow_pos (by norm_num) _) (gaussianVolumeConstant_pos n)) (Real.exp_pos _)

/-- For every nonnegative actual L² datum, heat evaluation controls its ball integral. -/
theorem heatEvalMeasure_ball_lower (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (L : ℝ) (hL : 0 < L) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ y ∂μ, 0 ≤ f y) :
    (∫ y in distBall g.form o L, f y ∂μ) ≤
      ballHeatConstant n * (μ (distBall g.form o L)).toReal *
        (∫ y, f y ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)) := by
  let t := L ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  let a := 1 / t
  have ha : 0 < a := one_div_pos.mpr ht
  let k := scalarGaussianL2 g hK hRic μ hμ o a ha
  let G := gaussianWeight g o a
  let U := scalarClassicalHeat hn g hK μ hμ f
  let W := scalarClassicalHeat hn g hK μ hμ k
  let B := distBall g.form o L
  have hB : MeasurableSet B := measurableSet_distBall g o L
  have hk : (fun y => k y) =ᵐ[μ] G := by
    filter_upwards [scalarGaussianL2_coe g hK hRic μ hμ o a ha] with y hy
    change _ = Real.exp (-(a * inducedDistance g.form o y ^ 2))
    rw [hy]
    congr 1
    ring
  have hU := scalarClassicalHeat_ae hn g hK μ hμ f ht
  have hW := scalarClassicalHeat_ae hn g hK μ hμ k ht
  have hGI : Integrable (fun y => G y * U y t) μ := by
    apply ((Lp.memLp k).integrable_mul (Lp.memLp (scalarHeatFamily g μ hμ t f))).congr
    filter_upwards [hk, hU] with y hky hUy
    change k y * scalarHeatFamily g μ hμ t f y = G y * U y t
    rw [hky]
    exact congrArg (fun z => G y * z) hUy.symm
  have hWI : Integrable (fun y => W y t * f y) μ := by
    apply ((Lp.memLp (scalarHeatFamily g μ hμ t k)).integrable_mul (Lp.memLp f)).congr
    filter_upwards [hW] with y hWy
    change scalarHeatFamily g μ hμ t k y * f y = W y t * f y
    exact congrArg (fun z => z * f y) hWy.symm
  have hpair : (∫ y, G y * U y t ∂μ) = ∫ y, W y t * f y ∂μ := by
    have hinner : inner ℝ k (scalarHeatFamily g μ hμ t f) =
        inner ℝ (scalarHeatFamily g μ hμ t k) f := by
      calc
        _ = inner ℝ ((scalarHeatFamily g μ hμ t).adjoint k) f :=
          (ContinuousLinearMap.adjoint_inner_left (scalarHeatFamily g μ hμ t) f k).symm
        _ = _ := by rw [scalarHeatFamily_adjoint]
    have hleft : inner ℝ k (scalarHeatFamily g μ hμ t f) = ∫ y, G y * U y t ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hk, hU] with y hky hUy
      simp only [RCLike.inner_apply, conj_trivial, hky, ← hUy, U, mul_comm]
    have hright : inner ℝ (scalarHeatFamily g μ hμ t k) f = ∫ y, W y t * f y ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hW] with y hWy
      simp only [RCLike.inner_apply, conj_trivial, ← hWy, W, mul_comm]
    exact hleft.symm.trans (hinner.trans hright)
  have hk0 : ∀ᵐ y ∂μ, 0 ≤ k y := by
    filter_upwards [hk] with y hy
    change k y = G y at hy
    exact (gaussianWeight_pos g o a y).le.trans_eq hy.symm
  have hW0 (y : M.Carrier) : 0 ≤ W y t := scalarClassicalHeat_nonneg hn g hK μ hμ k hk0 y ht
  have hU0 (y : M.Carrier) (s : ℝ) (hs : 0 < s) : 0 ≤ U y s :=
    scalarClassicalHeat_nonneg hn g hK μ hμ f hf y hs
  have hGaussLower (y : M.Carrier) : Real.exp (-((2 * n : ℕ) : ℝ)) * G y ≤ W y t := by
    have hh := scalarClassicalGaussianHeat_lower hn g hK hRic μ hμ o ha y ht
    have he : -((2 * n : ℕ) * a * t) = -((2 * n : ℕ) : ℝ) := by dsimp [a]; field_simp
    rw [he] at hh
    exact hh
  have hGball (y : M.Carrier) (hy : y ∈ B) : Real.exp (-1) ≤ G y := by
    have hd := (mem_distBall_iff g o y hL).mp hy
    have hd0 := g.induced_distance_nonneg o y
    apply Real.exp_le_exp.mpr
    change -1 ≤ -(a * inducedDistance g.form o y ^ 2)
    dsimp [a, t]
    rw [one_div_mul_eq_div]
    exact neg_le_neg ((div_le_one (sq_pos_of_pos hL)).mpr (by nlinarith))
  have hfi : IntegrableOn (fun y => f y) B μ := integrableOn_Lp_of_measure_ne_top f
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (riemannianVolume_distBall_lt_top g μ hμ o hL).ne
  have hlower : Real.exp (-((2 * n : ℕ) + 1 : ℝ)) * (∫ y in B, f y ∂μ) ≤
      ∫ y, W y t * f y ∂μ := by
    rw [← integral_indicator hB, ← integral_const_mul]
    apply integral_mono_ae (hfi.integrable_indicator hB |>.const_mul _) hWI
    filter_upwards [hf] with y hfy
    change Real.exp (-((2 * n : ℕ) + 1 : ℝ)) * B.indicator (fun y => f y) y ≤ W y t * f y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      apply mul_le_mul_of_nonneg_right _ hfy
      calc
        _ = Real.exp (-((2 * n : ℕ) : ℝ)) * Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-((2 * n : ℕ) : ℝ)) * G y :=
          mul_le_mul_of_nonneg_left (hGball y hy) (Real.exp_pos _).le
        _ ≤ _ := hGaussLower y
    · rw [indicator_of_notMem hy, mul_zero]
      exact mul_nonneg (hW0 y) hfy
  let Q : M.Carrier → ℝ := fun y => Real.exp (-(distFrom g.form o y ^ 2) / (2 * L ^ 2))
  have hQI : Integrable Q μ := by
    convert integrable_exp_neg_distance_sq g hK hRic μ hμ o (a := 1 / (2 * L ^ 2)) (by positivity) using 1
    funext y
    dsimp [Q, distFrom]
    congr 1
    ring
  have hupperPoint (y : M.Carrier) : G y * U y t ≤ (2 : ℝ) ^ n * U o (2 * t) * Q y := by
    have hh := nonnegativeHeatSolution_harnack liYauDifferential g hcomplete hK hRic
      (scalarClassicalHeat_smooth hn g hK μ hμ f) hU0
      (fun y s hs => scalarClassicalHeat_pde hn g hK μ hμ f y hs)
      ht (by linarith : t < 2 * t) y o
    rw [g.induced_distance_symm y o] at hh
    have hratio : 2 * t / t = 2 := by field_simp
    have htime : 2 * t - t = t := by ring
    rw [hratio, htime] at hh
    calc
      G y * U y t ≤ G y * ((2 : ℝ) ^ n * Real.exp (inducedDistance g.form o y ^ 2 / (2 * t)) * U o (2 * t)) :=
        mul_le_mul_of_nonneg_left hh (gaussianWeight_pos g o a y).le
      _ = (2 : ℝ) ^ n * U o (2 * t) * Q y := by
        have he : G y * Real.exp (inducedDistance g.form o y ^ 2 / (2 * t)) = Q y := by
          dsimp [G, gaussianWeight, Q, a, t, distFrom]
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring
        calc
          _ = (2 : ℝ) ^ n * U o (2 * t) * (G y * Real.exp (inducedDistance g.form o y ^ 2 / (2 * t))) := by ring
          _ = _ := by rw [he]
  have hupper : (∫ y, G y * U y t ∂μ) ≤
      (2 : ℝ) ^ n * U o (2 * t) * (gaussianVolumeConstant n * (μ B).toReal) := by
    calc
      _ ≤ ∫ y, ((2 : ℝ) ^ n * U o (2 * t)) * Q y ∂μ :=
        integral_mono hGI (hQI.const_mul _) hupperPoint
      _ = ((2 : ℝ) ^ n * U o (2 * t)) * ∫ y, Q y ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (normalizedGaussianIntegral g hcomplete hK hRic μ hμ o L hL)
        (mul_nonneg (pow_nonneg (by norm_num) _) (hU0 o (2 * t) (by positivity)))
  rw [hpair] at hupper
  have hcombined := hlower.trans hupper
  rw [heatEvalMeasure_integral]
  change (∫ y in B, f y ∂μ) ≤ ballHeatConstant n * (μ B).toReal * U o (2 * t)
  have he : Real.exp (((2 * n : ℕ) : ℝ) + 1) * Real.exp (-((2 * n : ℕ) + 1 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hc := mul_le_mul_of_nonneg_left hcombined (Real.exp_pos (((2 * n : ℕ) : ℝ) + 1)).le
  calc
    _ = Real.exp (((2 * n : ℕ) : ℝ) + 1) *
        (Real.exp (-((2 * n : ℕ) + 1 : ℝ)) * (∫ y in B, f y ∂μ)) := by rw [← mul_assoc, he, one_mul]
    _ ≤ _ := hc
    _ = _ := by dsimp [ballHeatConstant]; ring

end Yau.NodeProofs.P08Aux.HeatMeasure
