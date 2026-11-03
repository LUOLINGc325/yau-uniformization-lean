import Yau.LeafProofs.L03RawChartForms

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- Raw compact ordinary chart fields have all the genuine manifold
L²/support properties and reconstruct exactly under zero pullback. -/
theorem chartFormPushforward_raw_properties (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (W : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hW : MemLp W 2 (lebesgueC n)) (hcW : HasCompactSupport W)
    (hWO : tsupport W ⊆ chartTarget x) :
    L2RealForm g.form μ (chartFormPushforward x W) ∧
      CompactlySupportedRealForm (chartFormPushforward x W) ∧
      closure {y | chartFormPushforward x W y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source ∧
      chartFormPullbackZero x (chartFormPushforward x W) = W := by
  have hi := chartFormPushforward_image_support x W hcW hWO
  have hK : IsCompact (chartInv x '' tsupport W) :=
    hcW.image_of_continuousOn ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hWO)
  refine ⟨chartFormPushforward_l2_of_memLp g μ hμ x W hW hcW hWO,
    hK.of_isClosed_subset isClosed_closure hi, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hi hy
    exact (extChartAt (ComplexModel n) x).map_target (hWO hz)
  · funext z
    by_cases hz : z ∈ chartTarget x
    · simp only [chartFormPullbackZero, ite_eq_left hz, chartFormPushforward_to_chart x W hz]
    · have hzW : W z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hWO h))
      simp only [chartFormPullbackZero, ite_eq_right hz, hzW]

/-- Strong ordinary chart convergence with a fixed genuine compact
support implies convergence in the original metric L² form distance. -/
theorem chartFormPushforward_strong_l2_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ chartTarget x)
    (P : ℕ → ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ∀ m, ContDiff ℝ ∞ (P m)) (hPK : ∀ m, tsupport (P m) ⊆ K)
    (W : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hW : MemLp W 2 (lebesgueC n)) (hWK : tsupport W ⊆ K)
    (ht : Tendsto (fun m => ∫ z, ‖P m z - W z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    Tendsto (fun m => formL2DistanceSq g.form μ (chartFormPushforward x (P m))
      (chartFormPushforward x W)) atTop (𝓝 0) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hcW : HasCompactSupport W := hK.of_isClosed_subset (isClosed_tsupport _) hWK
  have hraw := chartFormPushforward_raw_properties g μ hμ x W hW hcW (hWK.trans hKO)
  have hAK : tsupport (chartFormPullbackZero x (chartFormPushforward x W)) ⊆ K := by
    rw [hraw.2.2.2]
    exact hWK
  obtain ⟨D, hD, hb⟩ := chartFormPushforward_l2_distance_bound g μ hμ
    (chartFormPushforward x W) hraw.1 hraw.2.1 x hraw.2.2.1 hK hKO hAK
  have hbound (m : ℕ) : formL2DistanceSq g.form μ (chartFormPushforward x (P m))
      (chartFormPushforward x W) ≤ ENNReal.ofReal (D * ∫ z, ‖P m z - W z‖ ^ 2 ∂lebesgueC n) := by
    have hPm : MemLp (P m) 2 (lebesgueC n) := (hP m).continuous.memLp_of_hasCompactSupport
      (hK.of_isClosed_subset (isClosed_tsupport _) (hPK m))
    have he := (ofReal_integral_norm_sq_eq_eLpNorm_sq (lebesgueC n) (hW.sub hPm)).symm
    have hi : (∫ z, ‖(W - P m) z‖ ^ 2 ∂lebesgueC n) =
        ∫ z, ‖P m z - W z‖ ^ 2 ∂lebesgueC n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change ‖W z - P m z‖ ^ 2 = ‖P m z - W z‖ ^ 2
        rw [norm_sub_rev]
    rw [hi] at he
    have h := hb (P m) (hP m) (hPK m)
    rw [hraw.2.2.2, he, ← ENNReal.ofReal_mul hD.le] at h
    exact h
  have hupper : Tendsto (fun m => ENNReal.ofReal (D * ∫ z, ‖P m z - W z‖ ^ 2 ∂lebesgueC n))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (ht.const_mul D)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => bot_le) hbound

end Yau.LeafProofs.L03
