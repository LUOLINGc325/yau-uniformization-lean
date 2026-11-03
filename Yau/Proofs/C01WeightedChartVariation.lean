import Yau.Proofs.C01WeightedParameterJets

/-! The exact coordinate second variation of a genuine weighted parallel field. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem weighted_chart_energy_second_derivative
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (Z : ℝ × ℝ → ComplexVector n) (u : ℝ)
    (hz : Z (0, u) ∈ chartTarget c) (hZ : ContDiffAt ℝ 3 Z (0, u))
    (P : ℝ → ComplexVector n) (φ : ℝ → ℝ) (b : ℝ)
    (hP : HasDerivAt P
      (-chartChristoffelBilin k c (Z (0, u)) (mapDirection Z (0, 1) (0, u)) (P u)) u)
    (hφ : HasDerivAt φ b u)
    (hJ : (fun s => mapDirection Z (1, 0) (0, s)) =ᶠ[𝓝 u] (fun s => φ s • P s))
    (hRadial : ∀ᶠ s in 𝓝 u, deriv (deriv (fun r => Z (r, s))) 0 =
      -chartChristoffelBilin k c (Z (0, s)) (mapDirection Z (1, 0) (0, s))
        (mapDirection Z (1, 0) (0, s))) :
    deriv (deriv (fun r => realMetricInChart k c (Z (r, u))
      (mapDirection Z (0, 1) (r, u)) (mapDirection Z (0, 1) (r, u)))) 0 =
      2 * realMetricInChart k c (Z (0, u)) (b • P u) (b • P u) +
      2 * realMetricInChart k c (Z (0, u)) (mapDirection Z (0, 1) (0, u))
        (connectionCurvature (chartChristoffelBilin k c) (Z (0, u))
          (φ u • P u) (mapDirection Z (0, 1) (0, u)) (φ u • P u)) := by
  have hZ₂ : ContDiffAt ℝ 2 Z (0, u) := hZ.of_le (by norm_num)
  have hL := mapCovariantD_weighted_parallelVariation (chartChristoffelBilin k c)
    Z hZ₂ P φ b hP hφ hJ
  have hLr : mapCovariantD (chartChristoffelBilin k c) Z (1, 0)
      (mapDirection Z (0, 1)) (0, u) = b • P u :=
    (mapCovariantD_torsionFree _ Z hZ₂ (chartChristoffelBilin_symm k c (Z (0, u)))
      (1, 0) (0, 1)).trans hL
  have hRad := mapCovariantD_radialAcceleration_zero k hk c Z hz hZ hRadial
  have hVar := mapEnergyDensity_secondVariation k hk c Z hz hZ (1, 0) (0, 1) hRad
  have hG : ContDiffAt ℝ 2 (fun p => realMetricInChart k c (Z p)) (0, u) :=
    (((realMetricInChart_smooth k hk c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).of_le (by simp)).comp
        (0, u) hZ₂
  have hVel : ContDiffAt ℝ 2 (mapDirection Z (0, 1)) (0, u) :=
    mapDirection_contDiffAt Z 2 hZ (0, 1)
  have hDensity := (hG.clm_apply hVel).clm_apply hVel
  rw [← mapDirection_fst_second_eq_deriv _ hDensity]
  simpa only [hLr, hJ.self_of_nhds] using hVar

end Yau.NodeProofs.C01Aux
