import Yau.LeafProofs.L23DistanceEnergyVariation

/-! The full second variation keeps the acceleration term of both moving
endpoints. It does not assume that radial accelerations vanish. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {M : ComplexManifold n}

theorem mapEnergyDensity_full_secondVariation
    (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z : E → ComplexVector n) {p : E}
    (hz : Z p ∈ chartTarget c) (hZ : ContDiffAt ℝ 3 Z p) (a b : E) :
    mapDirection (mapDirection (fun q => realMetricInChart h c (Z q)
      (mapDirection Z b q) (mapDirection Z b q)) a) a p =
      2 * realMetricInChart h c (Z p)
        (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) p)
        (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) p) +
      2 * realMetricInChart h c (Z p) (mapDirection Z b p)
        (connectionCurvature (chartChristoffelBilin h c) (Z p)
          (mapDirection Z a p) (mapDirection Z b p) (mapDirection Z a p)) +
      2 * realMetricInChart h c (Z p) (mapDirection Z b p)
        (mapCovariantD (chartChristoffelBilin h c) Z b
          (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z a)) p) := by
  have hZ₂ : ContDiffAt ℝ 2 Z p := hZ.of_le (by norm_num)
  have hJ : ContDiffAt ℝ 2 (mapDirection Z a) p := mapDirection_contDiffAt Z 2 hZ a
  have hT : ContDiffAt ℝ 2 (mapDirection Z b) p := mapDirection_contDiffAt Z 2 hZ b
  have hΓ : DifferentiableAt ℝ (chartChristoffelBilin h c) (Z p) :=
    ((chartChristoffelBilin_contDiffOn h hh c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt
      (by simp)
  have heq : mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) =ᶠ[𝓝 p]
      mapCovariantD (chartChristoffelBilin h c) Z b (mapDirection Z a) := by
    filter_upwards [(hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).eventually
      (by norm_num)] with q hq
    exact mapCovariantD_torsionFree _ Z hq (chartChristoffelBilin_symm h c (Z q)) a b
  have hComm := mapCovariantD_commutator (chartChristoffelBilin h c) Z
    (mapDirection Z a) hΓ hZ₂ hJ a b
  have hOuter := (mapCovariantD_congr (chartChristoffelBilin h c) Z heq a).trans
    (eq_add_of_sub_eq hComm)
  rw [mapMetricDensity_secondDirection h hh c Z (mapDirection Z b) hz hZ₂ hT a,
    hOuter, map_add]
  ring

theorem mapEnergyDensity_firstDirection_zero
    (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z : E → ComplexVector n) {p : E}
    (hz : Z p ∈ chartTarget c) (hZ : ContDiffAt ℝ 2 Z p) (a b : E)
    (hparallel : mapCovariantD (chartChristoffelBilin h c) Z b (mapDirection Z a) p = 0) :
    mapDirection (fun q => realMetricInChart h c (Z q)
      (mapDirection Z b q) (mapDirection Z b q)) a p = 0 := by
  have hT : DifferentiableAt ℝ (mapDirection Z b) p :=
    (mapDirection_contDiffAt Z 1 hZ b).differentiableAt_one
  rw [mapDirection_metricSelf h hh c Z (mapDirection Z b) hz
      (hZ.differentiableAt (by norm_num)) hT a,
    mapCovariantD_torsionFree _ Z hZ (chartChristoffelBilin_symm h c (Z p)) a b,
    hparallel, map_zero, mul_zero]

theorem mapEnergyDensity_paired_secondVariation
    (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z : E → ComplexVector n) {p : E}
    (hz : Z p ∈ chartTarget c) (hZ : ContDiffAt ℝ 3 Z p) (a ai b : E)
    (ha : mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) p = 0)
    (hai : mapCovariantD (chartChristoffelBilin h c) Z ai (mapDirection Z b) p = 0)
    (hradial :
      mapCovariantD (chartChristoffelBilin h c) Z b
          (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z a)) p +
        mapCovariantD (chartChristoffelBilin h c) Z b
          (mapCovariantD (chartChristoffelBilin h c) Z ai (mapDirection Z ai)) p = 0) :
    mapDirection (mapDirection (fun q => realMetricInChart h c (Z q)
        (mapDirection Z b q) (mapDirection Z b q)) a) a p +
      mapDirection (mapDirection (fun q => realMetricInChart h c (Z q)
        (mapDirection Z b q) (mapDirection Z b q)) ai) ai p =
      2 * realMetricInChart h c (Z p) (mapDirection Z b p)
          (connectionCurvature (chartChristoffelBilin h c) (Z p)
            (mapDirection Z a p) (mapDirection Z b p) (mapDirection Z a p)) +
        2 * realMetricInChart h c (Z p) (mapDirection Z b p)
          (connectionCurvature (chartChristoffelBilin h c) (Z p)
            (mapDirection Z ai p) (mapDirection Z b p) (mapDirection Z ai p)) := by
  have hR := congrArg (fun w : ComplexVector n =>
    2 * realMetricInChart h c (Z p) (mapDirection Z b p) w) hradial
  simp only [map_add, map_zero, mul_add, mul_zero] at hR
  rw [mapEnergyDensity_full_secondVariation h hh c Z hz hZ a b,
    mapEnergyDensity_full_secondVariation h hh c Z hz hZ ai b, ha, hai]
  simp only [map_zero, ContinuousLinearMap.zero_apply, mul_zero, zero_add]
  linarith only [hR]

end Yau.Proofs.C03Aux
