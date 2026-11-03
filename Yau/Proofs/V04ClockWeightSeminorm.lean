import Yau.Proofs.V04ClockRawCoefficient
import Yau.Proofs.V04ClockBoundaryWeights
import Yau.Proofs.V03BoundaryHilbertDifference
import Yau.Proofs.V03ClockDifference
import Yau.Proofs.V03EnergyTraceBounds
import Yau.Proofs.V03DirichletScaling

/-! The actual raw clock's half-order seminorm is controlled by the
original ambient and clock areas, without any positive lower-time margin. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockWeightRaw_scalarDSq_energy_bound {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      scalarDSq (clockWeightRaw d k j a F) ≤ ENNReal.ofReal C * variationEnergy d j F := by
  obtain ⟨C₀, hC₀, hbound⟩ := clockRawCoefficient_compact_lipschitz hd hk j a
  let C₁ := 2 * C₀ ^ 2 * (1 + (2 * d.T) ^ 2)
  let C := C₁ * (2 * (2 * Real.pi)⁻¹)
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun F hF => ?_⟩
  have hraw := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hG : Continuous (fun θ => d.G (F.f (circlePoint θ))) :=
    (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1).continuousOn.comp_continuous
      circlePoint_contDiff.continuous (fun θ => circlePoint_mem_closedBall θ)
  have hw := (closedDisc_scalar_trace_contDiff hF.2.1).continuous
  have hy (θ : ℝ) : F.f (circlePoint θ) ∈ boundaryCompact d j :=
    ⟨(hF.2.2.2.2.2.2.2.1 θ).1.le, (hF.2.2.2.2.2.2.2.1 θ).2.le⟩
  have hdifference : ∀ θ τ,
      ‖(clockWeightRaw d k j a F θ : ℂ) - (clockWeightRaw d k j a F τ : ℂ)‖ ≤
        C₀ * (‖d.G (F.f (circlePoint θ)) - d.G (F.f (circlePoint τ))‖ +
          (2 * d.T) * ‖F.w (circlePoint θ) - F.w (circlePoint τ)‖) := by
    intro θ τ
    have htθ := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
    have htτ := admissible_discTime_mem hF (circlePoint_mem_closedBall τ)
    have hh := hbound _ (hy θ) _ (hy τ) _ ⟨htθ.1.le, htθ.2.le⟩ _ ⟨htτ.1.le, htτ.2.le⟩
    have htime := admissible_clock_difference hF θ τ
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [htime]) hC₀)
  have hrawDSq := boundaryDSq_le_of_hilbert_difference hG hw
    (Complex.continuous_ofReal.comp hraw)
    (fun θ => congrArg d.G (congrArg F.f (circlePoint_periodic θ)))
    (fun θ => congrArg F.w (circlePoint_periodic θ))
    (fun θ => congrArg Complex.ofReal (clockWeightRaw_periodic d k j a F θ))
    hC₀ (by linarith [hd.1] : 0 ≤ 2 * d.T) hdifference
  have hGDSq : boundaryDSq (fun θ i => d.G (F.f (circlePoint θ)) i) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
    rw [boundaryDSq_vector_eq_inverse_area
      (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1)]
    gcongr
    exact euclideanArea_le_variationEnergy d j F
  have hwDSq : boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
    rw [boundaryDSq_scalar_eq_inverse_area hF.2.1]
    gcongr
    exact clockArea_le_variationEnergy d j F
  calc
    scalarDSq (clockWeightRaw d k j a F) ≤ ENNReal.ofReal C₁ *
      (boundaryDSq (fun θ i => d.G (F.f (circlePoint θ)) i) +
        boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := hrawDSq
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F +
        ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F) := by gcongr
    _ = ENNReal.ofReal C * variationEnergy d j F := by
      dsimp only [C]
      rw [ENNReal.ofReal_mul hC₁, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

theorem fixed_index_clock_weight_seminorm_bound {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
        ∀ᶠ ν in Filter.atTop,
          scalarDSq (clockWeight d k j a (F ν)) ≤ ENNReal.ofReal C * variationEnergy d j (F ν) := by
  obtain ⟨C₀, hC₀, hraw⟩ := clockWeightRaw_scalarDSq_energy_bound hd hk j a
  obtain ⟨z, hz, hZ⟩ := fixed_index_clock_normalizer_lower hd hk j a
  refine ⟨z⁻¹ ^ 2 * C₀, mul_nonneg (sq_nonneg _) hC₀, fun ε hε hε1 F hF => ?_⟩
  filter_upwards [hZ ε hε hε1 F hF] with ν hν
  let Z := circleAverage (clockWeightRaw d k j a (F ν))
  have hZp : 0 < Z := clockWeightRaw_average_pos hd (hF.1 ν)
    (clockWeightRaw_contDiff (a := a) hd hk (hF.1 ν)).continuous
  have hi : Z⁻¹ ≤ z⁻¹ := inv_anti₀ hz hν
  have hisq : Z⁻¹ ^ 2 ≤ z⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hZp.le) hi 2
  have heq : clockWeight d k j a (F ν) =
      fun θ => Z⁻¹ * clockWeightRaw d k j a (F ν) θ := by
    funext θ
    dsimp only [clockWeight, Z]
    ring
  rw [heq, scalarDSq_const_mul]
  calc
    _ ≤ ENNReal.ofReal (Z⁻¹ ^ 2) * (ENNReal.ofReal C₀ * variationEnergy d j (F ν)) := by
      gcongr
      exact hraw (F ν) (hF.1 ν)
    _ ≤ ENNReal.ofReal (z⁻¹ ^ 2) * (ENNReal.ofReal C₀ * variationEnergy d j (F ν)) := by
      gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

end Yau.Blueprint.V04Proof
