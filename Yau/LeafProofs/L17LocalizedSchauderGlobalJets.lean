import Yau.LeafProofs.L17LocalizedSchauderPairScaling
import Yau.LeafProofs.L17LocalizedSchauderSumJets

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def globalUnitValue (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier) (t : Time T) : ComplexVector n → ℝ :=
  unitValue P.radius (fun z => globalSum P T v (P.charts.chart q z,t))

theorem globalUnitValue_eq_finsum (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier) (t : Time T) :
    globalUnitValue P T v q t = (fun z => ∑ᶠ p, unitLocalizedTerm P T p q (v p) t z) := by
  funext z
  exact (supported_finsum_smul P T (fun p => localizedTerm P T p (v p)) ((P.radius^2)⁻¹)
    (fun p r hr => localizedTerm_zero_of_not_cover P T p (v p) r hr) (P.charts.chart q (P.radius • z),t)).symm

theorem unitLocalizedFamily_finite_neighborhood (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 1) :
    ∃ I : Finset P.centers, I.card ≤ P.overlapBudget ∧
      ∀ᶠ w in 𝓝 z, ∀ p, p ∉ I → ∀ t : Time T, unitLocalizedTerm P T p q (v p) t w = 0 := by
  obtain ⟨I,hI,hZero⟩ := exists_active_neighborhood P (P.charts.chart q (P.radius • z))
  refine ⟨I,hI,?_⟩
  have hzρ : P.radius • z ∈ ball (0 : ComplexVector n) P.radius := by
    apply mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
    simpa only [mul_one] using mul_lt_mul_of_pos_left
      (show ‖z‖ < 1 from by simpa only [mem_ball,dist_zero_right] using hz) P.radius_pos
  have hSource := P.charts.closedBall_source q
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hzρ))
  have hChart : ContinuousAt (P.charts.chart q) (P.radius • z) :=
    (P.charts.chart q).continuousOn.continuousAt ((P.charts.chart q).open_source.mem_nhds hSource)
  have hScale : ContinuousAt (fun w : ComplexVector n => P.radius • w) z := by fun_prop
  have hMap : ContinuousAt (fun w : ComplexVector n => P.charts.chart q (P.radius • w)) z := hChart.comp hScale
  filter_upwards [hMap.eventually hZero] with w hw p hp t
  change (P.radius^2)⁻¹ • localizedTerm P T p (v p) (P.charts.chart q (P.radius • w),t) = 0
  rw [localizedTerm_zero_of_not_cover P T p (v p) _ (hw p hp),smul_zero]

theorem globalUnitValue_contDiffAt_two (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) (q : M.Carrier) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball 0 1) :
    ContDiffAt ℝ 2 (globalUnitValue P T v q t) z := by
  rw [globalUnitValue_eq_finsum]
  obtain ⟨I,hI,hZero⟩ := unitLocalizedFamily_finite_neighborhood P T v q hz
  exact contDiffAt_finsum _ I 2
    (fun p _ => unitLocalizedTerm_contDiffAt_two P T p q (v p) t
      (localTrueJets_spatial_contDiffOn_two P T hT v D H b hTrue p t) hz)
    (hZero.mono (fun w hw p hp => hw p hp t))

theorem globalUnitValue_iteratedFDeriv_eq_finsum (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) (q : M.Carrier) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball 0 1) (j : ℕ) (hj : j ≤ 2) :
    iteratedFDeriv ℝ j (globalUnitValue P T v q t) z =
      ∑ᶠ p, iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z := by
  rw [globalUnitValue_eq_finsum]
  obtain ⟨I,hI,hZero⟩ := unitLocalizedFamily_finite_neighborhood P T v q hz
  exact iteratedFDeriv_finsum _ I j
    (fun p _ => (unitLocalizedTerm_contDiffAt_two P T p q (v p) t
      (localTrueJets_spatial_contDiffOn_two P T hT v D H b hTrue p t) hz).of_le (by exact_mod_cast hj))
    (hZero.mono (fun w hw p hp => hw p hp t))

end Yau.LeafProofs.L17LocalizedSchauderAux
