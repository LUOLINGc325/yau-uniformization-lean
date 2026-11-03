import Yau.LeafProofs.L05ABPRetraction
import Yau.LeafProofs.L05ABPSemiconvexABP

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem abp_source_shift_integral_tendsto {n : ℕ} {g : Point n → ℝ}
    (hg : ContinuousOn g (unitClosed n)) :
    Tendsto (fun j : ℕ => ∫ z in unitOpen n, (max (g z+1/((j:ℝ)+1)) 0)^(2*n+1))
      atTop (𝓝 (∫ z in unitOpen n, (max (g z) 0)^(2*n+1))) := by
  have hQsub : unitOpen n⊆unitClosed n := fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  obtain ⟨f,hf,heq,M,hM,hb⟩ := abp_bounded_uniform_extension hg
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hmeas : MeasurableSet (unitOpen n) := (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet
  have hFint (j : ℕ) : IntegrableOn
      (fun z : Point n => (max (g z+1/((j:ℝ)+1)) 0)^(2*n+1)) (unitOpen n) :=
    (((hg.add continuousOn_const).sup continuousOn_const).pow _).integrableOn_compact hD |>.mono_set hQsub
  have hboundint : IntegrableOn (fun _ : Point n => (M+1)^(2*n+1)) (unitOpen n) :=
    (continuousOn_const.integrableOn_compact hD).mono_set hQsub
  apply tendsto_integral_of_dominated_convergence (fun _ => (M+1)^(2*n+1))
    (fun j => (hFint j).aestronglyMeasurable) hboundint
  · intro j
    filter_upwards [ae_restrict_mem hmeas] with z hz
    have hzD := hQsub hz
    have hgz : |g z|≤M := by simpa only [heq hzD] using hb z
    have heta : (1:ℝ)/((j:ℝ)+1)≤1 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+1)).mpr
      norm_num
    have hmax : max (g z+1/((j:ℝ)+1)) 0≤M+1 :=
      max_le (by linarith [(abs_le.mp hgz).2]) (by linarith)
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (le_max_right _ _) _)]
    exact pow_le_pow_left₀ (le_max_right _ _) hmax _
  · apply Filter.Eventually.of_forall
    intro z
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ha : Tendsto (fun j : ℕ => max (g z+1/((j:ℝ)+1)) 0) atTop (𝓝 (max (g z) 0)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add ht).max tendsto_const_nhds
    exact ha.pow _

end Yau.LeafProofs.L05Aux
