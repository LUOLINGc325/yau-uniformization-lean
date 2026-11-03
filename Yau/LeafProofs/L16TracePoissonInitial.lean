import Yau.LeafProofs.L16TracePoissonAverage

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePoissonAverage_small_time_bound {n : ℕ} {α T F a : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (ha : 0 ≤ a) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F) (hB0 : ∀ x, B (x,0) = 0)
    {p : Point n} (hp : p.2 ∈ Set.Icc 0 T) :
    |tracePoissonAverage a (tracePastExtension T B) p| ≤ F*p.2^(α/2) := by
  by_cases ha0 : a = 0
  · rw [tracePoissonAverage,ite_eq_left ha0]
    exact tracePastExtension_small_time_bound hα hT hB hB0 hp le_rfl p.1
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hExt := tracePastExtension_holder hα.le hT hB
  have hCont : Continuous (tracePastExtension T B) :=
    continuousOn_univ.mp (holderBound_continuousOn hα hExt)
  have hSup (q : Point n) : |tracePastExtension T B q| ≤ F := hExt.2.1 q (Set.mem_univ _)
  have hInt := tracePoissonAverage_integrable haPos hCont hSup p
  have hProb := normalPoissonKernel_probability haPos
  have hDom : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖normalPoissonKernel a r*heatAverage r
        (fun y => tracePastExtension T B (y,p.2-r)) p.1‖ ≤
        normalPoissonKernel a r*(F*p.2^(α/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hHeat := heatAverage_bound hr
      (hCont.comp (continuous_id.prodMk continuous_const))
      (fun y => tracePastExtension_small_time_bound hα hT hB hB0 hp
        (show p.2-r ≤ p.2 from sub_le_self _ (le_of_lt hr)) y) p.1
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (normalPoissonKernel_nonneg ha hr)]
    exact mul_le_mul_of_nonneg_left hHeat (normalPoissonKernel_nonneg ha hr)
  rw [tracePoissonAverage,ite_eq_right ha0]
  calc
    |∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*heatAverage r
        (fun y => tracePastExtension T B (y,p.2-r)) p.1| ≤
      ∫ r in Set.Ioi (0 : ℝ), ‖normalPoissonKernel a r*heatAverage r
        (fun y => tracePastExtension T B (y,p.2-r)) p.1‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun r => normalPoissonKernel a r*heatAverage r
          (fun y => tracePastExtension T B (y,p.2-r)) p.1)
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*(F*p.2^(α/2)) :=
      integral_mono_ae hInt.norm (hProb.1.mul_const _) hDom
    _ = F*p.2^(α/2) := by rw [integral_mul_const,hProb.2,one_mul]

theorem heatAverage_normal_invariant {n : ℕ} {e : Space n} (g : Space n → ℝ)
    (hg : ∀ (x : Space n) (s : ℝ), g (x+s • e) = g x)
    (r : ℝ) (x : Space n) (s : ℝ) :
    heatAverage r g (x+s • e) = heatAverage r g x := by
  rw [heatAverage_def,heatAverage_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change gaussianKernel r y*g (x+s • e-y) = gaussianKernel r y*g (x-y)
    rw [show x+s • e-y = (x-y)+s • e by abel,hg]

theorem tracePoissonAverage_normal_invariant {n : ℕ} {e : Space n} (B : Point n → ℝ)
    (hB : ∀ (x : Space n) (s t : ℝ), B (x+s • e,t) = B (x,t))
    (a : ℝ) (x : Space n) (s t : ℝ) :
    tracePoissonAverage a B (x+s • e,t) = tracePoissonAverage a B (x,t) := by
  by_cases ha0 : a = 0
  · simp only [tracePoissonAverage,ite_eq_left ha0,hB]
  · rw [tracePoissonAverage,ite_eq_right ha0,tracePoissonAverage,ite_eq_right ha0]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      change normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) (x+s • e) =
        normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) x
      rw [heatAverage_normal_invariant (fun y => B (y,t-r))
        (fun y s' => hB y s' (t-r))]

end Yau.LeafProofs.L16Aux
