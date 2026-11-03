import Yau.LeafProofs.L16HalfSpaceAnisotropic

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

theorem normalTraceLayer_smul {n : ℕ} (c : ℝ) (B : Point n → ℝ) (ξ : Space n) (t a : ℝ) :
    normalTraceLayer (c • B) ξ t a = c*normalTraceLayer B ξ t a := by
  simp only [normalTraceLayer,Pi.smul_apply,smul_eq_mul]
  have hAvg (r : ℝ) : heatAverage r (fun y => c*B (y,t-r)) ξ =
      c*heatAverage r (fun y => B (y,t-r)) ξ := heatAverage_smul c r (fun y => B (y,t-r)) ξ
  simp_rw [hAvg,mul_left_comm (normalHeatProfile _ _) c]
  exact intervalIntegral.integral_const_mul _ _

theorem normalTraceLayer_add_of_bounded {n : ℕ} {F G t a : ℝ} {B C : Point n → ℝ}
    (hB : Continuous B) (hC : Continuous C) (hF : ∀ p, |B p| ≤ F) (hG : ∀ p, |C p| ≤ G)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    normalTraceLayer (B+C) ξ t a = normalTraceLayer B ξ t a+normalTraceLayer C ξ t a := by
  have hBI := (normalTraceLayer_integrable_and_bound hB hF ht ha ξ).1
  have hCI := (normalTraceLayer_integrable_and_bound hC hG ht ha ξ).1
  simp only [normalTraceLayer]
  calc
    _ = ∫ r in (0 : ℝ)..t, (normalHeatProfile r a*heatAverage r (fun y => B (y,t-r)) ξ+
        normalHeatProfile r a*heatAverage r (fun y => C (y,t-r)) ξ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht
      intro r hr
      have hh := heatAverage_add_of_bounded hr.1
        (hB.comp (continuous_id.prodMk continuous_const))
        (hC.comp (continuous_id.prodMk continuous_const))
        (fun y => hF (y,t-r)) (fun y => hG (y,t-r)) ξ
      change normalHeatProfile r a*heatAverage r
        ((fun y => B (y,t-r))+(fun y => C (y,t-r))) ξ = _
      have hAvg : heatAverage r ((fun y => B (y,t-r))+(fun y => C (y,t-r))) ξ =
          heatAverage r (fun y => B (y,t-r)) ξ+heatAverage r (fun y => C (y,t-r)) ξ := by
        simpa only [Function.comp_def,id_eq] using hh
      rw [hAvg,mul_add]
    _ = _ := intervalIntegral.integral_add hBI hCI

theorem halfSpaceTraceHeatDuhamel_smul {n : ℕ} (e : Space n) (T c : ℝ)
    (f : Point n → ℝ) (p : Point n) :
    halfSpaceTraceHeatDuhamel e T (c • f) p = c*halfSpaceTraceHeatDuhamel e T f p := by
  have hLayer (q : Point n) : boundaryTraceLayer e
      (tracePastExtension T (fun p => (c • f) (halfSpaceBoundaryProjection e p.1,p.2))) q =
      c*boundaryTraceLayer e (tracePastExtension T (fun p => f (halfSpaceBoundaryProjection e p.1,p.2))) q :=
    normalTraceLayer_smul c _ _ _ _
  simp only [halfSpaceTraceHeatDuhamel,halfSpaceSecondOrderExtension]
  split_ifs
  · exact hLayer p
  · simp only [hLayer]
    ring

theorem halfSpaceTraceHeatDuhamel_add {n : ℕ} {α T F G : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {e : Space n} (he : ‖e‖ = 1) {f g : Point n → ℝ}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hg : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) g G)
    {p : Point n} (hpT : p.2 ∈ Icc 0 T) :
    halfSpaceTraceHeatDuhamel e T (f+g) p =
      halfSpaceTraceHeatDuhamel e T f p+halfSpaceTraceHeatDuhamel e T g p := by
  let B := tracePastExtension T (fun p => f (halfSpaceBoundaryProjection e p.1,p.2))
  let C := tracePastExtension T (fun p => g (halfSpaceBoundaryProjection e p.1,p.2))
  have hB := tracePastExtension_holder hα.le hT (holderBound_halfSpace_boundary_trace hα.le hf)
  have hC := tracePastExtension_holder hα.le hT (holderBound_halfSpace_boundary_trace hα.le hg)
  have hLayer (q : Point n) (hq : 0 ≤ inner ℝ e q.1) (hqt : 0 ≤ q.2) :
      boundaryTraceLayer e (B+C) q = boundaryTraceLayer e B q+boundaryTraceLayer e C q :=
    normalTraceLayer_add_of_bounded (continuousOn_univ.mp (holderBound_continuousOn hα hB))
      (continuousOn_univ.mp (holderBound_continuousOn hα hC))
      (fun q => by simpa only [Real.norm_eq_abs] using hB.2.1 q (mem_univ _))
      (fun q => by simpa only [Real.norm_eq_abs] using hC.2.1 q (mem_univ _)) hqt hq _
  change halfSpaceSecondOrderExtension e (boundaryTraceLayer e (B+C)) p =
    halfSpaceSecondOrderExtension e (boundaryTraceLayer e B) p+
      halfSpaceSecondOrderExtension e (boundaryTraceLayer e C) p
  by_cases hp : 0 ≤ inner ℝ e p.1
  · simp only [halfSpaceSecondOrderExtension,ite_eq_left hp]
    exact hLayer p hp hpT.1
  · have hs (j : ℝ) (hj : 0 ≤ j) : 0 ≤ inner ℝ e (normalSample e j p.1) := by
      rw [normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) (le_of_not_ge hp)
    simp only [halfSpaceSecondOrderExtension,ite_eq_right hp]
    rw [hLayer (normalSample e 1 p.1,p.2) (hs 1 (by norm_num)) hpT.1,
      hLayer (normalSample e 2 p.1,p.2) (hs 2 (by norm_num)) hpT.1,
      hLayer (normalSample e 3 p.1,p.2) (hs 3 (by norm_num)) hpT.1]
    ring

theorem halfSpaceOddResidual_smul {n : ℕ} (e : Space n) (c : ℝ) (f : Point n → ℝ) :
    halfSpaceOddExtension e (halfSpaceZeroTraceResidual e (c • f)) =
      c • halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f) := by
  funext p
  simp only [halfSpaceOddExtension,halfSpaceZeroTraceResidual,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem halfSpaceOddResidual_add {n : ℕ} (e : Space n) (f g : Point n → ℝ) :
    halfSpaceOddExtension e (halfSpaceZeroTraceResidual e (f+g)) =
      halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)+
        halfSpaceOddExtension e (halfSpaceZeroTraceResidual e g) := by
  funext p
  simp only [halfSpaceOddExtension,halfSpaceZeroTraceResidual,Pi.add_apply]
  split_ifs <;> ring

/-- The actual explicit flat solver is homogeneous on all ambient points. -/
theorem halfSpaceHeatDuhamel_smul {n : ℕ} (e : Space n) (T c : ℝ) (f : Point n → ℝ) (p : Point n) :
    halfSpaceHeatDuhamel e T (c • f) p = c*halfSpaceHeatDuhamel e T f p := by
  rw [halfSpaceHeatDuhamel,halfSpaceOddResidual_smul,heatDuhamel_smul,halfSpaceTraceHeatDuhamel_smul]
  simp only [halfSpaceHeatDuhamel]
  ring

/-- Additivity uses the genuine integrability of the two source kernels;
    it holds over the whole ambient closed slab. -/
theorem halfSpaceHeatDuhamel_add {n : ℕ} {α T F G : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {e : Space n} (he : ‖e‖ = 1) {f g : Point n → ℝ}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hg : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) g G)
    {p : Point n} (hpT : p.2 ∈ Icc 0 T) :
    halfSpaceHeatDuhamel e T (f+g) p = halfSpaceHeatDuhamel e T f p+halfSpaceHeatDuhamel e T g p := by
  have hF := holderBound_halfSpace_zero_trace_odd_extension he hα hf
  have hG := holderBound_halfSpace_zero_trace_odd_extension he hα hg
  rw [halfSpaceHeatDuhamel,halfSpaceOddResidual_add,
    heatDuhamel_add_of_holder hα hT hF hG hpT,
    halfSpaceTraceHeatDuhamel_add hα hT he hf hg hpT]
  simp only [halfSpaceHeatDuhamel]
  ring

end Yau.LeafProofs.L16Aux
