import Yau.Proofs.V03LocalImmersionBound
import Yau.Proofs.V03TransitionInverse

/-! The original immersion controls actual cotangent coordinates locally
by its ambient distance. No properness, global inverse, or positive
dimension premise is introduced. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentImmersion_local_chart_bound {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ Metric.ball z r ⊆ cotangentTarget x ∧
      ∀ u ∈ Metric.ball z r, ∀ v ∈ Metric.ball z r,
        ‖u - v‖ ≤ C * ‖G (cotangentChartInv x u) - G (cotangentChartInv x v)‖ := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hc := (cotangentHolomorphic_chart_contDiffOn hG.1 x).contDiffAt (hopen.mem_nhds hz)
  have hd := hc.differentiableAt (by simp)
  have hzc : cotangentChart x (cotangentChartInv x z) = z := cotangentChart_right_inv x hz
  have hcoords : Function.Injective (cotangentCoordsVector : CotangentCoord n → CotangentIndex n → ℂ) :=
    (show Function.LeftInverse cotangentVectorOfCoords cotangentCoordsVector from
      cotangentVectorOfCoords_coordsVector).injective
  have hcomplex : Function.Injective
      (fderiv ℂ (fun w => G (cotangentChartInv x w)) z) := by
    intro u v huv
    apply hcoords
    apply cotangentDG_mulVec_injective_in_chart hG x (cotangentChartInv x z)
      (cotangentChartInv_mapsTo x hz)
    ext b
    simpa only [cotangentDG_mulVec, cotangentVectorOfCoords_coordsVector, hzc] using
      congrArg (fun w : ComplexVector q => w b) huv
  have hreal : Function.Injective
      (fderiv ℝ (fun w => G (cotangentChartInv x w)) z) := by
    intro u v huv
    rw [hd.fderiv_restrictScalars ℝ] at huv
    exact hcomplex huv
  obtain ⟨r, C, hr, hC, hb⟩ := local_lower_bound_of_injective_strict_derivative
    ((hc.restrict_scalars ℝ).hasStrictFDerivAt (by simp)) hreal
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨min r δ, C, lt_min hr hδ, hC, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right r δ)).trans hδsub
  · intro u hu v hv
    exact hb u (Metric.ball_subset_ball (min_le_left r δ) hu) v
      (Metric.ball_subset_ball (min_le_left r δ) hv)

end Yau.Blueprint.V03Proof
