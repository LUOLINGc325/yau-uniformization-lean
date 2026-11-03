import Yau.Proofs.V03TimeScalars
import Yau.Proofs.V03Walls
import Yau.Proofs.V03OuterBoundary

open scoped Topology ContDiff
open MeasureTheory Filter Set
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

/-- Narrow original-clock regularity, using only accepted scalar pullbacks.
This is the fixed b7097df clock proof without its unrelated Fejér imports. -/
theorem real_closedDisc_trace_contDiff {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiff ℝ ∞ (fun θ ↦ f (circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hh := (hf _ (circlePoint_mem_closedBall θ)).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun t (_ : t ∈ (univ : Set ℝ)) ↦ circlePoint_mem_closedBall t)
  exact contDiffWithinAt_univ.mp hh

theorem raw_weight_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) : ContDiff ℝ ∞ (clockWeightRaw d k j a F) := by
  obtain ⟨_, hbase, _, _, _, _, hfiber⟩ := hk.2.2.2.1 j
  have hb := real_closedDisc_trace_contDiff (cotangentDisc_smoothFn_contDiffOn hbase hF.1)
  have hf := real_closedDisc_trace_contDiff (cotangentDisc_scalar_contDiffOn hF.1 hfiber)
  have hw := real_closedDisc_trace_contDiff ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow a)
  have hrho : SmoothSpaceTime d.rho (Ici 0) := hd.2.2.1.1.2.2.2.1
  have hr := real_closedDisc_trace_contDiff
    (cotangentDisc_smoothSpaceTime_contDiffOn hrho hF.1 (discTime_contDiffOn hF.2.1)
      (fun ζ hζ ↦ (admissible_discTime_mem hF hζ).1.le))
  exact (hw.pow 4).mul (((hb.neg).mul (hr.add contDiff_const)).exp) |>.mul
    (((hf.neg).mul contDiff_const).exp)

theorem raw_weight_pos {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) : 0 < clockWeightRaw d k j a F θ := by
  have hm := (admissible_wallPower_bounds hd hF a θ).1
  dsimp only [clockWeightRaw]
  exact mul_pos (mul_pos (pow_pos hm 4) (Real.exp_pos _)) (Real.exp_pos _)

theorem clock_weight_pos_smooth {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    (∀ θ, 0 < clockWeight d k j a F θ) ∧ ContDiff ℝ ∞ (clockWeight d k j a F) ∧
      Function.Periodic (clockWeight d k j a F) (2 * Real.pi) := by
  have hc := raw_weight_contDiff hd hk (a := a) hF
  have hZ : 0 < circleAverage (clockWeightRaw d k j a F) := by
    unfold circleAverage
    apply mul_pos (by positivity)
    apply intervalIntegral.integral_pos (by positivity) hc.continuous.continuousOn
    · intro θ _
      exact (raw_weight_pos hd hF θ).le
    · exact ⟨0, ⟨le_rfl, by positivity⟩, raw_weight_pos hd hF 0⟩
  refine ⟨fun θ ↦ div_pos (raw_weight_pos hd hF θ) hZ, hc.div_const _, ?_⟩
  intro θ
  simp only [clockWeight, clockWeightRaw, circlePoint_periodic θ]

/-- The exact positive weight appearing in the frozen right-hand side. -/
def submeanWeight (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) (θ : ℝ) : ℝ :=
  discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
    (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹

theorem submeanWeight_pos_smooth {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    (∀ θ, 0 < submeanWeight d k j a F θ) ∧ ContDiff ℝ ∞ (submeanWeight d k j a F) ∧
      Function.Periodic (submeanWeight d k j a F) (2 * Real.pi) := by
  obtain ⟨hγ, hγc, hγp⟩ := clock_weight_pos_smooth hd hk hF
  have hm (θ : ℝ) := (admissible_wallPower_bounds hd hF a θ).1
  have hmc := real_closedDisc_trace_contDiff ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow a)
  have htc := real_closedDisc_trace_contDiff (discTime_contDiffOn hF.2.1)
  refine ⟨?_, (htc.div_const _).mul hγc |>.mul ((hmc.pow 4).inv (fun θ ↦ (pow_pos (hm θ) 4).ne')), ?_⟩
  · intro θ
    exact mul_pos (mul_pos (div_pos ((admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1)
      hF.2.2.2.1) (hγ θ)) (inv_pos.mpr (pow_pos (hm θ) 4))
  · intro θ
    simp only [submeanWeight, circlePoint_periodic θ, hγp θ]

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
