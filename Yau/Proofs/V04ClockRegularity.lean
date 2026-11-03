import Yau.Proofs.V04ClockNormalization
import Yau.Proofs.V03TimeScalars

/-! The frozen raw clock weight is smooth for every original admissible
disc. All pullbacks use the actual cotangent charts and physical time. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem closedDisc_real_trace_contDiff {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiff ℝ ∞ (fun θ => f (circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hh := (hf _ (circlePoint_mem_closedBall θ)).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall t)
  exact contDiffWithinAt_univ.mp hh

theorem clockWeightRaw_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) : ContDiff ℝ ∞ (clockWeightRaw d k j a F) := by
  obtain ⟨_, hbase, _, _, _, _, hfiber⟩ := hk.2.2.2.1 j
  have hb := closedDisc_real_trace_contDiff
    (cotangentDisc_smoothFn_contDiffOn hbase hF.1)
  have hf := closedDisc_real_trace_contDiff
    (cotangentDisc_scalar_contDiffOn hF.1 hfiber)
  have hw := closedDisc_real_trace_contDiff
    ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow a)
  have hrho : SmoothSpaceTime d.rho (Set.Ici 0) := hd.2.2.1.1.2.2.2.1
  have hr := closedDisc_real_trace_contDiff
    (cotangentDisc_smoothSpaceTime_contDiffOn hrho hF.1
      (discTime_contDiffOn hF.2.1)
      (fun ζ hζ => (admissible_discTime_mem hF hζ).1.le))
  exact (hw.pow 4).mul (((hb.neg).mul (hr.add contDiff_const)).exp) |>.mul
    (((hf.neg).mul contDiff_const).exp)

theorem exists_clockLift {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    ∃ Γ : ℂ → ℂ, ClockLift d k j a F Γ ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re :=
  clockLift_of_raw_regular hd hF (clockWeightRaw_contDiff hd hk hF)

end Yau.Blueprint.V04Proof
