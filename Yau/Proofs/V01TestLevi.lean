import Yau.Proofs.V01ChartTest
import Yau.Proofs.V01PenaltyLevi
import Yau.Proofs.V03LeviLocality

/-! The true Levi matrix of the chart-pulled support is computed locally
inside the actual chart target, at every selected center. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix
namespace Yau.Blueprint.V01Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem leviMatrix_congr_nhds
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℝ} {z : E} (hfg : f =ᶠ[𝓝 z] g) (dir : ι → E) :
    leviMatrix f z dir = leviMatrix g z dir := by
  ext i j
  exact Yau.Blueprint.V03Proof.mixedWirt_congr
    (hfg.mono (fun _ h => congrArg Complex.ofReal h)) (dir i) (dir j)

theorem chartTest_spatialLevi (x : M.Carrier)
    (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) (t : ℝ) :
    leviMatrix (fun q => chartTest x ψ (cotangentChartInv x q) t) z cotangentDir =
      leviMatrix (fun q : CotangentCoord n => ψ (q.1, q.2, t)) z cotangentDir := by
  have hOpen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  apply leviMatrix_congr_nhds
  filter_upwards [hOpen.mem_nhds hz] with q hq
  exact chartTest_chartInv x ψ hq t

theorem canonicalChartTest_spatialLevi (x : M.Carrier)
    {φ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (a : ComplexVector n × ComplexVector n × ℝ) (hφ : ContDiffAt ℝ 2 φ a)
    (α : ℝ) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) (t : ℝ) :
    leviMatrix (fun q => chartTest x (canonicalQuadraticSupport φ a α)
      (cotangentChartInv x q) t) z cotangentDir =
      leviMatrix (fun q : CotangentCoord n => φ (q.1, q.2, a.2.2))
        (a.1, a.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n) := by
  rw [chartTest_spatialLevi x _ hz t, canonicalQuadraticSupport_spatialLevi a hφ α z t]

end Yau.Blueprint.V01Proof
