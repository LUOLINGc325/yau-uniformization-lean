import Yau.Proofs.V03AtlasCompact

/-! Local coefficient regularity transfers through the actual cotangent
chart transition; no auxiliary topology is placed on raw cotangent pairs. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}
    {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem intrinsicCoefficient_contDiffAt_of_fixed_chart
    {B : CotangentPoint M → P → F} {y : CotangentPoint M} {p : P} (x : M.Carrier)
    (hy : y ∈ cotangentSource x)
    (hB : ContDiffAt ℝ 1 (fun w : CotangentCoord n × P => B (cotangentChartInv x w.1) w.2)
      (cotangentChart x y, p)) :
    ContDiffAt ℝ 1 (fun w : CotangentCoord n × P => B (cotangentChartInv y.1 w.1) w.2)
      (cotangentChart y.1 y, p) := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hq : cotangentChart y.1 y ∈ cotangentTarget y.1 := cotangentChart_mapsTo _ hself
  have hinv : cotangentChartInv y.1 (cotangentChart y.1 y) = y :=
    cotangentChart_left_inv _ hself
  have hsource : chartInv y.1 (cotangentChart y.1 y).1 ∈ (extChartAt (ComplexModel n) x).source := by
    change (cotangentChartInv y.1 (cotangentChart y.1 y)).1 ∈ (extChartAt (ComplexModel n) x).source
    rw [hinv]
    exact hy
  have hT := (cotangentChartTransition_contDiffAt y.1 x hq hsource).restrict_scalars ℝ
  have hT1 : ContDiffAt ℝ 1 (fun w => cotangentChart x (cotangentChartInv y.1 w))
      (cotangentChart y.1 y) := hT.of_le (by simp)
  have hTP : ContDiffAt ℝ 1 (fun w : CotangentCoord n × P =>
      (cotangentChart x (cotangentChartInv y.1 w.1), w.2)) (cotangentChart y.1 y, p) :=
    (hT1.comp (cotangentChart y.1 y, p) contDiffAt_fst).prodMk contDiffAt_snd
  have hB' : ContDiffAt ℝ 1
      (fun w : CotangentCoord n × P => B (cotangentChartInv x w.1) w.2)
      (cotangentChart x (cotangentChartInv y.1 (cotangentChart y.1 y)), p) := by
    simpa only [hinv] using hB
  have hcomp := hB'.comp (cotangentChart y.1 y, p) hTP
  apply hcomp.congr_of_eventuallyEq
  have hnear : {w : CotangentCoord n × P | w.1 ∈
      {u | u ∈ cotangentTarget y.1 ∧ chartInv y.1 u.1 ∈ (extChartAt (ComplexModel n) x).source}} ∈
      𝓝 (cotangentChart y.1 y, p) :=
    (isOpen_cotangentChartOverlap y.1 x).preimage continuous_fst |>.mem_nhds ⟨hq, hsource⟩
  filter_upwards [hnear] with w hw
  exact (congrArg (fun v => B v w.2) (cotangentChart_left_inv x hw.2)).symm

end Yau.Blueprint.V02WallTaylorProof
