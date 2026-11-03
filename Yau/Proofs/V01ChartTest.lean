import Yau.Proofs.V03Charts

/-! V01 scratch source: every test is pulled back through the one original
cotangent chart. Chart round trips retain their actual target hypothesis. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n : ℕ} {M : ComplexManifold n}

def chartTest (x : M.Carrier)
    (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (y : CotangentPoint M) (t : ℝ) : ℝ :=
  ψ ((cotangentChart x y).1, (cotangentChart x y).2, t)

theorem chartTest_chartInv (x : M.Carrier)
    (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) (t : ℝ) :
    chartTest x ψ (cotangentChartInv x z) t = ψ (z.1, z.2, t) := by
  unfold chartTest
  rw [Yau.Blueprint.V03Proof.cotangentChart_right_inv x hz]

theorem chartTest_contDiffOn (x : M.Carrier)
    {ψ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ)
    {V : Set (CotangentCoord n × ℝ)}
    (hV : V ⊆ cotangentTarget x ×ˢ Set.univ) :
    ContDiffOn ℝ ∞
      (fun p : CotangentCoord n × ℝ => chartTest x ψ (cotangentChartInv x p.1) p.2) V := by
  have hassoc : ContDiff ℝ ∞
      (fun p : CotangentCoord n × ℝ => (p.1.1, p.1.2, p.2)) := by
    fun_prop
  apply (hψ.comp hassoc).contDiffOn.congr
  intro p hp
  exact chartTest_chartInv x ψ (hV hp).1 p.2

end Yau.Blueprint.V01Proof
