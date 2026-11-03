import Yau.Proofs.P08ScalarLevi

/-! The smooth convex scalar profile used off the zero set. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.NodeProofs.P08Aux

def logRegularizer (ε s : ℝ) : ℝ := Real.log (Real.exp s + ε)

theorem logRegularizer_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (logRegularizer ε) := by
  exact (Real.contDiff_exp.add contDiff_const).log (fun s => (by positivity : Real.exp s + ε ≠ 0))

theorem logRegularizer_hasDerivAt {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (logRegularizer ε) (Real.exp s / (Real.exp s + ε)) s := by
  exact ((Real.hasDerivAt_exp s).add_const ε).log (by positivity)

theorem logRegularizer_deriv {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (logRegularizer ε) s = Real.exp s / (Real.exp s + ε) :=
  (logRegularizer_hasDerivAt hε s).deriv

theorem logRegularizer_deriv_deriv {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (deriv (logRegularizer ε)) s = ε * Real.exp s / (Real.exp s + ε) ^ 2 := by
  have hfun : deriv (logRegularizer ε) = (fun s => Real.exp s / (Real.exp s + ε)) :=
    funext (logRegularizer_deriv hε)
  rw [hfun]
  change deriv (Real.exp / fun x => Real.exp x + ε) s = _
  rw [((Real.hasDerivAt_exp s).div ((Real.hasDerivAt_exp s).add_const ε)
    (by positivity)).deriv]
  ring

theorem logRegularizer_deriv_deriv_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ deriv (deriv (logRegularizer ε)) s := by
  rw [logRegularizer_deriv_deriv hε]
  positivity

end Yau.NodeProofs.P08Aux
