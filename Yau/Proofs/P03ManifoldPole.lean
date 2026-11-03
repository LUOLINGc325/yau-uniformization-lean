import Yau.Proofs.P03Cutoffs
import Yau.Proofs.P03PoleRegularization

open scoped Manifold Topology ContDiff
open Filter Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine global cutoff logarithmic pole in an original manifold chart. -/
def manifoldCutoffPole (c : ℝ) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (ε : ℝ) (x : M.Carrier) : ℝ :=
  c * (b x * modelLogPole (chartPt a a) ε (chartPt a x))

theorem manifoldCutoffPole_smooth (c : ℝ) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) {ε : ℝ} (hε : 0 < ε) :
    SmoothFn (manifoldCutoffPole c b ε) := by
  letI := real_manifold M
  have hg : ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ) ∞
      (fun x : M.Carrier => modelLogPole (chartPt a a) ε (chartPt a x))
      (chartAt (ComplexVector n) a).source := by
    intro x hx
    have h := (modelLogPole_contDiff (chartPt a a) hε).comp_contMDiffWithinAt
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (x := a) x hx)
    convert! h using 1
  have hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ) ∞ (manifoldCutoffPole c b ε) := by
    convert! (contMDiff_const (c := c)).mul (b.contMDiff_smul hg) using 1
  exact contMDiff_real_chart hf

theorem manifoldCutoffPole_tsupport (c : ℝ) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (ε : ℝ) :
    tsupport (manifoldCutoffPole c b ε) ⊆ tsupport (b : M.Carrier → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra hb
  have hb0 : b x = 0 := Function.notMem_support.mp hb
  exact hx (by simp only [manifoldCutoffPole, hb0, zero_mul, mul_zero])

theorem manifoldCutoffPole_compactSupport (c : ℝ) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (ε : ℝ) :
    HasCompactSupport (manifoldCutoffPole c b ε) :=
  b.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (manifoldCutoffPole_tsupport c b ε)

theorem manifoldCutoffPole_inChart (c : ℝ) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (ε : ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    inChart a (manifoldCutoffPole c b ε) z =
      cutoffPoleRegularization c b.toContDiffBump (chartPt a a) ε z := by
  have hx : chartInv a z ∈ (chartAt (ComplexVector n) a).source := by
    change (extChartAt (ComplexModel n) a).symm z ∈ (chartAt (ComplexVector n) a).source
    simpa only [extChartAt_source] using (extChartAt (ComplexModel n) a).map_target hz
  have hb := b.eqOn_source hx
  have hi : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel n) a).right_inv hz
  change c * (b (chartInv a z) * modelLogPole (chartPt a a) ε (chartPt a (chartInv a z))) = _
  rw [hi, hb]
  change c * (b.toContDiffBump (chartPt a (chartInv a z)) * modelLogPole (chartPt a a) ε z) = _
  rw [hi]
  exact (mul_assoc _ _ _).symm

end Yau.NodeProofs.P03Aux
