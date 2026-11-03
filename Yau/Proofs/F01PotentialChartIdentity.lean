import Yau.Proofs.F01ScalarChartSmooth
import Yau.Proofs.F01LeviChartNaturality
import Yau.Proofs.F01ChartLogDet

/-! The original native metric-potential identity becomes an actual scalar
complex-Hessian difference in every holomorphic coordinate chart. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def localFlowPotential (α : HermitianField M) (u : M.Carrier → ℝ) (t : ℝ)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) : ℝ :=
  u (e z) + t * Real.log (pullbackMatrix α e z).det.re

theorem localFlowPotential_contDiffOn (α : HermitianField M) (hα : MetricSmooth α)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    ContDiffOn ℝ ∞ (localFlowPotential α u t e) e.source :=
  (smoothFn_comp_holomorphic_chart u hu e he).add
    (contDiffOn_const.mul (pullback_logdet_contDiffOn α hα e he hei))

theorem metric_potential_identity_in_chart (α k : HermitianField M) (hα : MetricSmooth α)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat α x - (t : ℂ) • ricci α x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    pullbackMatrix k e z - pullbackMatrix α e z = leviC (localFlowPotential α u t e) z := by
  let a := e z
  let J := linearMatrix (coordinateDifferential e a z)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hαc : pullbackMatrix α e z = Jᴴ * gMat α a * J :=
    pullbackMatrix_eq_congruence α e a z ha
  have hkc : pullbackMatrix k e z = Jᴴ * gMat k a * J :=
    pullbackMatrix_eq_congruence k e a z ha
  have hRc : pullbackRicci α e z = Jᴴ * ricci α a * J :=
    pullbackRicci_eq_ricci α hα e he hei hz
  have hUc : leviC (fun w => u (e w)) z = Jᴴ * levi u a * J :=
    leviC_holomorphic_chart u hu e he hz
  have heq : pullbackMatrix k e z = pullbackMatrix α e z -
      (t : ℂ) • pullbackRicci α e z + leviC (fun w => u (e w)) z := by
    rw [hkc, hpot a]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [← hαc, ← hRc, ← hUc]
  have hUs : ContDiffAt ℝ 2 (fun w => u (e w)) z :=
    ((smoothFn_comp_holomorphic_chart u hu e he).contDiffAt (e.open_source.mem_nhds hz)).of_le (by simp)
  have hLs : ContDiffAt ℝ 2 (fun w => Real.log (pullbackMatrix α e w).det.re) z :=
    ((pullback_logdet_contDiffOn α hα e he hei).contDiffAt (e.open_source.mem_nhds hz)).of_le (by simp)
  change pullbackMatrix k e z - pullbackMatrix α e z =
    leviC (fun w => u (e w) + t * Real.log (pullbackMatrix α e w).det.re) z
  rw [leviC_add hUs (contDiffAt_const.mul hLs), leviC_const_mul hLs t,
    heq, pullbackRicci, smul_neg, sub_neg_eq_add]
  abel

end Yau.NodeProofs.F01Aux
