import Yau.Proofs.F01NativeLogDetLevi
import Yau.Proofs.F01NativeLogDetEvolution
import Yau.Proofs.F01LaplacianLinearity

/-! Rebase the same actual potential flow at a later initial metric.
The linear scalar correction is computed from its actual determinant ratio. -/
noncomputable section
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def rebasedFlowPotential (α : HermitianField M) (h : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (a : ℝ) (x : M.Carrier) (s : ℝ) : ℝ :=
  U x (a + s) - U x a - s * flowLogDetRatio α h x a

theorem rebasedFlowPotential_initial (α : HermitianField M) (h : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (a : ℝ) (x : M.Carrier) :
    rebasedFlowPotential α h U a x 0 = 0 := by
  simp [rebasedFlowPotential]

theorem flow_logdet_rebase (α : HermitianField M) (h : ℝ → HermitianField M)
    (a s : ℝ) (x : M.Carrier) :
    flowLogDetRatio (h a) (fun r => h (a + r)) x s =
      flowLogDetRatio α h x (a + s) - flowLogDetRatio α h x a := by
  have hA := Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hB := Yau.LeafProofs.L12Aux.hMat_posDef (h a) x (chartPt x x) (mem_extChartAt_target x)
  have hC := Yau.LeafProofs.L12Aux.hMat_posDef (h (a + s)) x (chartPt x x) (mem_extChartAt_target x)
  have hAp := (Complex.pos_iff.mp hA.det_pos).1
  have hBp := (Complex.pos_iff.mp hB.det_pos).1
  have hCp := (Complex.pos_iff.mp hC.det_pos).1
  unfold flowLogDetRatio
  erw [Real.log_div hCp.ne' hBp.ne', Real.log_div hCp.ne' hAp.ne',
    Real.log_div hBp.ne' hAp.ne']
  ring

theorem rebased_metric_potential_identity
    (α : HermitianField M) (h : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (a s : ℝ)
    (hα : MetricSmooth α) (hha : MetricSmooth (h a))
    (hUa : SmoothFn (fun x => U x a)) (hUs : SmoothFn (fun x => U x (a + s)))
    (hPa : SmoothFn (fun x => flowLogDetRatio α h x a))
    (hpotA : ∀ x, gMat (h a) x = gMat α x - (a : ℂ) • ricci α x + levi (fun y => U y a) x)
    (hpotS : ∀ x, gMat (h (a + s)) x =
      gMat α x - ((a + s : ℝ) : ℂ) • ricci α x + levi (fun y => U y (a + s)) x) :
    ∀ x, gMat (h (a + s)) x = gMat (h a) x - (s : ℂ) • ricci (h a) x +
      levi (fun y => rebasedFlowPotential α h U a y s) x := by
  intro x
  have hdiff : SmoothFn (fun y => U y (a + s) - U y a) := fun b => (hUs b).sub (hUa b)
  have hmultiple : SmoothFn (fun y => s * flowLogDetRatio α h y a) :=
    fun b => contDiffOn_const.mul (hPa b)
  have hlevi : levi (fun y => flowLogDetRatio α h y a) x = -ricci (h a) x + ricci α x :=
    levi_logdet_ratio_native (h a) α hha hα x
  unfold rebasedFlowPotential
  rw [levi_sub_native hdiff hmultiple, levi_sub_native hUs hUa,
    levi_const_mul_native hPa s, hlevi, hpotS x, hpotA x]
  simp only [Complex.ofReal_add, add_smul, smul_add, smul_neg]
  abel

end Yau.NodeProofs.F01Aux
