import Yau.Proofs.F01DeterminantMetricLower
import Yau.Proofs.F01NativeLogDetEvolution

/-! A lower bound for the actual logarithmic determinant converts the
upper Hermitian estimate into a genuine positive metric lower estimate. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem metric_exp_lower_of_logdet_and_exp_upper
    {H K : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (hK : K.PosDef)
    {A B : ℝ} (hB : 0 ≤ B)
    (hupper : ((Real.exp B : ℂ) • H - K).PosSemidef)
    (hlog : -A ≤ Real.log (K.det.re / H.det.re)) :
    (K - (Real.exp (-(A + (n : ℝ) * B)) : ℂ) • H).PosSemidef := by
  have hpos : 0 < K.det.re / H.det.re :=
    div_pos (Complex.pos_iff.mp hK.det_pos).1 (Complex.pos_iff.mp hH.det_pos).1
  have hdet : Real.exp (-A) ≤ K.det.re / H.det.re := by
    simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
  have hlower := metric_lower_of_determinant_and_upper hH hK
    (Real.one_le_exp_iff.mpr hB) hupper hdet
  have he : Real.exp (-A) / (Real.exp B) ^ n = Real.exp (-(A + (n : ℝ) * B)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    ring
  rw [he] at hlower
  exact hlower

theorem flow_metric_exp_lower_of_logdet
    {M : ComplexManifold n} (α : HermitianField M) (h : ℝ → HermitianField M)
    {A B : ℝ} (hB : 0 ≤ B) (x : M.Carrier) (t : ℝ)
    (hupper : ((Real.exp B : ℂ) • gMat α x - gMat (h t) x).PosSemidef)
    (hlog : -A ≤ flowLogDetRatio α h x t) :
    (gMat (h t) x - (Real.exp (-(A + (n : ℝ) * B)) : ℂ) • gMat α x).PosSemidef :=
  metric_exp_lower_of_logdet_and_exp_upper
    (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
    (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
    hB hupper hlog

end Yau.NodeProofs.F01Aux
