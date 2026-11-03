import Yau.Proofs.F01TraceOrder
import Yau.Proofs.F01PotentialLaplacian

/-! The actual preliminary lower metric order gives a finite native
trace bound, and hence the Laplacian bound for the explicit proper penalty. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_le_dim_mul_of_lower_order {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) {C : ℝ} (hC : 0 < C)
    (horder : (H - ((C⁻¹ : ℝ) : ℂ) • A).PosSemidef) : traceWith H A ≤ C * n := by
  have hh := traceWith_posSemidef_nonneg hH horder
  rw [traceWith_sub, traceWith_self_posDef hH, traceWith_real_smul] at hh
  have hmul := mul_nonneg hC.le hh
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hmul
  linarith

theorem laplacian_bound_from_metric_comparison
    (α k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier)
    {C B : ℝ} (hC : 0 < C) (hB : 0 ≤ B)
    (horder : (gMat k x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef)
    (hLevi : ((B : ℂ) • gMat α x - levi f x).PosSemidef) :
    laplacian k f x ≤ B * (C * n) := by
  have hk := Yau.LeafProofs.L12Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  have htrace := traceWith_le_dim_mul_of_lower_order hk hC horder
  have hlevi := traceWith_mono hk hLevi
  rw [traceWith_real_smul] at hlevi
  exact hlevi.trans (mul_le_mul_of_nonneg_left htrace hB)

end Yau.NodeProofs.F01Aux
