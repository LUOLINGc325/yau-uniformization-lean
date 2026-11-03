import Yau.LeafProofs.L05
import Yau.LeafProofs.L05LogDetChuData

/-! The original Chu producer on a genuine positive-time backward
cylinder. Every structural log-determinant input is discharged by its
canonical finite-dimensional construction. No real Hessian bound is
assumed: the sole second-derivative range input is transformed. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L05Aux
variable {n : ℕ}

theorem native_logdet_backward_schauder
    (hn : 0 < n) {α β ell upper K B : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hell : 0 < ell) (hUpper : ell ≤ upper) (hK : 0 < K) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Point n → Sym n) (f u : Point n → ℝ),
      HolderBound β (backward 1) S K → HolderBound α (backward 1) f K →
      C2 (backward 1) u → (∀ p ∈ backward 1, |u p| ≤ B) →
      (∀ p ∈ backward 1,
        (((S p + complexHessianMap (hessian u p) : Sym n) : Mat n) -
          ell • (1 : Mat n)).PosSemidef ∧
        (upper • (1 : Mat n) - ((S p + complexHessianMap (hessian u p) : Sym n) : Mat n)).PosSemidef) →
      (∀ p ∈ backward 1,
        timeD (backward 1) u p - logDetReal (S p + complexHessianMap (hessian u p)) = f p) →
      SchauderBound (min α β) (backward (1 / 2)) u C := by
  obtain ⟨Kstar, hKstar, hKK, hKhalf, hKdim, hH1, hH2, hmod, hDF⟩ :=
    logDetReal_chuData (n := n) (beta := β) hell hUpper hK
  have hUp : 0 < upper := hell.trans_le hUpper
  have hell' : 0 < (1 / 2 : ℝ) * upper⁻¹ := mul_pos (by norm_num) (inv_pos.mpr hUp)
  have hInv : upper⁻¹ ≤ ell⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hell hUpper
  have hRange : (1 / 2 : ℝ) * upper⁻¹ ≤ (1 / 2 : ℝ) * ell⁻¹ :=
    mul_le_mul_of_nonneg_left hInv (by norm_num)
  obtain ⟨C, hC, hEstimate⟩ := (Yau.LeafProofs.L05).1 n hn α β
    ((1 / 2 : ℝ) * upper⁻¹) ((1 / 2 : ℝ) * ell⁻¹) Kstar K B
    hα hα1 hβ hβ1 hell' hRange hKstar hK.le hB
    (fun r => logDetDerivativeConstant n ell * r) hmod
  refine ⟨C, hC, ?_⟩
  intro S f u hS hf hu hSup hTransformed hEquation
  have hOrigin : ((0, 0) : Point n) ∈ backward 1 := by
    constructor <;> norm_num [backward, Metric.mem_ball, dist_zero_right]
  have hH3 : ChuH3 S Kstar β := by
    refine ⟨(hS.2.1 _ hOrigin).trans hKK, ?_⟩
    intro p hp q hq
    exact (hS.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hKK
      (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  exact hEstimate (slopeSet n ell upper) (logDetDomain n) (fun H _ => logDetReal H)
    S (fun H _ => complexHessianMap H) f u
    (slopeSet_isCompact n hell.le) (slopeSet_convex n ell upper)
    (slopeSet_nonempty n hUpper) hH1 hH2 hH3 hDF hf hu hSup hTransformed hEquation

end Yau.NodeProofs.F01Aux
