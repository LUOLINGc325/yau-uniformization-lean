import Yau.LeafProofs.L05LogDetChuData
import Yau.LeafProofs.L05MongeInitialShift

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates L16Aux

set_option maxHeartbeats 1800000 in
theorem mongeAmpereInitialSchauder_of_chu (hChu : ChuTransformedHessian) :
    MongeAmpereInitialSchauder := by
  intro n hn alpha beta ell L K B ha0 ha1 hb0 hb1 hell hL hK hB
  obtain ⟨Kstar,hKstar,hKK,hKhalf,hKdim,hH1,hH2,hmod,hDF⟩ :=
    logDetReal_chuData (n := n) (beta := beta) hell hL hK
  have hLp : 0 < L := hell.trans_le hL
  have he0 : 0 < (1/2:ℝ)*L⁻¹ := mul_pos (by norm_num) (inv_pos.mpr hLp)
  have hInv : L⁻¹ ≤ ell⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hell hL
  have heL : (1/2:ℝ)*L⁻¹ ≤ (1/2:ℝ)*ell⁻¹ := mul_le_mul_of_nonneg_left hInv (by norm_num)
  obtain ⟨C,hC,hEst⟩ := hChu n hn alpha beta ((1/2:ℝ)*L⁻¹) ((1/2:ℝ)*ell⁻¹)
    Kstar K B ha0 ha1 hb0 hb1 he0 heL hKstar hK.le hB
    (fun r => logDetDerivativeConstant n ell*r) hmod
  refine ⟨C,hC,?_⟩
  intro A u hAsmooth hApos
  dsimp only
  intro hS hf hu hub hzero hRange hPDE
  have hMap : Set.MapsTo (timeTranslatePoint (1/4:ℝ)) (backward (n := n) 1)
      (cylinder (Metric.ball 0 1) (-1) 1) := fun p hp =>
    (timeTranslatePoint_mem_buffer Set.Subset.rfl (by norm_num : (-1:ℝ) < -(1^2)+(1/4))
      (by norm_num : (1/4:ℝ) < 1) hp).1
  have hSshift : HolderBound beta (backward 1) (timeTranslate (1/4:ℝ) (clampedBackground A)) K :=
    holderBound_timeTranslate_set hMap hS
  have hfshift : HolderBound alpha (backward 1) (timeTranslate (1/4:ℝ) (backgroundSource A)) K :=
    holderBound_timeTranslate_set hMap hf
  have hOrigin : ((0,0) : Point n) ∈ backward 1 := by
    refine ⟨Metric.mem_ball_self (by norm_num),?_⟩
    norm_num
  have hH3 : ChuH3 (timeTranslate (1/4:ℝ) (clampedBackground A)) Kstar beta := by
    refine ⟨(hSshift.2.1 _ hOrigin).trans hKK,?_⟩
    intro p hp q hq
    exact (hSshift.2.2 p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (abs_nonneg _) _)))
  have huShift : C2 (backward 1) (timeTranslate (1/4:ℝ) u) :=
    c2_timeTranslate_backward_buffer Set.Subset.rfl (by norm_num : (-1:ℝ) < -(1^2)+(1/4))
      (by norm_num : (1/4:ℝ) < 1) hu
  have hShiftRange (p : Point n) (hp : p ∈ backward 1) :
      timeTranslate (1/4:ℝ) (clampedBackground A) p+
        complexHessianMap (hessian (timeTranslate (1/4:ℝ) u) p) ∈ slopeSet n ell L := by
    rw [hessian_timeTranslate]
    exact hRange _ (hMap hp)
  have hShiftPDE (p : Point n) (hp : p ∈ backward 1) :
      timeD (backward 1) (timeTranslate (1/4:ℝ) u) p-
        logDetReal (timeTranslate (1/4:ℝ) (clampedBackground A) p+
          complexHessianMap (hessian (timeTranslate (1/4:ℝ) u) p))=
        timeTranslate (1/4:ℝ) (backgroundSource A) p := by
    rw [timeD_timeTranslate_backward_buffer Set.Subset.rfl
      (by norm_num : (-1:ℝ) < -(1^2)+(1/4)) (by norm_num : (1/4:ℝ) < 1) hu hp,
      hessian_timeTranslate]
    exact hPDE _ (hMap hp)
  have hsol := hEst (slopeSet n ell L) (logDetDomain n) (fun H _ => logDetReal H)
    (timeTranslate (1/4:ℝ) (clampedBackground A)) (fun H _ => complexHessianMap H)
    (timeTranslate (1/4:ℝ) (backgroundSource A)) (timeTranslate (1/4:ℝ) u)
    (slopeSet_isCompact n hell.le) (slopeSet_convex n ell L) (slopeSet_nonempty n hL)
    hH1 hH2 hH3 hDF hfshift huShift (fun p hp => hub _ (hMap hp)) hShiftRange hShiftPDE
  exact schauderBound_initial_of_shifted (lt_min ha0 hb0) hu hzero hsol

end Yau.LeafProofs.L05Aux
