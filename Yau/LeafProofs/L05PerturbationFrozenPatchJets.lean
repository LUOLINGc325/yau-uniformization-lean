import Yau.LeafProofs.L05PerturbationAffineInverse
import Yau.LeafProofs.L05PerturbationFrozenRescale
import Yau.LeafProofs.L05PerturbationActualEquation
import Yau.LeafProofs.L05PerturbationBilinearBounds
import Yau.LeafProofs.L05PerturbationRescaledOperator

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_half_open_subset_unit {n : ℕ} : perturbOpen (0 : Space n) (1/2) 0⊆unitOpen n := by
  intro p hp
  refine ⟨ball_subset_ball (by norm_num) hp.1,?_,hp.2.2⟩
  have ht := hp.2.1
  change (-1 : ℝ) < p.2
  norm_num at ht
  linarith

theorem perturb_frozen_patch_jets_of_autonomous {n : ℕ} {ell L eta0 C0 : ℝ}
    (hAuto : ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ univ F → F 0=0 → ∀ v : Point n → ℝ, ContinuousOn v (unitClosed n) →
      (∀ p∈unitClosed n, |v p| ≤ 1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) v →
      SchauderBound eta0 (backward (1/2)) v C0)
    {r : ℝ} (hr : 0 < r) (z : Point n)
    (hBuf : perturbClosed z.1 r z.2 ⊆ perturbBack (0 : Space n) (1/2) 0)
    {F : Sym n → ℝ} (hF : Continuous F) (hE : globalElliptic F ell L)
    (hConc : ConcaveOn ℝ univ F) (h0 : F 0=0) {h : Point n → ℝ}
    (hC : ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0))
    (hSup : ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1)
    (hSol : viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
      (fun H _ => F H) (fun _ => 0) h) :
    C2 (perturbBack z.1 (r/2) z.2) h ∧
      (∀ p∈perturbBack z.1 (r/2) z.2,
        ‖hessian h p‖ ≤ (r⁻¹)^2*((Fintype.card (RIdx n) : ℝ)*C0)) ∧
      ∀ p∈perturbBack z.1 (r/2) z.2,
        timeD (perturbBack z.1 (r/2) z.2) h p=F (hessian h p) := by
  let v := fun p => h (perturbCenter z r p)
  let G := perturbFrozenRescale F r
  have hGData := perturb_frozen_rescale_data hr hF hE hConc
  have hVData := perturb_frozen_patch_data hr z hBuf h0 hC hSup hSol
  have hV := hAuto G hGData.1 hGData.2.1 hGData.2.2.1 hGData.2.2.2 v hVData.1 hVData.2.1 hVData.2.2
  have hUnscale := perturb_center_unscale_c2 hr z h hV.1
  have hNative : viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
      (fun H _ => G H) (fun _ => 0) v := by
    constructor
    · intro p hp
      exact hVData.2.2.1 p (perturb_half_open_subset_unit hp)
    · intro p hp
      exact hVData.2.2.2 p (perturb_half_open_subset_unit hp)
  have hActual := perturb_actual_equation_top (by norm_num : (0 : ℝ) < 1/2) hGData.1 hV.1 hNative
  have hCancel : (r⁻¹)^2*r^2=1 := by rw [← mul_pow,inv_mul_cancel₀ hr.ne',one_pow]
  refine ⟨hUnscale.1,?_,?_⟩
  · intro p hp
    have hy := perturb_inverse_center_back_mem hr z hp
    have hMat := perturb_matrix_norm_le_card (hessian v (perturbCenter (perturbInverseCenter z r) r⁻¹ p))
    rw [← perturb_spatialDD_eq_bilinear hV.1 hy] at hMat
    have hScalar := mul_le_mul_of_nonneg_left (hV.2.2.2.1.2.1 _ hy)
      (show 0 ≤ (Fintype.card (RIdx n) : ℝ) by positivity)
    rw [(hUnscale.2 p hp).2.2.1,perturb_sym_smul_norm,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hMat.trans hScalar) (sq_nonneg _)
  · intro p hp
    have hy := perturb_inverse_center_back_mem hr z hp
    calc
      _ = (r⁻¹)^2*timeD (backward (1/2)) v (perturbCenter (perturbInverseCenter z r) r⁻¹ p) :=
        (hUnscale.2 p hp).2.2.2
      _ = (r⁻¹)^2*G (hessian v (perturbCenter (perturbInverseCenter z r) r⁻¹ p)) := by rw [hActual _ hy]
      _ = F ((r⁻¹)^2 • hessian v (perturbCenter (perturbInverseCenter z r) r⁻¹ p)) := by
        dsimp only [G]
        rw [perturb_frozen_rescale_eq hr F h0,← mul_assoc,hCancel,one_mul]
      _ = F (hessian h p) := congrArg F (hUnscale.2 p hp).2.2.1.symm

end Yau.LeafProofs.L05Aux
