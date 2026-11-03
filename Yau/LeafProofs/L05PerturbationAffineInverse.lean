import Yau.LeafProofs.L05PerturbationAffineMapC2
import Yau.LeafProofs.L05PerturbationCorePatches

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbInverseCenter {n : ℕ} (z : Point n) (r : ℝ) : Point n :=
  (-(r⁻¹) • z.1,-(r⁻¹)^2*z.2)

theorem perturb_inverse_center_apply {n : ℕ} (z : Point n) (r : ℝ) (p : Point n) :
    perturbCenter (perturbInverseCenter z r) r⁻¹ p=
      (r⁻¹ • (p.1-z.1),(r⁻¹)^2*(p.2-z.2)) := by
  apply Prod.ext
  · simp only [perturbCenter,perturbInverseCenter,smul_sub,neg_smul]
    abel
  · dsimp only [perturbCenter,perturbInverseCenter]
    ring

theorem perturb_center_inverse_left {n : ℕ} {r : ℝ} (hr : 0 < r) (z p : Point n) :
    perturbCenter z r (perturbCenter (perturbInverseCenter z r) r⁻¹ p)=p := by
  rw [perturb_inverse_center_apply]
  apply Prod.ext
  · simp only [perturbCenter,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    abel
  · dsimp only [perturbCenter]
    field_simp [hr.ne'] <;> ring

theorem perturb_inverse_center_back_mem {n : ℕ} {r : ℝ} (hr : 0 < r) (z : Point n)
    {p : Point n} (hp : p∈perturbBack z.1 (r/2) z.2) :
    perturbCenter (perturbInverseCenter z r) r⁻¹ p∈backward (1/2) := by
  have hx : ‖p.1-z.1‖ < r/2 := by simpa only [mem_ball,dist_eq_norm] using hp.1
  have hScale : r⁻¹*(r/2)=(1/2 : ℝ) := by field_simp [hr.ne']
  have hLo : -(r/2)^2 < p.2-z.2 := by linarith only [hp.2.1]
  have hLoScale : (r⁻¹)^2*(-(r/2)^2)=-(1/2 : ℝ)^2 := by
    field_simp [hr.ne'] <;> ring
  rw [perturb_inverse_center_apply]
  refine ⟨?_,?_,?_⟩
  · change dist (r⁻¹ • (p.1-z.1)) 0 < 1/2
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_lt_mul_of_pos_left hx (inv_pos.mpr hr)).trans_eq hScale
  · change -(1/2 : ℝ)^2 < (r⁻¹)^2*(p.2-z.2)
    have hh := mul_lt_mul_of_pos_left hLo (sq_pos_of_pos (inv_pos.mpr hr))
    rwa [hLoScale] at hh
  · change (r⁻¹)^2*(p.2-z.2) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hp.2.2)

theorem perturb_center_unscale_c2 {n : ℕ} {r : ℝ} (hr : 0 < r) (z : Point n)
    (h : Point n → ℝ)
    (hV : C2 (backward (1/2)) (fun q => h (perturbCenter z r q))) :
    C2 (perturbBack z.1 (r/2) z.2) h ∧
      ∀ p∈perturbBack z.1 (r/2) z.2,
        spatialD h p=r⁻¹ • spatialD (fun q => h (perturbCenter z r q))
          (perturbCenter (perturbInverseCenter z r) r⁻¹ p) ∧
        spatialDD h p=(r⁻¹)^2 • spatialDD (fun q => h (perturbCenter z r q))
          (perturbCenter (perturbInverseCenter z r) r⁻¹ p) ∧
        hessian h p=(r⁻¹)^2 • hessian (fun q => h (perturbCenter z r q))
          (perturbCenter (perturbInverseCenter z r) r⁻¹ p) ∧
        timeD (perturbBack z.1 (r/2) z.2) h p=(r⁻¹)^2*
          timeD (backward (1/2)) (fun q => h (perturbCenter z r q))
            (perturbCenter (perturbInverseCenter z r) r⁻¹ p) := by
  let P := perturbBack z.1 (r/2) z.2
  have hMap : MapsTo (perturbCenter (perturbInverseCenter z r) r⁻¹) P (backward (1/2)) :=
    fun p hp => perturb_inverse_center_back_mem hr z hp
  have hEq : (fun p => (fun q => h (perturbCenter z r q))
      (perturbCenter (perturbInverseCenter z r) r⁻¹ p))=h := by
    funext p
    change h (perturbCenter z r (perturbCenter (perturbInverseCenter z r) r⁻¹ p))=h p
    rw [perturb_center_inverse_left hr]
  have hPull := perturb_center_c2_map hV (perturbInverseCenter z r) r⁻¹ hMap
    (fun _ hp => perturb_back_uniqueDiff hp)
  rw [hEq] at hPull
  refine ⟨hPull,?_⟩
  intro p hp
  have hD := perturb_center_spatialD_map hV (perturbInverseCenter z r) r⁻¹ (hMap hp)
  have hDD := perturb_center_spatialDD_map hV (perturbInverseCenter z r) r⁻¹ (hMap hp)
  have hH := perturb_center_hessian_map hV (perturbInverseCenter z r) r⁻¹ (hMap hp)
  have hT := perturb_center_timeD_map hV (perturbInverseCenter z r) r⁻¹ hMap hp (perturb_back_uniqueDiff hp)
  rw [hEq] at hD hDD hH hT
  exact ⟨hD,hDD,hH,hT⟩

end Yau.LeafProofs.L05Aux
