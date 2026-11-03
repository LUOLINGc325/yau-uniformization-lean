import Yau.LeafProofs.L05PerturbationVariableHolder
import Yau.LeafProofs.L05PerturbationPolynomialSubtraction

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_classical_pucci_sub {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) {u f : Point n → ℝ} (hu : C2 Q u)
    (hRes : ∀ p∈Q, timeD Q u p-pucciPlus ell L (hessian u p) ≤ f p) :
    viscositySub Q (fun H _ => pucciPlus ell L H) f u := by
  intro p hp phi hphi ht
  obtain ⟨hTime,hMat⟩ := parabolic_touchAbove_jets hQ hu hp hphi ht
  have hP : ((hessian phi p : Mat n)+(0 : ℝ) • (1 : Mat n)-(hessian u p : Mat n)).PosSemidef := by
    simpa only [zero_smul,add_zero] using hMat
  have hMono := jet_pucci_le_of_matrix_le hell hL (le_rfl : (0 : ℝ) ≤ 0) hP
  simp only [zero_mul,add_zero] at hMono
  have hActual := hRes p hp
  rw [hTime] at hActual
  change timeD univ phi p-pucciPlus ell L (hessian phi p) ≤ f p
  linarith only [hActual,hMono]

theorem perturb_frozen_difference_residual {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (hQB : Q⊆backward 1) {ell L delta B : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hd : 0 ≤ delta)
    {Phi : Sym n → Point n → ℝ} {f u h : Point n → ℝ}
    (hE : ∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L)
    (hu : C2 (backward 1) u) (hh : C2 Q h)
    (hUeq : ∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)
    (hHeq : ∀ p∈Q, timeD Q h p=Phi (hessian h p) (0,0))
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, |Phi H p-Phi H (0,0)| ≤ delta*(1+‖H‖))
    (hf : ∀ p∈backward 1, |f p| ≤ delta) (hBound : ∀ p∈Q, ‖hessian h p‖ ≤ B) :
    viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => delta*(2+B)) (fun p => u p-h p) ∧
      viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => delta*(2+B)) (fun p => h p-u p) := by
  have huQ := c2_open_restrict hQ hQB hu
  have hTimeU : ∀ p∈Q, timeD Q u p=timeD (backward 1) u p :=
    fun p hp => timeD_open_restrict hQ hQB u hp
  constructor
  · apply perturb_classical_pucci_sub hQ hell hL (L16Aux.c2_sub huQ hh)
    intro p hp
    rw [L16Aux.timeD_sub huQ hh hp,perturb_c2_hessian_sub huQ hh hp,hTimeU p hp,hHeq p hp]
    have hPucci := jet_elliptic_difference_le_pucci hell hL (hE p (hQB hp)) (hessian u p) (hessian h p)
    have hC := (abs_le.mp (hCoeff (hessian h p) p (hQB hp))).2
    have hF := (abs_le.mp (hf p (hQB hp))).2
    have hNorm := mul_le_mul_of_nonneg_left (hBound p hp) hd
    have hEq := hUeq p (hQB hp)
    nlinarith only [hPucci,hC,hF,hNorm,hEq]
  · apply perturb_classical_pucci_sub hQ hell hL (L16Aux.c2_sub hh huQ)
    intro p hp
    rw [L16Aux.timeD_sub hh huQ hp,perturb_c2_hessian_sub hh huQ hp,hTimeU p hp,hHeq p hp]
    have hPucci := jet_elliptic_difference_le_pucci hell hL (hE p (hQB hp)) (hessian h p) (hessian u p)
    have hC := (abs_le.mp (hCoeff (hessian h p) p (hQB hp))).1
    have hF := (abs_le.mp (hf p (hQB hp))).1
    have hNorm := mul_le_mul_of_nonneg_left (hBound p hp) hd
    have hEq := hUeq p (hQB hp)
    nlinarith only [hPucci,hC,hF,hNorm,hEq]

end Yau.LeafProofs.L05Aux
