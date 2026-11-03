import Yau.Proofs.G04KahlerForm
import Yau.Proofs.G04RicciForm
import Yau.Proofs.G04LeviForms

/-! The native potential identity closes the limiting Kähler form. This
uses the computed Ricci and Levi forms of the original background. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

theorem matrixPairing_add_matrix (A B : Matrix (Fin n) (Fin n) ℂ)
    (u v : ComplexVector n) :
    matrixPairing (A + B) u v = matrixPairing A u v + matrixPairing B u v := by
  simp [matrixPairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem matrixPairing_sub_matrix (A B : Matrix (Fin n) (Fin n) ℂ)
    (u v : ComplexVector n) :
    matrixPairing (A - B) u v = matrixPairing A u v - matrixPairing B u v := by
  simp [matrixPairing, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem matrixPairing_smul_matrix (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (u v : ComplexVector n) :
    matrixPairing (c • A) u v = c * matrixPairing A u v := by
  simp only [matrixPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem closed_realForm_add (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : ClosedRealForm A) (hcB : ClosedRealForm B) :
    ClosedRealForm (A + B) := by
  intro x z hz I
  simp only [L03.formComponents_add]
  rw [L03.exteriorComponents_add_at _ _ z
    (L03.smoothRealForm_coefficient_differentiableAt A hA x hz)
    (L03.smoothRealForm_coefficient_differentiableAt B hB x hz), hcA x z hz I,
    hcB x z hz I, add_zero]

theorem omegaForm_eq_potential (g h : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (t : ℝ)
    (hpot : ∀ x, gMat h x = gMat g x - (t : ℂ) • ricci g x + levi f x) :
    omegaForm h = omegaForm g + (-t) • rhoForm g hg + ddRealForm f := by
  apply L03.realForm_eq_of_center_components
  intro x I
  rw [show omegaForm h = iotaRealForm (gMat h)
    (fun x => L12Aux.hMat_isHermitian h x (chartPt x x)) from rfl,
    iotaRealForm_center_components]
  simp only [L03.formComponents_add, Pi.add_apply, L03.formComponents_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [show omegaForm g = iotaRealForm (gMat g)
    (fun x => L12Aux.hMat_isHermitian g x (chartPt x x)) from rfl,
    iotaRealForm_center_components, rhoForm, iotaRealForm_center_components,
    dd_eq_iota f hf, iotaRealForm_center_components, hpot x]
  rw [matrixPairing_add_matrix, matrixPairing_sub_matrix, matrixPairing_smul_matrix]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero]
  ring

theorem kahlerClosed_of_closed_omega (h : HermitianField M)
    (hc : ClosedRealForm (omegaForm h)) : KahlerClosed h := by
  intro x a b c
  have hh := hc x (chartPt x x) (mem_extChartAt_target x) ![a,b,c]
  have hskew : (fun w => kahlerFormFn h x w c a) =
      (fun w => -kahlerFormFn h x w a c) := by
    funext w
    unfold kahlerFormFn
    rw [(h (chartInv x w)).conjugate_symmetric]
    simp
  rw [hskew]
  simp only [rDeriv, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  unfold exteriorComponents at hh
  simp only [omegaForm_components] at hh
  simp [Fin.sum_univ_succ, Fin.succAbove, rDeriv] at hh
  linarith

theorem kahlerClosed_of_native_potential (g h : HermitianField M)
    (hg : MetricSmooth g) (hkg : KahlerClosed g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (t : ℝ)
    (hpot : ∀ x, gMat h x = gMat g x - (t : ℂ) • ricci g x + levi f x) :
    KahlerClosed h := by
  apply kahlerClosed_of_closed_omega
  rw [omegaForm_eq_potential g h hg f hf t hpot]
  exact closed_realForm_add _ _
    (L03.smoothRealForm_add _ _ (omegaForm_smooth g hg)
      (L03.smoothRealForm_smul _ _ (rhoForm_smooth g hg)))
    (dd_smooth f hf)
    (closed_realForm_add _ _ (omegaForm_smooth g hg)
      (L03.smoothRealForm_smul _ _ (rhoForm_smooth g hg))
      (omegaForm_closed g hg hkg)
      (closedRealForm_smul _ _ (rhoForm_smooth g hg) (rhoForm_closed g hg)))
    (dd_properties f hf).2.2.1

end Yau.NodeProofs.F01Aux
