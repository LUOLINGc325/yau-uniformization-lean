import Yau.Proofs.F04Nonlinear
import Yau.Proofs.F04MassCutoff

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The exact nonlinear equation cancels the curvature term in the
 exponential density mass. Its spatial Laplacian remains the ACTUAL w,
 while the cutoff-time term is controlled by exp(w)-1. -/
theorem nonlinear_compact_mass_pointwise
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (u : Pt X → ℝ) (w χ : STF X) {t R a : ℝ}
    (hwD : ∀ x, HasDerivAt (w x) (deriv (w x) t) t)
    (hEq : ∀ x, deriv (w x) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
      (1-Real.exp (-w x t))*scalarCurvature (h t) x)
    (hw0 : ∀ x, 0 ≤ w x t) (hχt : ∀ x, deriv (χ x) t ≤ a*χ x t) (x : Pt X) :
    massCutoff u R x*
      ((deriv (fun s => Real.exp (w x s)-1) t*χ x t+(Real.exp (w x t)-1)*deriv (χ x) t)*density ρ x t-
        scalarCurvature (h t) x*((Real.exp (w x t)-1)*χ x t*density ρ x t)) ≤
      (χ x t*massCutoff u R x*laplacian (h t) (fun y => w y t) x)*density ρ x t+
        a*(massCutoff u R x*((Real.exp (w x t)-1)*χ x t*density ρ x t)) := by
  have hzD := ((hwD x).exp.sub_const 1).deriv
  have hCancel : deriv (fun s => Real.exp (w x s)-1) t-
      scalarCurvature (h t) x*(Real.exp (w x t)-1) = laplacian (h t) (fun y => w y t) x := by
    rw [hzD,hEq x]
    simpa only [mul_comm (Real.exp (w x t)-1) (scalarCurvature (h t) x)] using
      nonlinear_exponential_cancellation (w x t) (laplacian (h t) (fun y => w y t) x)
        (scalarCurvature (h t) x)
  have hZ : 0 ≤ Real.exp (w x t)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (hw0 x))
  have hTime := mul_le_mul_of_nonneg_left (hχt x)
    (mul_nonneg (mul_nonneg (massCutoff_range u R x).1 hZ) (density_pos ρ x t).le)
  calc
    _ = massCutoff u R x*χ x t*density ρ x t*
          (deriv (fun s => Real.exp (w x s)-1) t-scalarCurvature (h t) x*(Real.exp (w x t)-1))+
          (massCutoff u R x*(Real.exp (w x t)-1)*density ρ x t)*deriv (χ x) t := by ring
    _ = (χ x t*massCutoff u R x*laplacian (h t) (fun y => w y t) x)*density ρ x t+
          (massCutoff u R x*(Real.exp (w x t)-1)*density ρ x t)*deriv (χ x) t := by rw [hCancel]; ring
    _ ≤ _ := by nlinarith only [hTime]

end Yau.F04Proof
