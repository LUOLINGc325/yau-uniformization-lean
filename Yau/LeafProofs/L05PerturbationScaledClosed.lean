import Yau.LeafProofs.L05PerturbationPolynomialUpdate

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_iter_scaled_closed_iff {n : ℕ} {r : ℝ} (hr : 0 < r) (R : ℝ) (p : Point n) :
    perturbScale r p∈perturbClosed (0 : Space n) (r*R) 0 ↔
      p∈perturbClosed (0 : Space n) R 0 := by
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hLo : -(r*R)^2 ≤ r^2*p.2 ↔ -R^2 ≤ p.2 := by
    rw [show -(r*R)^2=r^2*(-R^2) from by ring]
    exact mul_le_mul_iff_right₀ hr2
  have hHi : r^2*p.2 ≤ 0 ↔ p.2 ≤ 0 := by
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hr2 : r^2*p.2 ≤ r^2*0 ↔ p.2 ≤ 0)
  simp only [perturbScale,perturbClosed,mem_prod,mem_closedBall,mem_Icc,zero_sub]
  change (dist (r • p.1) 0 ≤ r*R ∧ -(r*R)^2 ≤ r^2*p.2 ∧ r^2*p.2 ≤ 0) ↔
    (dist p.1 0 ≤ R ∧ -R^2 ≤ p.2 ∧ p.2 ≤ 0)
  simp only [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
    mul_le_mul_iff_right₀ hr,hLo,hHi]

theorem perturb_iter_scale_inverse {n : ℕ} {r : ℝ} (hr : 0 < r) (p : Point n) :
    perturbScale r (perturbScale r⁻¹ p)=p := by
  rw [perturbScale_comp,mul_inv_cancel₀ hr.ne',perturbScale_one]

theorem perturb_iter_error_transfer {n : ℕ} {r rho eta : ℝ} (hr : 0 < r) (hRho : 0 < rho)
    (u : Point n → ℝ) (c d q s : ℝ) (b e : Space n →L[ℝ] ℝ) (A B : Sym n)
    (hCorrect : ∀ p∈perturbClosed (0 : Space n) rho 0,
      |perturbIterSolution u c b A q r eta p-perturbPolynomial d e B s p| ≤ rho^(2+eta)) :
    ∀ p∈perturbClosed (0 : Space n) (r*rho) 0,
      |u p-perturbPolynomial (c+r^(2+eta)*d) (b+r^(1+eta) • e) (A+r^eta • B) (q+r^eta*s) p| ≤
        (r*rho)^(2+eta) := by
  intro p hp
  let z := perturbScale r⁻¹ p
  let P := perturbPolynomial (c+r^(2+eta)*d) (b+r^(1+eta) • e) (A+r^eta • B) (q+r^eta*s)
  have hInv : perturbScale r z=p := perturb_iter_scale_inverse hr p
  have hz : z∈perturbClosed (0 : Space n) rho 0 :=
    (perturb_iter_scaled_closed_iff hr rho z).mp (by rwa [hInv])
  have hBound := hCorrect z hz
  have hPower : 0 < r^(2+eta) := Real.rpow_pos_of_pos hr _
  have hUpdate := perturb_iter_polynomial_update (eta := eta) hr c d q s b e A B z
  have hExpr : u p-P p=r^(2+eta)*(perturbIterSolution u c b A q r eta z-perturbPolynomial d e B s z) := by
    calc
      _ = u (perturbScale r z)-P (perturbScale r z) := congrArg (fun w => u w-P w) hInv.symm
      _ = _ := by
        change u (perturbScale r z)-perturbPolynomial (c+r^(2+eta)*d) (b+r^(1+eta) • e)
          (A+r^eta • B) (q+r^eta*s) (perturbScale r z)= _
        rw [hUpdate]
        dsimp only [perturbIterSolution]
        field_simp [hPower.ne']
        ring
  change |u p-P p| ≤ (r*rho)^(2+eta)
  rw [hExpr,abs_mul,abs_of_pos hPower]
  exact (mul_le_mul_of_nonneg_left hBound hPower.le).trans_eq (Real.mul_rpow hr.le hRho.le).symm

theorem perturb_iter_sup_of_error {n : ℕ} {r eta c q : ℝ} (hr : 0 < r)
    (u : Point n → ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    (hError : ∀ p∈perturbClosed (0 : Space n) r 0,
      |u p-perturbPolynomial c b A q p| ≤ r^(2+eta)) :
    ∀ p∈backward 1, |perturbIterSolution u c b A q r eta p| ≤ 1 := by
  intro p hp
  have hpC : p∈perturbClosed (0 : Space n) 1 0 :=
    ⟨ball_subset_closedBall hp.1,by simpa only [one_pow,zero_sub] using hp.2.1.le,hp.2.2⟩
  have hMem : perturbScale r p∈perturbClosed (0 : Space n) r 0 := by
    simpa only [mul_one] using (perturb_iter_scaled_closed_iff hr 1 p).mpr hpC
  have hPos : 0 < r^(2+eta) := Real.rpow_pos_of_pos hr _
  dsimp only [perturbIterSolution]
  rw [abs_mul,abs_of_pos (inv_pos.mpr hPos)]
  exact (mul_le_mul_of_nonneg_left (hError _ hMem) (inv_pos.mpr hPos).le).trans_eq
    (inv_mul_cancel₀ hPos.ne')

theorem perturb_iter_initial_solution {n : ℕ} (u : Point n → ℝ) (eta : ℝ) :
    perturbIterSolution u 0 0 0 0 1 eta=u := by
  funext p
  simp [perturbIterSolution,perturbScale_one,perturbPolynomial,perturbQuad]

theorem perturb_iter_initial_operator {n : ℕ} (Phi : Sym n → Point n → ℝ) (eta : ℝ)
    (h0 : Phi 0 (0,0)=0) : perturbIterOperator Phi 0 1 eta=Phi := by
  funext H p
  simp [perturbIterOperator,perturbScale_one,h0]

theorem perturb_iter_initial_source {n : ℕ} (f : Point n → ℝ) (eta : ℝ)
    (h0 : f (0,0)=0) : perturbIterSource f 1 eta=f := by
  funext p
  simp [perturbIterSource,perturbScale_one,h0]

end Yau.LeafProofs.L05Aux
