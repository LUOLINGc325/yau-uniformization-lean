import Yau.LeafProofs.L05PerturbationPolynomialBounds
import Yau.LeafProofs.L05PerturbationPolynomialLimits
import Yau.LeafProofs.L05PerturbationRadiusInterpolation

open Filter Set Metric
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_polynomial_tail_bound {n : ℕ} {r eta Sc Sb SA Sq : ℝ} (hr : 0 < r)
    (cInf c qInf q : ℝ) (bInf b : Space n →L[ℝ] ℝ) (AInf A : Sym n)
    (hc : |cInf-c| ≤ Sc*r^(2+eta)) (hb : ‖bInf-b‖ ≤ Sb*r^(1+eta))
    (hA : ‖AInf-A‖ ≤ SA*r^eta) (hq : |qInf-q| ≤ Sq*r^eta)
    {p : Point n} (hp : p∈perturbClosed (0 : Space n) r 0) :
    |perturbPolynomial cInf bInf AInf qInf p-perturbPolynomial c b A q p| ≤
      (Sc+Sb+(1/2 : ℝ)*SA+Sq)*r^(2+eta) := by
  rw [perturb_polynomial_sub]
  have hBound := perturb_polynomial_closed_bound hr.le (cInf-c) (qInf-q) (bInf-b) (AInf-A) hc hb hA hq hp
  apply hBound.trans_eq
  simp only [Real.rpow_add hr,Real.rpow_one,Real.rpow_two]
  ring

theorem perturb_polynomial_discrete_remainder {n : ℕ} {rho eta Sc Sb SA Sq : ℝ}
    (hRho : 0 < rho) (u : Point n → ℝ)
    (c q : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ) (A : ℕ → Sym n)
    (cInf qInf : ℝ) (bInf : Space n →L[ℝ] ℝ) (AInf : Sym n)
    (hc : ∀ k : ℕ, |cInf-c k| ≤ Sc*(rho^k : ℝ)^(2+eta))
    (hb : ∀ k : ℕ, ‖bInf-b k‖ ≤ Sb*(rho^k : ℝ)^(1+eta))
    (hA : ∀ k : ℕ, ‖AInf-A k‖ ≤ SA*(rho^k : ℝ)^eta)
    (hq : ∀ k : ℕ, |qInf-q k| ≤ Sq*(rho^k : ℝ)^eta)
    (hError : ∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-perturbPolynomial (c k) (b k) (A k) (q k) p| ≤ (rho^k : ℝ)^(2+eta)) :
    ∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-perturbPolynomial cInf bInf AInf qInf p| ≤
        (1+Sc+Sb+(1/2 : ℝ)*SA+Sq)*(rho^k : ℝ)^(2+eta) := by
  intro k hk p hp
  have hTail := perturb_polynomial_tail_bound (eta := eta) (pow_pos hRho k)
    cInf (c k) qInf (q k) bInf (b k) AInf (A k) (hc k) (hb k) (hA k) (hq k) hp
  have hErr := hError k hk p hp
  have hTri : |u p-perturbPolynomial cInf bInf AInf qInf p| ≤
      |u p-perturbPolynomial (c k) (b k) (A k) (q k) p|+
      |perturbPolynomial cInf bInf AInf qInf p-perturbPolynomial (c k) (b k) (A k) (q k) p| := by
    have hEq : u p-perturbPolynomial cInf bInf AInf qInf p=
        (u p-perturbPolynomial (c k) (b k) (A k) (q k) p)+
        (perturbPolynomial (c k) (b k) (A k) (q k) p-perturbPolynomial cInf bInf AInf qInf p) := by ring
    rw [hEq]
    simpa only [abs_sub_comm] using abs_add_le
      (u p-perturbPolynomial (c k) (b k) (A k) (q k) p)
      (perturbPolynomial (c k) (b k) (A k) (q k) p-perturbPolynomial cInf bInf AInf qInf p)
  nlinarith only [hTri,hTail,hErr]

theorem perturb_polynomial_continuous_remainder {n : ℕ} {rho eta Sc Sb SA Sq : ℝ}
    (hRho : 0 < rho) (hRho1 : rho < 1) (heta : 0 < eta)
    (hJ : 0 ≤ 1+Sc+Sb+(1/2 : ℝ)*SA+Sq) (u : Point n → ℝ)
    (c q : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ) (A : ℕ → Sym n)
    (cInf qInf : ℝ) (bInf : Space n →L[ℝ] ℝ) (AInf : Sym n)
    (hc : ∀ k : ℕ, |cInf-c k| ≤ Sc*(rho^k : ℝ)^(2+eta))
    (hb : ∀ k : ℕ, ‖bInf-b k‖ ≤ Sb*(rho^k : ℝ)^(1+eta))
    (hA : ∀ k : ℕ, ‖AInf-A k‖ ≤ SA*(rho^k : ℝ)^eta)
    (hq : ∀ k : ℕ, |qInf-q k| ≤ Sq*(rho^k : ℝ)^eta)
    (hError : ∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-perturbPolynomial (c k) (b k) (A k) (q k) p| ≤ (rho^k : ℝ)^(2+eta)) :
    ∀ r : ℝ, 0 < r → r ≤ rho → ∀ p∈perturbClosed (0 : Space n) r 0,
      |u p-perturbPolynomial cInf bInf AInf qInf p| ≤
        ((1+Sc+Sb+(1/2 : ℝ)*SA+Sq)*rho^(-(2+eta)))*r^(2+eta) := by
  exact perturb_discrete_radius_bound hRho hRho1 (show 0 ≤ 2+eta by linarith) hJ
    u (perturbPolynomial cInf bInf AInf qInf)
    (perturb_polynomial_discrete_remainder hRho u c q b A cInf qInf bInf AInf hc hb hA hq hError)

end Yau.LeafProofs.L05Aux
