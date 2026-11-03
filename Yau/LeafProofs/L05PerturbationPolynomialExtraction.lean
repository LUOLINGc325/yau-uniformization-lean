import Yau.LeafProofs.L05PerturbationPolynomialExtractionIdentities
import Yau.LeafProofs.L05PerturbationPolynomialExtractionNorm

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- Two time points and three spatial points extract the actual coefficients,
with the dimension-free bilinear operator norm and arbitrary cylinder center. -/
theorem perturb_polynomial_coefficients {n : ℕ} {r B T : ℝ}
    (hr : 0<r) (hB : 0≤B) (x : Space n)
    (c1 c2 q1 q2 : ℝ) (b1 b2 : Space n →L[ℝ] ℝ) (A1 A2 : Sym n)
    (hb : ∀ p∈perturbClosed x r T,
      |perturbPolynomial c1 b1 A1 q1 p-
        perturbPolynomial c2 b2 A2 q2 p|≤B) :
    |q1-q2|≤2*B/r^2 ∧
      ‖spatialDD (perturbPolynomial c1 b1 A1 q1) (0,0)-
        spatialDD (perturbPolynomial c2 b2 A2 q2) (0,0)‖≤4*B/r^2 := by
  let D : Point n → ℝ := fun p => perturbPolynomial c1 b1 A1 q1 p-perturbPolynomial c2 b2 A2 q2 p
  let a := perturbBilinear A1-perturbBilinear A2
  have hrr : 0<r^2 := sq_pos_of_pos hr
  have htime : T-r^2≤T := sub_le_self _ (sq_nonneg r)
  have hcenter : (x,T)∈perturbClosed x r T := ⟨mem_closedBall_self hr.le,htime,le_rfl⟩
  have hbottom : (x,T-r^2)∈perturbClosed x r T := ⟨mem_closedBall_self hr.le,le_rfl,htime⟩
  have hdc : |D (x,T)|≤B := hb _ hcenter
  have hdb : |D (x,T-r^2)|≤B := hb _ hbottom
  have htimeId : D (x,T)-D (x,T-r^2)=(q1-q2)*r^2 := by
    dsimp only [D,perturbPolynomial]
    ring
  have hq : |q1-q2|≤2*B/r^2 := by
    apply (le_div_iff₀ hrr).mpr
    have hh : |(q1-q2)*r^2|≤2*B := by
      rw [← htimeId]
      exact (abs_sub _ _).trans (by linarith only [hdc,hdb])
    simpa only [abs_mul,abs_of_pos hrr] using hh
  have hK : 0≤4*B/r^2 := div_nonneg (by positivity) hrr.le
  have hDiag : ∀ e : Space n, ‖e‖=1 → |a e e|≤4*B/r^2 := by
    intro e he
    have hvec : ‖r • e‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,he,mul_one]
    have hplus : (x+r • e,T)∈perturbClosed x r T := by
      refine ⟨?_,htime,le_rfl⟩
      simp only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,hvec,le_refl]
    have hminus : (x-r • e,T)∈perturbClosed x r T := by
      refine ⟨?_,htime,le_rfl⟩
      rw [mem_closedBall,dist_eq_norm,show (x-r • e)-x=-(r • e) by abel,norm_neg,hvec]
    have hp : |D (x+r • e,T)|≤B := hb _ hplus
    have hm : |D (x-r • e,T)|≤B := hb _ hminus
    have hId : D (x+r • e,T)+D (x-r • e,T)-2*D (x,T)=r^2*a e e := by
      have h1 := perturb_extraction_space_identity c1 q1 r T b1 A1 x e
      have h2 := perturb_extraction_space_identity c2 q2 r T b2 A2 x e
      dsimp only [D,a]
      simp only [sub_apply]
      linear_combination h1-h2
    have hfour : |r^2*a e e|≤4*B := by
      rw [← hId]
      have hp' := abs_le.mp hp
      have hm' := abs_le.mp hm
      have hc' := abs_le.mp hdc
      exact abs_le.mpr ⟨by linarith only [hp'.1,hm'.1,hc'.2],by linarith only [hp'.2,hm'.2,hc'.1]⟩
    apply (le_div_iff₀ hrr).mpr
    rw [abs_mul,abs_of_pos hrr] at hfour
    nlinarith only [hfour]
  have hSym : ∀ v w, a v w=a w v := by
    intro v w
    dsimp only [a]
    simp only [sub_apply]
    rw [perturbBilinear_symmetric A1 v w,perturbBilinear_symmetric A2 v w]
  have hnorm : ‖a‖≤4*B/r^2 := perturb_extraction_symmetric_opNorm a hK hSym
    (perturb_extraction_diagonal_bound a hK hDiag)
  refine ⟨hq,?_⟩
  simpa only [perturb_polynomial_spatialDD] using hnorm

end Yau.LeafProofs.L05Aux
