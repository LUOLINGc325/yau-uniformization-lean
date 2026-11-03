import Yau.LeafProofs.L05PerturbationPolynomials

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- Normalizing only nonzero vectors needs no positive-dimensional instance. -/
theorem perturb_extraction_diagonal_bound {n : ℕ}
    (a : Space n →L[ℝ] Space n →L[ℝ] ℝ) {K : ℝ} (_hK : 0≤K)
    (hUnit : ∀ e : Space n, ‖e‖=1 → |a e e|≤K) :
    ∀ v : Space n, |a v v|≤K*‖v‖^2 := by
  intro v
  by_cases hv : v=0
  · simp only [hv,map_zero,abs_zero,norm_zero,pow_two,mul_zero,le_refl]
  have hnorm : 0<‖v‖ := norm_pos_iff.mpr hv
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖=1 := by
    dsimp only [e]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnorm),inv_mul_cancel₀ hnorm.ne']
  have hscale : ‖v‖ • e=v := by
    dsimp only [e]
    rw [smul_smul,mul_inv_cancel₀ hnorm.ne',one_smul]
  have hhom : a v v=‖v‖^2*a e e := by
    calc
      _ = a (‖v‖ • e) (‖v‖ • e) := by rw [hscale]
      _ = _ := by simp only [map_smul,smul_apply,smul_eq_mul]; ring
  rw [hhom,abs_mul,abs_of_nonneg (sq_nonneg ‖v‖)]
  calc
    _ ≤ ‖v‖^2*K := mul_le_mul_of_nonneg_left (hUnit e he) (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- Symmetric polarization and the real parallelogram identity give the exact
bilinear operator norm, including in the zero-dimensional space. -/
theorem perturb_extraction_symmetric_opNorm {n : ℕ}
    (a : Space n →L[ℝ] Space n →L[ℝ] ℝ) {K : ℝ} (hK : 0≤K)
    (hSym : ∀ v w, a v w=a w v)
    (hDiag : ∀ v, |a v v|≤K*‖v‖^2) : ‖a‖≤K := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro w hw
  rw [Real.norm_eq_abs]
  have hPlus := hDiag (v+w)
  have hMinus := hDiag (v-w)
  have hPolar : 4*a v w=a (v+w) (v+w)-a (v-w) (v-w) := by
    simp only [map_add,map_sub,add_apply,sub_apply]
    rw [hSym w v]
    ring
  have hPar : ‖v+w‖^2+‖v-w‖^2=4 := by
    have h := parallelogram_law_with_norm ℝ v w
    rw [hv,hw] at h
    norm_num at h
    exact h
  have hBound : |4*a v w|≤4*K := by
    rw [hPolar]
    calc
      _ ≤ |a (v+w) (v+w)|+|a (v-w) (v-w)| := abs_sub _ _
      _ ≤ K*‖v+w‖^2+K*‖v-w‖^2 := add_le_add hPlus hMinus
      _ = 4*K := by rw [← mul_add,hPar]; ring
  rw [abs_mul,show |(4 : ℝ)|=4 by norm_num] at hBound
  linarith only [hBound]

end Yau.LeafProofs.L05Aux
