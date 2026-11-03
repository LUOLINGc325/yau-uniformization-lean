import Yau.LeafProofs.L05TraceEllipticity

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem inverse_norm_sub_le {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A B : Sym n}
    (hA : A ∈ slopeSet n ell L) (hB : B ∈ slopeSet n ell L) :
    ‖(A : Mat n)⁻¹-(B : Mat n)⁻¹‖ ≤ ((2*n)*ell⁻¹)^2*‖A-B‖ := by
  have hAn := symInverse_norm_le hell hL hA
  have hBn := symInverse_norm_le hell hL hB
  have hM : 0 ≤ (2*n:ℝ)*ell⁻¹ := mul_nonneg (by positivity) (inv_nonneg.mpr hell.le)
  rw [inverse_sub_identity (slopeSet_subset_logDetDomain hell hA) (slopeSet_subset_logDetDomain hell hB)]
  calc
    _ ≤ (‖(A : Mat n)⁻¹‖*‖(B : Mat n)-(A : Mat n)‖)*‖(B : Mat n)⁻¹‖ :=
      (Matrix.frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
    _ ≤ (((2*n)*ell⁻¹)*‖(B : Mat n)-(A : Mat n)‖)*((2*n)*ell⁻¹) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hAn (norm_nonneg _)) hBn
        (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev]; change _=((2*n:ℝ)*ell⁻¹)^2*‖(A : Mat n)-(B : Mat n)‖; ring

def logDetDerivativeConstant (n : ℕ) (ell : ℝ) : ℝ :=
  (1/2:ℝ)*Real.sqrt (Fintype.card (RIdx n))*((2*n)*ell⁻¹)^2

theorem logDetDerivativeConstant_nonneg (n : ℕ) (ell : ℝ) :
    0 ≤ logDetDerivativeConstant n ell := by unfold logDetDerivativeConstant; positivity

theorem logDetReal_fderiv_sub_le {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {A B : Sym n}
    (hA : A ∈ slopeSet n ell L) (hB : B ∈ slopeSet n ell L) (V : Sym n) :
    |fderiv ℝ (@logDetReal n) A V-fderiv ℝ (@logDetReal n) B V| ≤
      logDetDerivativeConstant n ell*‖A-B‖*‖V‖ := by
  rw [logDetReal_fderiv (slopeSet_subset_logDetDomain hell hA),
    logDetReal_fderiv (slopeSet_subset_logDetDomain hell hB),← mul_sub,abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  rw [← Matrix.trace_sub,← Matrix.sub_mul]
  have ht := abs_trace_mul_le ((A : Mat n)⁻¹-(B : Mat n)⁻¹) (V : Mat n)
  have hn := inverse_norm_sub_le hell hL hA hB
  calc
    _ ≤ (1/2:ℝ)*(Real.sqrt (Fintype.card (RIdx n))*‖(A : Mat n)⁻¹-(B : Mat n)⁻¹‖*‖(V : Mat n)‖) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ ≤ (1/2:ℝ)*(Real.sqrt (Fintype.card (RIdx n))*(((2*n)*ell⁻¹)^2*‖A-B‖)*‖(V : Mat n)‖) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)) (norm_nonneg _)) (by norm_num)
    _ = _ := by unfold logDetDerivativeConstant; change _=_*_*‖(V : Mat n)‖; ring

theorem linearModulus {c : ℝ} (hc : 0 ≤ c) : Modulus (fun r => c*r) := by
  refine ⟨by simp,fun r hr => mul_nonneg hc hr,?_,?_⟩
  · intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left hxy hc
  · have hh : Tendsto (fun r : ℝ => c*r) (𝓝[≥] (0:ℝ)) (𝓝 (c*0)) :=
      ((continuous_const.mul continuous_id : Continuous (fun r : ℝ => c*r)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simpa only [mul_zero] using hh

theorem logDetReal_chuDerivativeModulus {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {E : Set (Sym n)} (hE : E ⊆ slopeSet n ell L) :
    ChuDerivativeModulus E (fun A _ => logDetReal A) (fun r => logDetDerivativeConstant n ell*r) := by
  intro A hA B hB p hp q hq V hV
  have hh := logDetReal_fderiv_sub_le hell hL (hE hA) (hE hB) V
  have hc := logDetDerivativeConstant_nonneg n ell
  have hD : 0 ≤ parabolicDistance p q := add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hnorm : 0 ≤ logDetDerivativeConstant n ell*‖A-B‖ := mul_nonneg hc (norm_nonneg _)
  change |fderiv ℝ (@logDetReal n) A V-fderiv ℝ (@logDetReal n) B V| ≤ _
  exact hh.trans ((mul_le_mul_of_nonneg_left hV hnorm).trans (by nlinarith only [mul_nonneg hc hD]))

end Yau.LeafProofs.L05Aux
