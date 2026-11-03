import Yau.Proofs.V03LeviCalculus
import Yau.Proofs.V03CauchyBinet

/-! The Levi derivative of the logarithm of a positive sum of squared
holomorphic functions. All derivatives are the original nested operators. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]

def holomorphicSqSum (f : ι → E → ℂ) (z : E) : ℝ := ∑ i, ‖f i z‖ ^ 2

theorem holomorphicSqSum_coe (f : ι → E → ℂ) (z : E) :
    (holomorphicSqSum f z : ℂ) = ∑ i, star (f i z) * f i z := by
  simp only [holomorphicSqSum, Complex.ofReal_sum, star_mul_self_eq_norm_sq]

theorem holomorphicSqSum_contDiffAt {f : ι → E → ℂ} {z : E} {m : ℕ∞ω}
    (hf : ∀ i, ContDiffAt ℂ m (f i) z) :
    ContDiffAt ℝ m (holomorphicSqSum f) z :=
  ContDiffAt.sum fun i _ => ((hf i).restrict_scalars ℝ).norm_sq (𝕜 := ℂ)

theorem holomorphicSqSum_wirtBar {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, DifferentiableAt ℂ (f i) z) (v : E) :
    wirtBar (fun y => (holomorphicSqSum f y : ℂ)) z v =
      ∑ i, star (fderiv ℂ (f i) z v) * f i z := by
  simp_rw [holomorphicSqSum_coe]
  rw [wirtBar_sum Finset.univ (fun i y => star (f i y) * f i y) z v (fun i _ =>
    ((hf i).restrictScalars ℝ).star.mul ((hf i).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  rw [wirtBar_mul ((hf i).restrictScalars ℝ).star ((hf i).restrictScalars ℝ),
    wirtBar_conj, wirt_holomorphic (hf i), wirtBar_holomorphic (hf i)]
  ring

theorem holomorphicSqSum_wirt {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, DifferentiableAt ℂ (f i) z) (v : E) :
    wirt (fun y => (holomorphicSqSum f y : ℂ)) z v =
      ∑ i, star (f i z) * fderiv ℂ (f i) z v := by
  simp_rw [holomorphicSqSum_coe]
  rw [wirt_sum Finset.univ (fun i y => star (f i y) * f i y) z v (fun i _ =>
    ((hf i).restrictScalars ℝ).star.mul ((hf i).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  rw [wirt_mul ((hf i).restrictScalars ℝ).star ((hf i).restrictScalars ℝ),
    wirt_conj, wirtBar_holomorphic (hf i), star_zero, wirt_holomorphic (hf i)]
  ring

theorem holomorphicSqSum_pair_wirt {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, ContDiffAt ℂ 2 (f i) z) (v : E) :
    wirt (fun y => ∑ i, star (fderiv ℂ (f i) y v) * f i y) z v =
      ∑ i, star (fderiv ℂ (f i) z v) * fderiv ℂ (f i) z v := by
  have hd (i : ι) : DifferentiableAt ℂ (fun y => fderiv ℂ (f i) y v) z :=
    ((hf i).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero |>.clm_apply
      (differentiableAt_const v)
  rw [wirt_sum Finset.univ (fun i y => star (fderiv ℂ (f i) y v) * f i y) z v (fun i _ =>
    ((hd i).restrictScalars ℝ).star.mul
      (((hf i).differentiableAt (by norm_num)).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  rw [wirt_mul ((hd i).restrictScalars ℝ).star
      (((hf i).differentiableAt (by norm_num)).restrictScalars ℝ),
    wirt_conj, wirtBar_holomorphic (hd i), star_zero,
    wirt_holomorphic ((hf i).differentiableAt (by norm_num))]
  ring

theorem log_holomorphicSqSum_levi {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, ContDiffAt ℂ 2 (f i) z) (hs : holomorphicSqSum f z ≠ 0) (v : E) :
    wirt (fun y => wirtBar (fun y' => (Real.log (holomorphicSqSum f y') : ℂ)) y v) z v =
      (holomorphicSqSum f z : ℂ)⁻¹ *
        (∑ i, star (fderiv ℂ (f i) z v) * fderiv ℂ (f i) z v) -
      (holomorphicSqSum f z : ℂ)⁻¹ ^ 2 *
        (∑ i, star (f i z) * fderiv ℂ (f i) z v) *
        (∑ i, star (fderiv ℂ (f i) z v) * f i z) := by
  have hS := holomorphicSqSum_contDiffAt hf
  have hd (i : ι) : DifferentiableAt ℂ (f i) z := (hf i).differentiableAt (by norm_num)
  have hD (i : ι) : DifferentiableAt ℂ (fun y => fderiv ℂ (f i) y v) z :=
    ((hf i).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero |>.clm_apply
      (differentiableAt_const v)
  have hSC : DifferentiableAt ℝ (fun y => (holomorphicSqSum f y : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hS.differentiableAt (by norm_num))
  have hsC : (holomorphicSqSum f z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hB : DifferentiableAt ℝ
      (fun y => ∑ i, star (fderiv ℂ (f i) y v) * f i y) z :=
    DifferentiableAt.fun_sum fun i _ => ((hD i).restrictScalars ℝ).star.mul
      ((hd i).restrictScalars ℝ)
  have hlocal : ∀ᶠ y in 𝓝 z, ∀ i, ContDiffAt ℂ 2 (f i) y :=
    eventually_all.mpr fun i => (hf i).eventually (by norm_num)
  have heq : (fun y => wirtBar (fun y' => (Real.log (holomorphicSqSum f y') : ℂ)) y v)
      =ᶠ[𝓝 z] (fun y => (holomorphicSqSum f y : ℂ)⁻¹ *
        ∑ i, star (fderiv ℂ (f i) y v) * f i y) := by
    filter_upwards [hlocal, hS.continuousAt.eventually_ne hs] with y hy hsy
    rw [wirtBar_log_real ((holomorphicSqSum_contDiffAt hy).differentiableAt
      (by norm_num)) hsy, holomorphicSqSum_wirtBar
        (fun i => (hy i).differentiableAt (by norm_num))]
  have hw : wirt (fun y => wirtBar
      (fun y' => (Real.log (holomorphicSqSum f y') : ℂ)) y v) z v =
      wirt (fun y => (holomorphicSqSum f y : ℂ)⁻¹ *
        ∑ i, star (fderiv ℂ (f i) y v) * f i y) z v := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_mul (f := fun y => (holomorphicSqSum f y : ℂ)⁻¹) (hSC.fun_inv hsC) hB,
    wirt_inv hSC hsC, holomorphicSqSum_wirt hd, holomorphicSqSum_pair_wirt hf]
  ring

end Yau.Blueprint.V03Proof
