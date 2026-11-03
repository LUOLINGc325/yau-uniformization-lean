import Yau.LeafProofs.L18

/-! Entrywise real differentiation of actual complex matrix products and inverses. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C05Aux
open Filter
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem fderiv_complex_matrix_mul_entry {A B : E → Matrix ι ι ℂ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z) (v : E) (i j : ι) :
    fderiv ℝ (fun w => (A w * B w) i j) z v =
      ∑ k, (fderiv ℝ (fun w => A w i k) z v * B z k j +
        A z i k * fderiv ℝ (fun w => B w k j) z v) := by
  simp only [Matrix.mul_apply]
  have hp (k : ι) : DifferentiableAt ℝ (fun w => A w i k * B w k j) z :=
    (hA i k).mul (hB k j)
  rw [fderiv_fun_sum (fun k _ => hp k)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (hA i k) (hB k j)]
  simp <;> ring

theorem fderiv_complex_matrix_inv_entry {A : E → Matrix ι ι ℂ} {O : Set E}
    (hO : IsOpen O) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun w => A w i j) O)
    (hdet : ∀ w ∈ O, (A w).det ≠ 0) {z : E} (hz : z ∈ O) (v : E) (i j : ι) :
    fderiv ℝ (fun w => (A w)⁻¹ i j) z v =
      -(((A z)⁻¹ * (Matrix.of fun p q => fderiv ℝ (fun w => A w p q) z v) * (A z)⁻¹) i j) := by
  let DA : Matrix ι ι ℂ := Matrix.of fun p q => fderiv ℝ (fun w => A w p q) z v
  let DI : Matrix ι ι ℂ := Matrix.of fun p q => fderiv ℝ (fun w => (A w)⁻¹ p q) z v
  have hAd (p q : ι) : DifferentiableAt ℝ (fun w => A w p q) z :=
    ((hA p q).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hId (p q : ι) : DifferentiableAt ℝ (fun w => (A w)⁻¹ p q) z :=
    ((Yau.LeafProofs.L18Aux.contDiffOn_matrix_inv hA hdet p q).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdprod (p q : ι) : fderiv ℝ (fun w => ((A w)⁻¹ * A w) p q) z v = 0 := by
    have he : (fun w => ((A w)⁻¹ * A w) p q) =ᶠ[𝓝 z]
        (fun _ : E => (1 : Matrix ι ι ℂ) p q) := by
      filter_upwards [hO.mem_nhds hz] with w hw
      exact congrArg (fun M : Matrix ι ι ℂ => M p q)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet w hw)))
    rw [he.fderiv_eq]
    simp
  have hm : DI * A z + (A z)⁻¹ * DA = 0 := by
    ext p q
    have hpq := hdprod p q
    rw [fderiv_complex_matrix_mul_entry hId hAd] at hpq
    simpa only [DA, DI, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.zero_apply, Finset.sum_add_distrib] using hpq
  have hm' := congrArg (fun M : Matrix ι ι ℂ => M * (A z)⁻¹) hm
  have hDI : DI = -((A z)⁻¹ * DA * (A z)⁻¹) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet z hz)),
      Matrix.mul_one, Matrix.zero_mul] using hm'
  simpa only [DI, DA, Matrix.of_apply, Matrix.neg_apply] using
    congrArg (fun M : Matrix ι ι ℂ => M i j) hDI

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_complex_trace_mul {A B : ℝ → Matrix ι ι ℂ}
    {A' B' : Matrix ι ι ℂ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) :
    HasDerivAt (fun s => (A s * B s).trace) (A' * B t + A t * B').trace t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hA i j).mul (hB j i)))
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.add_apply,
    Finset.sum_add_distrib, Pi.mul_apply] using hd

end Yau.Proofs.C05Aux
