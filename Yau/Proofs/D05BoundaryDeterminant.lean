import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix

/-! The complex determinant differential at the identity, for genuine real
within derivatives. No continuation through a boundary point is used. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι]

private def complexDetAlt : (ι → ℂ) [⋀^ι]→L[ℝ] ℂ :=
  ({ Matrix.detRowAlternating with cont := continuous_id.matrix_det } :
    (ι → ℂ) [⋀^ι]→L[ℂ] ℂ).restrictScalars ℝ

theorem complex_det_differentiableWithinAt {A : E → Matrix ι ι ℂ} {S : Set E} {z : E}
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun w => A w i j) S z) :
    DifferentiableWithinAt ℝ (fun w => (A w).det) S z := by
  have hrow (i : ι) : DifferentiableWithinAt ℝ (fun w => A w i) S z :=
    differentiableWithinAt_pi.mpr (hA i)
  exact (differentiableWithinAt_const (c :=
    (complexDetAlt : (ι → ℂ) [⋀^ι]→L[ℝ] ℂ))).continuousAlternatingMap_apply hrow

theorem fderivWithin_complex_det_sum_updateRow {A : E → Matrix ι ι ℂ}
    {S : Set E} {z : E} (hS : UniqueDiffWithinAt ℝ S z)
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun w => A w i j) S z) (v : E) :
    fderivWithin ℝ (fun w => (A w).det) S z v =
      ∑ i, ((A z).updateRow i (fderivWithin ℝ (fun w => A w i) S z v)).det := by
  let d : (ι → ℂ) [⋀^ι]→L[ℝ] ℂ := complexDetAlt
  have hrow (i : ι) : DifferentiableWithinAt ℝ (fun w => A w i) S z :=
    differentiableWithinAt_pi.mpr (hA i)
  have h := fderivWithin_continuousAlternatingMap_apply_apply
    (f := fun _ : E => d) (g := fun i w => A w i)
    (differentiableWithinAt_const (c := d)) hrow hS v
  have hfun : (fun w : E => d (fun i => A w i)) = fun w => (A w).det := rfl
  have hupdate (i : ι) :
      d (Function.update (fun j => A z j) i (fderivWithin ℝ (fun w => A w i) S z v)) =
        ((A z).updateRow i (fderivWithin ℝ (fun w => A w i) S z v)).det := rfl
  simp only [fderivWithin_fun_const, Pi.zero_apply, zero_apply,
    ContinuousAlternatingMap.coe_zero, zero_add] at h
  rw [hfun] at h
  simpa only [hupdate] using h

theorem det_one_updateRow (i : ι) (row : ι → ℂ) :
    ((1 : Matrix ι ι ℂ).updateRow i row).det = row i := by
  have hr : (∑ k, row k • (1 : Matrix ι ι ℂ) k) = row := by
    ext j
    simp [Matrix.one_apply]
  conv_lhs => rw [← hr]
  rw [Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

theorem fderivWithin_complex_trace {A : E → Matrix ι ι ℂ} {S : Set E} {z : E}
    (hS : UniqueDiffWithinAt ℝ S z)
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun w => A w i j) S z) (v : E) :
    fderivWithin ℝ (fun w => Matrix.trace (A w)) S z v =
      ∑ i, fderivWithin ℝ (fun w => A w i i) S z v := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [fderivWithin_fun_sum hS (fun i _ => hA i i)]
  simp

theorem fderivWithin_complex_det_eq_trace_at_one {A : E → Matrix ι ι ℂ}
    {S : Set E} {z : E} (hS : UniqueDiffWithinAt ℝ S z)
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun w => A w i j) S z)
    (hAz : A z = 1) (v : E) :
    fderivWithin ℝ (fun w => (A w).det) S z v =
      fderivWithin ℝ (fun w => Matrix.trace (A w)) S z v := by
  rw [fderivWithin_complex_det_sum_updateRow hS hA v,
    fderivWithin_complex_trace hS hA v]
  simp_rw [hAz, det_one_updateRow]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderivWithin_pi (hA i) hS]
  rfl

theorem fderivWithin_complex_re {f : E → ℂ} {S : Set E} {z : E}
    (hS : UniqueDiffWithinAt ℝ S z) (hf : DifferentiableWithinAt ℝ f S z) (v : E) :
    fderivWithin ℝ (fun w => (f w).re) S z v =
      (fderivWithin ℝ f S z v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt z
    hf.hasFDerivWithinAt).fderivWithin hS
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) h

theorem gram_logdet_boundary_normal_eq_trace {A : E → Matrix ι ι ℂ}
    {S : Set E} {z : E} (hS : UniqueDiffWithinAt ℝ S z)
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun w => A w i j) S z)
    (hAz : A z = 1) (v : E) :
    fderivWithin ℝ (fun w => Real.log (A w).det.re) S z v =
      fderivWithin ℝ (fun w => (Matrix.trace (A w)).re) S z v := by
  have hd := complex_det_differentiableWithinAt hA
  have hRe : DifferentiableWithinAt ℝ (fun w => (A w).det.re) S z :=
    Complex.reCLM.differentiableAt.comp_differentiableWithinAt z hd
  have htrace : DifferentiableWithinAt ℝ (fun w => Matrix.trace (A w)) S z := by
    simpa only [Matrix.trace, Matrix.diag_apply] using
      DifferentiableWithinAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hA i i)
  have hnonzero : (A z).det.re ≠ 0 := by rw [hAz]; simp
  rw [fderivWithin.log hRe hnonzero hS]
  simp only [hAz, Matrix.det_one, Complex.one_re, inv_one, one_smul]
  rw [fderivWithin_complex_re hS hd, fderivWithin_complex_re hS htrace,
    fderivWithin_complex_det_eq_trace_at_one hS hA hAz]

end Yau.Blueprint.D05Proof
