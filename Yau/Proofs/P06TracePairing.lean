import Yau.Proofs.P06CutoffOrder

noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem formHermitianMatrix_sub (A B : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (A - B) x = formHermitianMatrix A x - formHermitianMatrix B x := by
  ext a b
  apply Complex.ext <;>
    simp [formHermitianMatrix, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem formHermitianMatrix_add (A B : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (A + B) x = formHermitianMatrix A x + formHermitianMatrix B x := by
  ext a b
  apply Complex.ext <;>
    simp [formHermitianMatrix, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem realOneOne_sub (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) :
    RealOneOne (A - B) := by
  intro x u v
  change A x ![Complex.I • u, Complex.I • v] - B x ![Complex.I • u, Complex.I • v] =
    A x ![u, v] - B x ![u, v]
  rw [hA x u v, hB x u v]

theorem realOneOne_add (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) :
    RealOneOne (A + B) := by
  intro x u v
  change A x ![Complex.I • u, Complex.I • v] + B x ![Complex.I • u, Complex.I • v] =
    A x ![u, v] + B x ![u, v]
  rw [hA x u v, hB x u v]

theorem omegaForm_nonnegative (g : HermitianField M) : FormLE 0 (G04Aux.omegaForm g) := by
  intro x
  rw [G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g),
    formHermitianMatrix_zero, sub_zero]
  exact (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef

/-- Pairing with the original Kähler form gives exactly the original
complex metric trace, with no extra factor of two. -/
theorem formInner_omegaForm (g : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) (x : M.Carrier) :
    formInner g A (G04Aux.omegaForm g) x = formTrace g A x := by
  rw [G04Aux.formInner_oneOne g A _ hA (G04Aux.omegaForm_oneOne g) x,
    G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g)]
  have hH := Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have hG : (gMat g x).PosDef := hH
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG.isUnit.map Matrix.detMonoidHom), Matrix.mul_one]
  rfl

theorem formTrace_nonnegative (g : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) (hp : FormLE 0 A) (x : M.Carrier) : 0 ≤ formTrace g A x := by
  rw [← formInner_omegaForm g A hA x]
  exact formInner_nonnegative_oneOne g A _ hA (G04Aux.omegaForm_oneOne g) hp
    (omegaForm_nonnegative g) x

/-- Positive test forms pair with a signed Cg-bounded form by at most
C times their genuine trace. No closedness assumption is used. -/
theorem formInner_le_trace_bound (g : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hp : FormLE 0 A) (hB : RealOneOne B)
    {C : ℝ} (hbound : FormOrderBound g C B) (x : M.Carrier) :
    formInner g A B x ≤ C * formTrace g A x := by
  let D : RealForm M 2 := C • G04Aux.omegaForm g - B
  have hD : RealOneOne D := realOneOne_sub _ B
    (realOneOne_multiply (fun _ => C) _ (G04Aux.omegaForm_oneOne g)) hB
  have hDp : FormLE 0 D := by
    intro y
    simpa only [D, formHermitianMatrix_zero, sub_zero, formHermitianMatrix_sub,
      G04Aux.formHermitianMatrix_real_smul,
      G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g)] using
        (hbound y).2
  have h := formInner_nonnegative_oneOne g A D hA hD hp hDp x
  have heq : formInner g A D x = C * formTrace g A x - formInner g A B x := by
    rw [show D = C • G04Aux.omegaForm g - B from rfl, formInner_sub_right,
      formInner_smul_right]
    change C * formInner g A (G04Aux.omegaForm g) x - formInner g A B x = _
    rw [formInner_omegaForm g A hA x]
  rw [heq] at h
  linarith

theorem formInner_abs_le_trace_bound (g : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hp : FormLE 0 A) (hB : RealOneOne B)
    {C : ℝ} (hbound : FormOrderBound g C B) (x : M.Carrier) :
    |formInner g A B x| ≤ C * formTrace g A x := by
  let D : RealForm M 2 := C • G04Aux.omegaForm g + B
  have hD : RealOneOne D := realOneOne_add _ B
    (realOneOne_multiply (fun _ => C) _ (G04Aux.omegaForm_oneOne g)) hB
  have hDp : FormLE 0 D := by
    intro y
    rw [formHermitianMatrix_zero, sub_zero]
    change (formHermitianMatrix (C • G04Aux.omegaForm g + B) y).PosSemidef
    rw [formHermitianMatrix_add, G04Aux.formHermitianMatrix_real_smul,
      G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g)]
    convert (hbound y).1 using 1
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h := formInner_nonnegative_oneOne g A D hA hD hp hDp x
  have heq : formInner g A D x = C * formTrace g A x + formInner g A B x := by
    rw [show D = C • G04Aux.omegaForm g + B from rfl, formInner_add_right,
      formInner_smul_right]
    change C * formInner g A (G04Aux.omegaForm g) x + formInner g A B x = _
    rw [formInner_omegaForm g A hA x]
  rw [heq] at h
  exact abs_le.mpr ⟨by linarith, formInner_le_trace_bound g A B hA hp hB hbound x⟩

theorem formTrace_mono (g : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (hAB : FormLE A B) (x : M.Carrier) :
    formTrace g A x ≤ formTrace g B x := by
  have hD := realOneOne_sub B A hB hA
  have hp : FormLE 0 (B - A) := by
    intro y
    simpa only [formHermitianMatrix_zero, sub_zero, formHermitianMatrix_sub] using hAB y
  have h := formTrace_nonnegative g (B - A) hD hp x
  rw [← formInner_omegaForm g (B - A) hD x, formInner_sub_left] at h
  change 0 ≤ formInner g B (G04Aux.omegaForm g) x - formInner g A (G04Aux.omegaForm g) x at h
  rw [formInner_omegaForm g B hB x, formInner_omegaForm g A hA x] at h
  linarith

/-- Compact positive form tests have a genuine L¹ trace bound against
the paper's signed bounded data, in the original Riemannian measure. -/
theorem integral_abs_formInner_le_trace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11A : RealOneOne A) (hp : FormLE 0 A) (hB : SmoothRealForm B) (h11B : RealOneOne B)
    {C : ℝ} (hbound : FormOrderBound g.form C B) :
    (∫ x, |formInner g.form A B x| ∂μ) ≤ C * ∫ x, formTrace g.form A x ∂μ := by
  have hpair := smooth_compact_formInner_integrable g μ hμ A B hA hB hcA
  have htrace := smooth_compact_formInner_integrable g μ hμ A (G04Aux.omegaForm g.form) hA
    (G04Aux.omegaForm_smooth g.form (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)) hcA
  have heq : formInner g.form A (G04Aux.omegaForm g.form) = formTrace g.form A :=
    funext (formInner_omegaForm g.form A h11A)
  rw [heq] at htrace
  calc
    _ ≤ ∫ x, C * formTrace g.form A x ∂μ := integral_mono hpair.abs (htrace.const_mul C)
      (fun x => formInner_abs_le_trace_bound g.form A B h11A hp h11B hbound x)
    _ = _ := integral_const_mul _ _

end Yau.NodeProofs.P06Aux
