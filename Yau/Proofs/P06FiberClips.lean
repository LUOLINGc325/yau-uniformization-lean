import Yau.Proofs.P06RelativeMatrixPairing
import Yau.Proofs.P06TracePairing

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Pointwise spectral clipping reconstructed as an actual alternating
real two-form on the original tangent fibers. -/
def intervalForm (g : HermitianField M) (C : ℝ) (A : RealForm M 2) : RealForm M 2 :=
  G04Aux.iotaRealForm (fun x => relativeIntervalClip C (gMat g x) (formHermitianMatrix A x))
    (fun _ => relativeIntervalClip_hermitian C _ _)

def positiveForm (g : HermitianField M) (A : RealForm M 2) : RealForm M 2 :=
  G04Aux.iotaRealForm (fun x => relativePositivePart (gMat g x) (formHermitianMatrix A x))
    (fun _ => (relativePositivePart_posSemidef _ _).1)

theorem intervalForm_oneOne (g : HermitianField M) (C : ℝ) (A : RealForm M 2) :
    RealOneOne (intervalForm g C A) := G04Aux.iotaRealForm_oneOne _ _

theorem positiveForm_oneOne (g : HermitianField M) (A : RealForm M 2) :
    RealOneOne (positiveForm g A) := G04Aux.iotaRealForm_oneOne _ _

theorem intervalForm_matrix (g : HermitianField M) (C : ℝ) (A : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (intervalForm g C A) x =
      relativeIntervalClip C (gMat g x) (formHermitianMatrix A x) :=
  G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.iotaRealForm_represents _ _) x

theorem positiveForm_matrix (g : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (positiveForm g A) x =
      relativePositivePart (gMat g x) (formHermitianMatrix A x) :=
  G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.iotaRealForm_represents _ _) x

theorem positiveForm_nonnegative (g : HermitianField M) (A : RealForm M 2) :
    FormLE 0 (positiveForm g A) := by
  intro x
  rw [positiveForm_matrix, formHermitianMatrix_zero, sub_zero]
  exact relativePositivePart_posSemidef _ _

theorem intervalForm_orderBound (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (hA : RealOneOne A) : FormOrderBound g C (intervalForm g C A) := by
  intro x
  rw [intervalForm_matrix]
  have hb := relativeIntervalClip_bounds hC (gMat g x) (formHermitianMatrix A x)
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x)
  constructor
  · convert hb.2 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring
  · convert hb.1 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring

theorem oneOne_eq_at_of_matrix_eq (g : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier)
    (he : formHermitianMatrix A x = formHermitianMatrix B x) : A x = B x := by
  have hz : formNormSq g (A - B) x = 0 := by
    rw [formNormSq_eq_pointFormHS g _ (realOneOne_sub A B hA hB),
      pointFormHS, formHermitianMatrix_sub, he, sub_self, relativeMatrixHS,
      metricWhiten_zero]
    change ‖(0 : EuclideanSpace ℂ (Fin n × Fin n))‖ ^ 2 = 0
    simp
  have hzero := (formNormSq_eq_zero_iff g (A - B) x).mp hz
  exact sub_eq_zero.mp hzero

theorem intervalForm_eq_self (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (hA : RealOneOne A) (hb : FormOrderBound g C A) :
    intervalForm g C A = A := by
  funext x
  apply oneOne_eq_at_of_matrix_eq g _ A (intervalForm_oneOne g C A) hA x
  rw [intervalForm_matrix]
  apply relativeIntervalClip_eq_self hC _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x)
  · convert (hb x).2 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring
  · convert (hb x).1 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring

theorem positiveForm_eq_self (g : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) (hp : FormLE 0 A) : positiveForm g A = A := by
  funext x
  apply oneOne_eq_at_of_matrix_eq g _ A (positiveForm_oneOne g A) hA x
  rw [positiveForm_matrix]
  apply relativePositivePart_eq_self _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
  simpa only [formHermitianMatrix_zero, sub_zero] using hp x

theorem intervalForm_nonexpansive_sq (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier) :
    formNormSq g (intervalForm g C A - intervalForm g C B) x ≤ formNormSq g (A - B) x := by
  rw [formNormSq_eq_pointFormHS g _
    (realOneOne_sub _ _ (intervalForm_oneOne g C A) (intervalForm_oneOne g C B)),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub A B hA hB)]
  simp only [pointFormHS, formHermitianMatrix_sub, intervalForm_matrix]
  exact pow_le_pow_left₀ (norm_nonneg _) (relativeIntervalClip_nonexpansive hC _ _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x) ((G04Aux.representsSelf B hB).2 x)) 2

theorem positiveForm_nonexpansive_sq (g : HermitianField M)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier) :
    formNormSq g (positiveForm g A - positiveForm g B) x ≤ formNormSq g (A - B) x := by
  rw [formNormSq_eq_pointFormHS g _
    (realOneOne_sub _ _ (positiveForm_oneOne g A) (positiveForm_oneOne g B)),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub A B hA hB)]
  simp only [pointFormHS, formHermitianMatrix_sub, positiveForm_matrix]
  exact pow_le_pow_left₀ (norm_nonneg _) (relativePositivePart_nonexpansive _ _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x) ((G04Aux.representsSelf B hB).2 x)) 2

theorem intervalForm_zero_at (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (x : M.Carrier) (hAx : A x = 0) : intervalForm g C A x = 0 := by
  apply oneOne_eq_at_of_matrix_eq g _ 0 (intervalForm_oneOne g C A)
    (by intro y u v; rfl) x
  rw [intervalForm_matrix, formHermitianMatrix_zero]
  have hm : formHermitianMatrix A x = 0 := by
    ext i j
    simp [formHermitianMatrix, hAx]
  rw [hm, relativeIntervalClip_zero hC]

theorem positiveForm_zero_at (g : HermitianField M)
    (A : RealForm M 2) (x : M.Carrier) (hAx : A x = 0) : positiveForm g A x = 0 := by
  apply oneOne_eq_at_of_matrix_eq g _ 0 (positiveForm_oneOne g A)
    (by intro y u v; rfl) x
  rw [positiveForm_matrix, formHermitianMatrix_zero]
  have hm : formHermitianMatrix A x = 0 := by
    ext i j
    simp [formHermitianMatrix, hAx]
  rw [hm, relativePositivePart_zero]

theorem intervalForm_support (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) : {x | intervalForm g C A x ≠ 0} ⊆ {x | A x ≠ 0} := by
  intro x hx ha
  exact hx (intervalForm_zero_at g hC A x ha)

theorem positiveForm_support (g : HermitianField M) (A : RealForm M 2) :
    {x | positiveForm g A x ≠ 0} ⊆ {x | A x ≠ 0} := by
  intro x hx ha
  exact hx (positiveForm_zero_at g A x ha)

theorem intervalForm_compact (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A : RealForm M 2) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (intervalForm g C A) :=
  hcA.of_isClosed_subset isClosed_closure (closure_mono (intervalForm_support g hC A))

theorem positiveForm_compact (g : HermitianField M)
    (A : RealForm M 2) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (positiveForm g A) :=
  hcA.of_isClosed_subset isClosed_closure (closure_mono (positiveForm_support g A))

/-- The true original form norm satisfies the sharp interval projection
inequality, retaining both the metric and the same signed bound C. -/
theorem intervalForm_distance_sq (g : HermitianField M) {C : ℝ} (hC : 0 ≤ C)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B)
    (hb : FormOrderBound g C B) (x : M.Carrier) :
    formNormSq g (intervalForm g C A - B) x ≤ formNormSq g (A - B) x -
      formNormSq g (A - intervalForm g C A) x := by
  rw [formNormSq_eq_pointFormHS g _ (realOneOne_sub _ _ (intervalForm_oneOne g C A) hB),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub A B hA hB),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub _ _ hA (intervalForm_oneOne g C A))]
  simp only [pointFormHS, formHermitianMatrix_sub, intervalForm_matrix]
  apply relativeIntervalClip_distance_sq hC _ _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x)
  · convert (hb x).2 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring
  · convert (hb x).1 using 1 <;> ext i j <;> simp [gMat, Complex.real_smul] <;> ring

theorem positiveForm_distance_sq (g : HermitianField M)
    (A B : RealForm M 2) (hA : RealOneOne A) (hB : RealOneOne B)
    (hp : FormLE 0 B) (x : M.Carrier) :
    formNormSq g (positiveForm g A - B) x ≤ formNormSq g (A - B) x -
      formNormSq g (A - positiveForm g A) x := by
  rw [formNormSq_eq_pointFormHS g _ (realOneOne_sub _ _ (positiveForm_oneOne g A) hB),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub A B hA hB),
    formNormSq_eq_pointFormHS g _ (realOneOne_sub _ _ hA (positiveForm_oneOne g A))]
  simp only [pointFormHS, formHermitianMatrix_sub, positiveForm_matrix]
  apply relativePositivePart_distance_sq _ _ _
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
    ((G04Aux.representsSelf A hA).2 x)
  simpa only [formHermitianMatrix_zero, sub_zero] using hp x

end Yau.NodeProofs.P06Aux.Clip
