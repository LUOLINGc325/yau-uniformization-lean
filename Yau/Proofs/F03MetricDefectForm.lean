import Yau.Proofs.F03MetricDefectHeat

/-! The actual metric defect is smooth, closed real (1,1) initial data for the registered Hodge heat. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint NodeProofs.G04Aux LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem formHermitianMatrix_sub (A B : RealForm M 2) (x : M.Carrier) :
    formHermitianMatrix (A-B) x=formHermitianMatrix A x-formHermitianMatrix B x := by
  ext a b
  simp only [formHermitianMatrix,Pi.sub_apply,ContinuousAlternatingMap.sub_apply,
    Complex.ofReal_sub,Matrix.sub_apply]
  ring

theorem realOneOne_sub {A B : RealForm M 2} (hA : RealOneOne A) (hB : RealOneOne B) :
    RealOneOne (A-B) := by
  intro x u v
  simp only [Pi.sub_apply,ContinuousAlternatingMap.sub_apply,hA x u v,hB x u v]

theorem closedRealForm_sub {k : ℕ} {A B : RealForm M k}
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : ClosedRealForm A) (hcB : ClosedRealForm B) : ClosedRealForm (A-B) := by
  have hs : SmoothRealForm (A-B) := (L03.smoothFormSubmodule k).sub_mem hA hB
  have he : L03.exteriorRealForm (A-B)=0 := by
    rw [sub_eq_add_neg,← neg_one_smul ℝ B,
      L03.exteriorRealForm_add A ((-1:ℝ) • B) hA (L03.smoothRealForm_smul _ B hB),
      L03.exteriorRealForm_smul (-1) B hB,
      exterior_closed_eq_zero A hA hcA,exterior_closed_eq_zero B hB hcB]
    simp
  intro x z hz I
  rw [← L03.exteriorRealForm_represents (A-B) hs x z hz I,he,L03.formComponents_zero]
  rfl

def flowMetricDefectForm (X : KahlerManifold n) (h : Flow X) (s : ℝ) : RealForm X.manifold 2 :=
  omegaForm X.metric.form-omegaForm (h s)

theorem flowMetricDefectForm_matrix (X : KahlerManifold n) (h : Flow X) (s : ℝ) (x : Pt X) :
    formHermitianMatrix (flowMetricDefectForm X h s) x=gMat X.metric.form x-gMat (h s) x := by
  rw [flowMetricDefectForm,formHermitianMatrix_sub,
    NodeProofs.G04Aux.formHermitianMatrix_of_representsIota _ _ (omegaForm_represents X.metric.form),
    NodeProofs.G04Aux.formHermitianMatrix_of_representsIota _ _ (omegaForm_represents (h s))]

theorem flowMetricDefectForm_trace (X : KahlerManifold n) (h : Flow X) (s : ℝ) :
    formTrace X.metric.form (flowMetricDefectForm X h s)=flowMetricDefect X h s := by
  funext x
  rw [formTrace,flowMetricDefectForm_matrix]
  rfl

theorem flowMetricDefectForm_data (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {s : ℝ} (hs : 0 ≤ s) :
    BoundedOneOneData X.metric.form (flowMetricDefectForm X h s) ∧
      ClosedRealForm (flowMetricDefectForm X h s) ∧
      ∀ x,(formHermitianMatrix (flowMetricDefectForm X h s) x).PosSemidef := by
  have hg := L18Aux.metricSmooth_of_smoothMetric X.metric
  have hh := L23Aux.metricFamilySmooth_slice h hf.1.2.1 hs
  have hgk : KahlerClosed X.metric.form := by
    rw [← hf.1.1]
    exact hf.1.2.2.1 0 le_rfl
  have hsG := omegaForm_smooth X.metric.form hg
  have hsH := omegaForm_smooth (h s) hh
  refine ⟨⟨(L03.smoothFormSubmodule 2).sub_mem hsG hsH,
    realOneOne_sub (omegaForm_oneOne _) (omegaForm_oneOne _),1,by norm_num,?_⟩,
    closedRealForm_sub hsG hsH (omegaForm_closed _ hg hgk)
      (omegaForm_closed _ hh (hf.1.2.2.1 s hs)),?_⟩
  · intro x
    rw [flowMetricDefectForm_matrix]
    have hDefect := hf.2.2.2.2.1 s hs x
    have hG := (L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    have hH := (L18Aux.hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    constructor
    · convert hDefect.add hG using 1 <;> simp [gMat] <;> abel
    · convert hH using 1 <;> simp [gMat] <;> abel
  · intro x
    rw [flowMetricDefectForm_matrix]
    exact hf.2.2.2.2.1 s hs x

end Yau.Proofs.F03Aux
