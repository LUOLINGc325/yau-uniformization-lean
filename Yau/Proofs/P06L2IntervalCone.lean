import Yau.Proofs.P06IntervalResidualForms
import Yau.Proofs.P06TraceHilbertMaps
import Yau.Proofs.P06CutoffData
import Yau.Proofs.P06MetricCutoffs

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The same paper bound C, tested against all positive raw L² forms whose
trace is genuinely integrable; infinite volume causes no totalized integral. -/
def hodgeL2IntervalCone (g : SmoothMetric M) (μ : Measure M.Carrier) (C : ℝ) : Set (L2FormHilbert g μ 2) :=
  {f | oneOneProjectionHilbert g μ f = f ∧
    ∀ (B : RealForm M 2) (hB : L2RealForm g.form μ B), RealOneOne B → FormLE 0 B →
      Integrable (formTrace g.form B) μ →
      |inner ℝ f (realizeActualForm g μ B hB)| ≤ C * ∫ x, formTrace g.form B x ∂μ}

theorem hodgeL2IntervalCone_isClosed (g : SmoothMetric M) (μ : Measure M.Carrier) (C : ℝ) :
    IsClosed (hodgeL2IntervalCone g μ C) := by
  simp only [hodgeL2IntervalCone, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter (isClosed_eq (oneOneProjectionHilbert g μ).continuous continuous_id)
  refine isClosed_iInter (fun B => isClosed_iInter (fun hB => isClosed_iInter (fun _ =>
    isClosed_iInter (fun _ => isClosed_iInter (fun _ => ?_)))))
  exact isClosed_le (continuous_id.inner continuous_const).abs continuous_const

theorem realizeActualForm_mem_hodgeL2IntervalCone (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) {C : ℝ}
    (hbound : FormOrderBound g.form C A) : realizeActualForm g μ A hA ∈ hodgeL2IntervalCone g μ C := by
  constructor
  · rw [oneOneProjectionHilbert_realize]
    apply realizeActualForm_congr
    exact P06Weitzenbock.oneOneProjection_fixed A h11
  · intro B hB h11B hpB htr
    rw [realizeActualForm_inner]
    calc
      _ ≤ ∫ x, |formInner g.form A B x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * formTrace g.form B x ∂μ :=
        integral_mono (formInner_integrable g μ A B hA hB).abs (htr.const_mul C) (fun x => by
          rw [congrFun (formInner_symm g.form A B) x]
          exact formInner_abs_le_trace_bound g.form B A h11B hpB h11 hbound x)
      _ = _ := integral_const_mul _ _

theorem formTrace_multiply_raw (g : HermitianField M) (η : M.Carrier → ℝ)
    (B : RealForm M 2) (h11 : RealOneOne B) (x : M.Carrier) :
    formTrace g (multiplyRealForm η B) x = η x * formTrace g B x := by
  rw [← formInner_omegaForm g _ (realOneOne_multiply η B h11) x,
    multiplyRealForm_inner_left, formInner_omegaForm g B h11 x]

theorem contact_cutoff_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (P B : RealForm M 2) (hP : L2RealForm g.form μ P) (hB : L2RealForm g.form μ B)
    (h11 : RealOneOne B) (c : ℝ) (hcontact : ∀ x, formInner g.form P B x = c * formTrace g.form B x)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    inner ℝ (realizeActualForm g μ P hP) (realizeActualForm g μ (multiplyRealForm η B)
      (l2RealForm_multiply_smooth_compact g μ η hη hcη B hB)) =
        c * ∫ x, formTrace g.form (multiplyRealForm η B) x ∂μ := by
  rw [realizeActualForm_inner]
  calc
    _ = ∫ x, c * formTrace g.form (multiplyRealForm η B) x ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [multiplyRealForm_inner_right, hcontact, formTrace_multiply_raw g.form η B h11 x]
        ring)
    _ = _ := integral_const_mul _ _

theorem formLE_multiply_nonnegative (g : HermitianField M) (η : M.Carrier → ℝ)
    (hη : ∀ x, 0 ≤ η x) (B : RealForm M 2) (hB : FormLE 0 B) :
    FormLE 0 (multiplyRealForm η B) := by
  intro x
  rw [formHermitianMatrix_multiply, formHermitianMatrix_zero, sub_zero]
  have hp : (formHermitianMatrix B x).PosSemidef := by
    simpa only [formHermitianMatrix_zero, sub_zero] using hB x
  exact hp.smul (Complex.nonneg_iff.mpr ⟨hη x, rfl⟩)

end Yau.NodeProofs.P06Aux
