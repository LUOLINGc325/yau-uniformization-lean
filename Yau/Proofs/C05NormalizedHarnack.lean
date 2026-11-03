import Yau.Proofs.C05ScalarHarnack
import Yau.Proofs.C05DefectClock

/-! The genuine near-minimum scalar on the original normalized clock.
Its center value tends to zero on the same original good sequence. -/

noncomputable section
open scoped Topology

namespace Yau.Proofs.C05Aux
open Yau Blueprint Filter C04Aux
variable {n : ℕ} {X : KahlerManifold n}

def normalizedHarnackMinimum (h : Flow X) (ti R : ℝ) (x : Pt X) (z : ℝ) : ℝ :=
  minimizedScalarHarnack h x (ti + z / R) / R ^ 2

theorem normalizedHarnackMinimum_nonneg (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (ti R : ℝ) (x : Pt X) (z : ℝ)
    (ht : 0 < ti + z / R) : 0 ≤ normalizedHarnackMinimum h ti R x z :=
  div_nonneg (minimizedScalarHarnack_nonneg o h hH x ht) (sq_nonneg _)

theorem normalizedHarnackMinimum_le (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (ti R : ℝ) (x : Pt X) (z : ℝ)
    (ht : 0 < ti + z / R) :
    normalizedHarnackMinimum h ti R x z ≤ scalarHarnackSum h x (ti + z / R) / R ^ 2 :=
  div_le_div_of_nonneg_right (minimizedScalarHarnack_le o h hH x ht) (sq_nonneg _)

theorem normalizedHarnackMinimum_center_tendsto (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hR : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (hgood : Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
      (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0)) :
    Tendsto (fun i => normalizedHarnackMinimum h (tw i)
      (scalarCurvature (h (tw i)) o) o 0) atTop (𝓝 0) := by
  have hlow (i : ℕ) : 0 ≤ normalizedHarnackMinimum h (tw i)
      (scalarCurvature (h (tw i)) o) o 0 := by
    apply normalizedHarnackMinimum_nonneg o h hH
    simpa only [zero_div, add_zero] using htw i
  have hup (i : ℕ) : normalizedHarnackMinimum h (tw i)
      (scalarCurvature (h (tw i)) o) o 0 ≤
        scalarHarnackSum h o (tw i) / scalarCurvature (h (tw i)) o ^ 2 := by
    simpa only [zero_div, add_zero] using
      normalizedHarnackMinimum_le o h hH (tw i) (scalarCurvature (h (tw i)) o) o 0
        (by simpa only [zero_div, add_zero] using htw i)
  exact squeeze_zero hlow hup (normalized_center_defect_tendsto o h U P ρ hf tw htw hR hgood)

end Yau.Proofs.C05Aux
