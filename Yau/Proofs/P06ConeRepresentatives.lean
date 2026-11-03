import Yau.Proofs.P06HodgeIntervalHeat
import Yau.Proofs.P06HodgePositiveHeat

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Membership in the genuine positive test cone fixes the actual fiber
positive part, as equality of original sections almost everywhere. -/
theorem positiveCone_representative_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hp : realizeActualForm g μ A hA ∈ hodgeL2PositiveCone g μ) :
    ∀ᵐ x ∂μ, A x = Clip.positiveForm g.form A x := by
  let hP := FiberApprox.positiveForm_l2_of_l2 g μ A hA h11
  have hn := positiveForm_Hilbert_normal g μ A hA h11 _ hp
  rw [real_inner_self_eq_norm_sq] at hn
  have hz : realizeActualForm g μ A hA =
      realizeActualForm g μ (Clip.positiveForm g.form A) hP := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (realizeActualForm g μ A hA -
      realizeActualForm g μ (Clip.positiveForm g.form A) hP)]
  exact (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hA)
    (L2FormSpace.ofSection (Clip.positiveForm g.form A) hP)).mp hz

/-- The same-C test cone fixes the exact signed fiber interval clip.
This includes C=0 and does not require a smooth representative. -/
theorem intervalCone_representative_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) {C : ℝ} (hC : 0 ≤ C)
    (hp : realizeActualForm g μ A hA ∈ hodgeL2IntervalCone g μ C) :
    ∀ᵐ x ∂μ, A x = Clip.intervalForm g.form C A x := by
  let hP := FiberApprox.intervalForm_l2_of_l2 g μ A hA h11 hC
  have hn := intervalForm_Hilbert_normal g μ hμ A hA h11 hC _ hp
  rw [real_inner_self_eq_norm_sq] at hn
  have hz : realizeActualForm g μ A hA =
      realizeActualForm g μ (Clip.intervalForm g.form C A) hP := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (realizeActualForm g μ A hA -
      realizeActualForm g μ (Clip.intervalForm g.form C A) hP)]
  exact (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hA)
    (L2FormSpace.ofSection (Clip.intervalForm g.form C A) hP)).mp hz

end Yau.NodeProofs.P06Aux
