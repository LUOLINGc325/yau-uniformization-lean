import Yau.Proofs.F04GraphLinear

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem realize_section_neg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hneg : L2RealForm g.form μ (-A)) :
    realizeL2Form g μ (L2FormSpace.ofSection (-A) hneg) =
      -realizeL2Form g μ (L2FormSpace.ofSection A hA) := by
  simp only [realizeL2Form]
  rw [← UniformSpace.Completion.coe_neg]
  congr 1

theorem realize_section_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (hsub : L2RealForm g.form μ (A - B)) :
    realizeL2Form g μ (L2FormSpace.ofSection (A - B) hsub) =
      realizeL2Form g μ (L2FormSpace.ofSection A hA) -
        realizeL2Form g μ (L2FormSpace.ofSection B hB) := by
  simp only [realizeL2Form]
  rw [← UniformSpace.Completion.coe_sub]
  congr 1

end Yau.F04Proof
