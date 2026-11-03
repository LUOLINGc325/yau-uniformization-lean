import Yau.Proofs.P03TopRepresentativeGlue
import Yau.Proofs.P03WeakRegularity

open scoped Manifold Topology ContDiff
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The actual homogeneous weak Dolbeault equation has a global holomorphic
representative equal to the original tensor for the geometric volume. -/
theorem weakDbar_zero_holomorphic_top_representative
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hE : Holomorphic (r := r) E)
    (u : NQForm E 0) (hu : WeakDbar (r := r) E u (zeroForm E 1)) :
    ∃ v : NQForm E 0, HolomorphicTopForm (r := r) E v ∧ ∀ᵐ x ∂μ, v x = u x := by
  classical
  choose f hf hae using fun a α => weakDbar_zero_holomorphic_coefficients E u hu a α
  let F : M.Carrier → ComplexVector n → ComplexVector r := fun a z =>
    WithLp.toLp 2 (fun α => f a α z)
  apply glue_holomorphic_top_representatives E g μ hμ hE u F
  · intro a
    exact (differentiableOn_piLp (𝕜 := ℂ) 2).mpr (hf a)
  · intro a
    have hall := ae_all_iff.mpr (hae a)
    filter_upwards [hall] with z hz
    ext α : 1
    exact hz α

end Yau.NodeProofs.P03Aux
