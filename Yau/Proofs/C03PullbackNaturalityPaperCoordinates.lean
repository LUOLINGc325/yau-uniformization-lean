import Yau.Proofs.P02BisectionalNaturality

/-! The paper's intrinsic bisectional numerator in any actual chart. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Yau Yau.LeafProofs.L12Aux Yau.NodeProofs.P02Aux
open scoped Manifold
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem paperBisectional_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (c x : M.Carrier) (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (U V : TangentVector M x) :
    paperBisectionalNumerator h x U V =
      coordinateBisectional h c (chartPt c x) (tangentCoords c x U) (tangentCoords c x V) := by
  let q : realTransportBundle M :=
    ⟨x, (realTangentEquiv x |>.symm U, realTangentEquiv x |>.symm V)⟩
  have H := transportBisectional_in_chart h hs c q hx
  have hcoord (W : TangentVector M x) :
      realTangentCoords c x ((realTangentEquiv x).symm W) = tangentCoords c x W := by
    rw [realTangentCoords_eq_complex_coords c x hx]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  simpa only [q, transportBisectional, ContinuousLinearEquiv.apply_symm_apply, hcoord] using H

end Yau.Proofs.C03Aux.PullbackNaturality
