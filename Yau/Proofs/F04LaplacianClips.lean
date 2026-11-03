import Yau.Proofs.F04Adjoint
import Yau.Proofs.F04SmoothPositiveScalar

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- Opposite smooth positive clips have exactly zero local Laplacian pairing.
 At positive f the negative clip vanishes on a neighborhood; elsewhere the
 positive clip is zero. -/
theorem laplacian_smoothPositive_cross_zero
    (H : HermitianField M) {δ : ℝ} (hδ : 0 < δ)
    {f : M.Carrier → ℝ} (hf : Continuous f) (x : M.Carrier) :
    smoothPositive δ (f x) * laplacian H (fun y => smoothPositive δ (-f y)) x = 0 := by
  by_cases hx : f x ≤ 0
  · rw [smoothPositive_of_nonpos hδ hx, zero_mul]
  · have hpos : 0 < f x := lt_of_not_ge hx
    have hnear : {y | 0 < f y} ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have he : (fun y => smoothPositive δ (-f y)) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hnear] with y hy
      exact smoothPositive_of_nonpos hδ (neg_nonpos.mpr hy.le)
    rw [laplacian_congr_of_eventuallyEq H he, Yau.LeafProofs.L18Aux.laplacian_const, mul_zero]

end Yau.F04Proof
