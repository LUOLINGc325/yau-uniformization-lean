import Yau.Proofs.P03CoefficientMetrics

open scoped Manifold Topology ContDiff ComplexOrder Matrix TensorProduct
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar
open scoped CoefficientNorms CoefficientBundles

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_chartFrameGram (g : HermitianField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    hMat g a (chartPt a x) = hermitianGram (g x) (determinantFrameBasis a x hx) := by
  have hi : chartInv a (chartPt a x) = x := (extChartAt (ComplexModel n) a).left_inv hx
  ext i j
  simp only [hMat, hermitianGram, determinantFrameBasis_apply]
  change (g (chartInv a (chartPt a x))).toFun
      (chartVec a (chartInv a (chartPt a x)) (stdVec i))
      (chartVec a (chartInv a (chartPt a x)) (stdVec j)) = _
  rw [hi]

theorem hMat_det_chart_change (g : HermitianField M) (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    (hMat g a (chartPt a x)).det =
      star (determinantTransitionMatrix a b x).det *
        (hMat g b (chartPt b x)).det * (determinantTransitionMatrix a b x).det := by
  rw [hMat_chartFrameGram g a x ha, hMat_chartFrameGram g b x hb,
    determinantTransitionMatrix_eq_basisMatrix a b x ha hb]
  exact hermitianGram_det_changeBasis (g x)
    (determinantFrameBasis b x hb) (determinantFrameBasis a x ha)

theorem chartMetric_pairing (g : HermitianField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v w : TangentVector M x) :
    star (WithLp.ofLp (tangentCoords a x v)) ⬝ᵥ
      (hMat g a (chartPt a x) *ᵥ WithLp.ofLp (tangentCoords a x w)) = (g x).toFun v w := by
  rw [hMat_chartFrameGram g a x hx]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, determinantFrameBasis_repr,
    Pi.star_apply, mul_assoc] using
    hermitian_coordinates (g x) (determinantFrameBasis a x hx) v w

/-- The line metric defined in the centred chart has the same induced expression
in every overlapping genuine chart. -/
theorem antiCanonicalMetric_chart_apply (g : HermitianField M) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (u v : AntiCanonicalFiber M x) :
    (antiCanonicalMetric g x).toFun u v =
      star (u (chartTopForm a x hx)) * (hMat g a (chartPt a x)).det * v (chartTopForm a x hx) := by
  rw [antiCanonicalMetric_center_apply,
    antiCanonicalScalar_change a x x hx (mem_extChartAt_source x) u,
    antiCanonicalScalar_change a x x hx (mem_extChartAt_source x) v,
    hMat_det_chart_change g a x x hx (mem_extChartAt_source x)]
  simp only [gMat, star_mul]
  ring

theorem matrix_pairing_three_scalars {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (u v : ComplexVector r) (c d e : ℂ) :
    star (WithLp.ofLp (c • u)) ⬝ᵥ ((d • A) *ᵥ WithLp.ofLp (e • v)) =
      star c * d * e * (star (WithLp.ofLp u) ⬝ᵥ (A *ᵥ WithLp.ofLp v)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, PiLp.smul_apply, Matrix.smul_apply,
    smul_eq_mul, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tangentAntiCanonicalMetric_tmul (g : HermitianField M) (x : M.Carrier)
    (v w : TangentVector M x) (u u' : AntiCanonicalFiber M x) :
    (tangentAntiCanonicalMetric g x).toFun (v ⊗ₜ[ℂ] u) (w ⊗ₜ[ℂ] u') =
      (antiCanonicalMetric g x).toFun u u' * (g x).toFun v w := by
  rw [tangentAntiCanonicalMetric_center_pairing]
  simp only [tangentAntiCanonicalCoordinateLinearEquiv_tmul, tangentAntiCanonicalCenterMatrix]
  rw [matrix_pairing_three_scalars]
  rw [show gMat g x = hMat g x (chartPt x x) from rfl,
    chartMetric_pairing g x x (mem_extChartAt_source x) v w,
    antiCanonicalMetric_center_apply]
  rfl

end Yau.NodeProofs.P03Aux
