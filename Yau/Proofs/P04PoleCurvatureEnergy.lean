import Yau.Proofs.P04FlatNakano
import Yau.Proofs.P04PoleGlobalLevi
import Yau.Proofs.P04CompactQuadratic

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem flat_curvatureEnergy (g : HermitianField M) (φ : M.Carrier → ℝ)
    (x : M.Carrier) (V : Fin n → Fin 1 → ℂ) :
    curvatureEnergy (r := 1) (CanonicalCoefficients M) g flatMetric φ x V =
      (gMat g x)⁻¹.det.re *
        (star (fun i => ∑ j, (gMat g x)⁻¹ i j*V j 0) ⬝ᵥ
          (levi φ x *ᵥ (fun i => ∑ j, (gMat g x)⁻¹ i j*V j 0))).re := by
  unfold curvatureEnergy
  have hR : weightedCurvature (r := 1) (CanonicalCoefficients M) flatMetric φ x (chartPt x x) =
      fun i j => levi φ x j i • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    funext i j
    simp only [weightedCurvature,flat_curvature,flat_metricMatrix,zero_add,levi]
  rw [hR,nakano_line_quadratic]

theorem flat_curvatureEnergy_mono (g : HermitianField M) (φ ψ : M.Carrier → ℝ)
    (x : M.Carrier) (h : (levi φ x-levi ψ x).PosSemidef)
    (V : Fin n → Fin 1 → ℂ) :
    curvatureEnergy (r := 1) (CanonicalCoefficients M) g flatMetric ψ x V ≤
      curvatureEnergy (r := 1) (CanonicalCoefficients M) g flatMetric φ x V := by
  rw [flat_curvatureEnergy,flat_curvatureEnergy]
  apply mul_le_mul_of_nonneg_left
  · have H := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg
        (fun i => ∑ j, (gMat g x)⁻¹ i j*V j 0))).1
    simpa only [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,sub_nonneg] using H
  · exact (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1

/-- The actual variational inverse reverses the curvature order. -/
theorem flat_inverseCurvatureNormSq_antitone (g : HermitianField M)
    (φ ψ : M.Carrier → ℝ) (f : NQForm (CanonicalCoefficients M) 1)
    (x : M.Carrier) (h : (levi φ x-levi ψ x).PosSemidef) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g flatMetric φ f x ≤
      inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g flatMetric ψ f x := by
  apply iSup_mono
  intro V
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_sub_left (flat_curvatureEnergy_mono g φ ψ x h V) _

/-- Off the actual support, a semipositive variational inverse is exactly zero. -/
theorem flat_inverseCurvatureNormSq_zero (g : HermitianField M) (φ : M.Carrier → ℝ)
    (hN : WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric φ)
    (f : NQForm (CanonicalCoefficients M) 1) (x : M.Carrier)
    (hx : f x=(0 : NQForm (CanonicalCoefficients M) 1) x) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g flatMetric φ f x=0 := by
  apply le_antisymm
  · apply iSup_le
    intro V
    have hcoeff : (fun i α => coefficients (r := 1) (CanonicalCoefficients M) f x
        (chartPt x x) (fun _ => i) α)=0 := by
      funext i α
      simp only [coefficients]
      rw [show chartInv x (chartPt x x)=x from
        (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x),hx]
      simp only [L14Aux.nqForm_zero_apply,AlternatingMap.zero_apply,map_zero,PiLp.zero_apply,
        Pi.zero_apply]
    change ENNReal.ofReal (2*(coefficientInner (r := 1) (CanonicalCoefficients M) g flatMetric x
      (fun i α => coefficients (r := 1) (CanonicalCoefficients M) f x
        (chartPt x x) (fun _ => i) α) V).re-_) ≤ 0
    rw [hcoeff]
    have henergy := L14Aux.curvatureEnergy_nonneg (CanonicalCoefficients M) g flatMetric φ hN x V
    simp only [coefficientInner,Pi.zero_apply,star_zero,zero_mul,Finset.sum_const_zero,
      mul_zero,Complex.zero_re,mul_zero,zero_sub]
    exact (ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr henergy)).le
  · exact bot_le

end Yau.Proofs.P04Aux
