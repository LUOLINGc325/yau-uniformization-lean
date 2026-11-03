import Yau.Proofs.V03MetricSmooth

/-! The original metric norm equals its actual chart Gram quadratic form,
which is smooth in the point and vector coordinates. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def hermitianChartNormSq (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (hMat h x z *ᵥ WithLp.ofLp v)).re

theorem hermitianChartNormSq_eq_norm (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) :
    hermitianChartNormSq h x z v =
      hermitianNormSq (h (chartInv x z)) (chartVec x (chartInv x z) v) := by
  have hsum : (∑ i, v i • stdVec i) = v := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have hframe := congrArg (chartVec x (chartInv x z)) hsum
  simp only [chartVec_sum, chartVec_smul] at hframe
  unfold hermitianChartNormSq
  rw [hMat_quadratic, hframe]
  rfl

theorem hermitianChartNormSq_at_point (h : HermitianField M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    hermitianChartNormSq h x (chartPt x y) v = hermitianNormSq (h y) (chartVec x y v) := by
  rw [hermitianChartNormSq_eq_norm]
  exact congrArg (fun z : M.Carrier => hermitianNormSq (h z) (chartVec x z v))
    ((extChartAt (ComplexModel n) x).left_inv hy)

theorem hermitianChartNormSq_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n => hermitianChartNormSq g.form x p.1 p.2)
      (cotangentTarget x) := by
  have hξ (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n => p.2 i)
      (cotangentTarget x) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp contDiff_snd).contDiffOn
  have hmat (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n => hMat g.form x p.1 i j) (cotangentTarget x) :=
    (hMat_contDiffOn g x i j).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n =>
      ∑ i, star (p.2 i) * ∑ j, hMat g.form x p.1 i j * p.2 j)
      (cotangentTarget x) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i)).mul
      (ContDiffOn.sum fun j _ => (hmat i j).mul (hξ j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

theorem hermitianNormSq_ofReal_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (r : ℝ) (v : V) :
    hermitianNormSq h ((r : ℂ) • v) = r ^ 2 * hermitianNormSq h v := by
  have hstar : star (r : ℂ) = (r : ℂ) := by simp
  unfold hermitianNormSq
  rw [h.map_smul_left, h.map_smul_right, hstar]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  ring

end Yau.Blueprint.V03Proof
