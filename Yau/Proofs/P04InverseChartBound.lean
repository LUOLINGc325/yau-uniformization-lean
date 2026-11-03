import Yau.Proofs.P04VariationalBound
import Yau.LeafProofs.L14InverseMeasurable

noncomputable section
open Set WithLp MeasureTheory
open scoped Topology Manifold ContDiff InnerProductSpace Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem flat_matrixCoefficientPairing (F U : Fin n → Fin 1 → ℂ) :
    matrixCoefficientPairing (1 : Matrix (Fin 1) (Fin 1) ℂ) F U =
      ∑ i, star (F i 0)*U i 0 := by
  simp only [matrixCoefficientPairing,Fintype.sum_unique,Matrix.one_apply,
    ite_true,mul_one]
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd]

/-- The actual chart variational inverse is bounded by the proved scalar
quadratic estimate; the curvature matrix is the computed flat-line Levi. -/
theorem flat_chartInverseCurvatureCoefficientSup_le (φ : M.Carrier → ℝ)
    (f : NQForm (CanonicalCoefficients M) 1) (a : M.Carrier) (z : ComplexVector n)
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ v : ComplexVector n, δ*‖v‖^2 ≤ matrixQuadratic (leviC (inChart a φ) z) v) :
    L14Aux.chartInverseCurvatureCoefficientSup (r := 1) (CanonicalCoefficients M) flatMetric φ f a z ≤
      ENNReal.ofReal (‖(toLp 2 (fun i => coefficients (r := 1) (CanonicalCoefficients M)
        f a z (fun _ => i) 0) : ComplexVector n)‖^2/δ) := by
  apply iSup_le
  intro V
  have hR : weightedCurvature (r := 1) (CanonicalCoefficients M) flatMetric φ a z =
      fun i j => leviC (inChart a φ) z j i • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    funext i j
    simp only [weightedCurvature,flat_curvature,flat_metricMatrix,zero_add]
  change ENNReal.ofReal (2*(matrixCoefficientPairing
    (BundleDbar.metricMatrix (r := 1) (CanonicalCoefficients M) flatMetric a z)
    (fun i α => coefficients (r := 1) (CanonicalCoefficients M) f a z (fun _ => i) α) V).re-
    nakanoQuadratic (weightedCurvature (r := 1) (CanonicalCoefficients M) flatMetric φ a z) V) ≤ _
  rw [flat_metricMatrix,flat_matrixCoefficientPairing,hR,nakano_line_quadratic]
  apply ENNReal.ofReal_le_ofReal
  exact scalar_variational_bound _ hδ hlower _ _

theorem flat_inverseCurvatureNormSq_inChart_le (g : SmoothMetric M)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (f : NQForm (CanonicalCoefficients M) 1) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget a)
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ v : ComplexVector n, δ*‖v‖^2 ≤ matrixQuadratic (leviC (inChart a φ) z) v) :
    inverseCurvatureNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric φ f (chartInv a z) ≤
      ENNReal.ofReal (((hMat g.form a z).det.re)⁻¹*
        (‖(toLp 2 (fun i => coefficients (r := 1) (CanonicalCoefficients M)
          f a z (fun _ => i) 0) : ComplexVector n)‖^2/δ)) := by
  have hz' : z ∈ localDomain (r := 1) (CanonicalCoefficients M) a := by
    rwa [coefficient_localDomain]
  rw [L14Aux.inverseCurvatureNormSq_inChart (CanonicalCoefficients M) coefficient_holomorphic
    g.form flatMetric flatMetric_smooth φ hφ f a z hz',
    ENNReal.ofReal_mul (inv_nonneg.mpr (L18Aux.hMat_det_re_pos g.form a hz).le)]
  exact mul_le_mul_right (flat_chartInverseCurvatureCoefficientSup_le φ f a z hδ hlower) _

end Yau.Proofs.P04Aux
