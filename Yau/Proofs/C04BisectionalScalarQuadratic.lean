import Yau.Proofs.C04BisectionalScalarPolarization

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ}

def metricQuadratic (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (H *ᵥ v)).re

theorem metricQuadratic_nonneg (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (v : Fin n → ℂ) : 0 ≤ metricQuadratic H v :=
  (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg v)).1

theorem metricQuadratic_le (H A : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (h : HermLE A ((c : ℂ) • H)) (v : Fin n → ℂ) :
    metricQuadratic A v ≤ c*metricQuadratic H v := by
  have hh := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg v)).1
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  exact sub_nonneg.mp hh

theorem metricQuadratic_parallelogram (H : Matrix (Fin n) (Fin n) ℂ)
    (u v : Fin n → ℂ) :
    metricQuadratic H (u+v) + metricQuadratic H (u-v) =
      2*metricQuadratic H u + 2*metricQuadratic H v := by
  simp only [metricQuadratic, star_add, star_sub, Matrix.mulVec_add,
    Matrix.mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct, Complex.add_re, Complex.sub_re]
  ring

theorem metricQuadratic_I (H : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    metricQuadratic H (Complex.I • u) = metricQuadratic H u := by
  simp [metricQuadratic, star_smul, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem metricQuadratic_add_sub_le (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (u v : Fin n → ℂ) :
    metricQuadratic H (u+v) ≤ 2*metricQuadratic H u+2*metricQuadratic H v ∧
      metricQuadratic H (u-v) ≤ 2*metricQuadratic H u+2*metricQuadratic H v := by
  have hh := metricQuadratic_parallelogram H u v
  have hp := metricQuadratic_nonneg H hH (u+v)
  have hm := metricQuadratic_nonneg H hH (u-v)
  constructor <;> linarith

variable {M : ComplexManifold n}

theorem bisectional_le_scalar (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hBC : NonnegBisectional k) (x : M.Carrier)
    (u v : Fin n → ℂ) :
    (curvatureValue (chernCurvature k x) u u v v).re ≤
      scalarCurvature k x * metricQuadratic (gMat k x) u * metricQuadratic (gMat k x) v := by
  let H := gMat k x
  let C := chernCurvature k x
  let D := P06Aux.scalarUniqueness_curvatureDirection C u
  have hH : H.PosDef := L12Aux.hMat_posDef k x _ (mem_extChartAt_target x)
  have hstar : ∀ i j a b, star (C i j a b) = C j i b a :=
    P06Aux.chernInChart_star k hs x _ (mem_extChartAt_target x)
  have hD : D.PosSemidef :=
    P06Aux.scalarUniqueness_curvatureDirection_posSemidef C hstar
      (fun a b => hBC x (WithLp.toLp 2 a) (WithLp.toLp 2 b)) u
  have htrace : traceWith H D = metricQuadratic (ricci k x) u := by
    unfold traceWith metricQuadratic
    rw [← P06Aux.scalarUniqueness_curvatureContraction_quadratic]
    have he : (fun a b => ∑ j, ∑ l, H⁻¹ j l * C b a j l) = ricci k x := by
      ext a b
      exact (P06Aux.ricci_eq_chern_contraction k hs hk x a b).symm
    rw [he]
  have hb := metricQuadratic_le H D (posSemidef_le_metric_trace H D hH hD) v
  rw [htrace] at hb
  have hr := metricQuadratic_le H (ricci k x) (ricci_scalar_bounds k hs hk hBC x).2.2 u
  have hv := metricQuadratic_nonneg H hH.posSemidef v
  have heq : metricQuadratic D v = (curvatureValue C u u v v).re := by
    exact congrArg Complex.re (P06Aux.scalarUniqueness_curvatureDirection_quadratic C u v)
  rw [heq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hr hv)

end Yau.Proofs.C04BisectionalScalarAux
