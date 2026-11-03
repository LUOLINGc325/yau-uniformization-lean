import Yau.Proofs.P03NakanoBaseChange

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs Yau.LeafProofs.L14Aux

theorem nakano_leviCorrection_metric_inverse {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (H : Matrix (Fin r) (Fin r) ℂ) (V : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => G j i • H) (G⁻¹ * Matrix.of V) =
      (∑ i, ∑ j, ∑ α, ∑ β, star (V i α) * H α β * G⁻¹ i j * V j β).re := by
  have he : (G⁻¹)ᴴ * G * G⁻¹ = G⁻¹ := by
    rw [hG.inv.isHermitian.eq, Matrix.nonsing_inv_mul G (hG.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mul]
  calc
    _ = nakanoQuadratic (fun i j => ((G⁻¹)ᴴ * G * G⁻¹) j i • H) V :=
      nakano_leviCorrection_base_change G G⁻¹ H V
    _ = nakanoQuadratic (fun i j => G⁻¹ j i • H) V :=
      congrArg (fun L : Matrix (Fin n) (Fin n) ℂ => nakanoQuadratic (fun i j => L j i • H) V) he
    _ = _ := (nakano_leviCorrection_eq_kronecker G⁻¹ H V).trans
      (congrArg Complex.re (metricPairing_eq_kronecker G⁻¹ H V V).symm)

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Raising both anti-holomorphic slots with the original base inverse
metric recovers exactly the coefficient norm, with its top determinant. -/
theorem raised_metric_nakano_eq_coefficientInner (g : HermitianField M)
    (h : Metric (M := M) E) (x : M.Carrier) (V : Fin n → Fin r → ℂ) :
    (gMat g x)⁻¹.det.re * nakanoQuadratic
      (fun i j => gMat g x j i • BundleDbar.metricMatrix (r := r) E h x (chartPt x x))
      (fun i α => ∑ j, (gMat g x)⁻¹ i j * V j α) =
        (coefficientInner (r := r) E g h x V V).re := by
  have hc := nakano_leviCorrection_metric_inverse (gMat g x) (gMat_posDef g x)
    (BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) V
  have hi : (gMat g x)⁻¹.det.im = 0 := matrix_isHermitian_det_im _ (gMat_posDef g x).inv.isHermitian
  change (gMat g x)⁻¹.det.re * nakanoQuadratic
    (fun i j => gMat g x j i • BundleDbar.metricMatrix (r := r) E h x (chartPt x x))
    ((gMat g x)⁻¹ * Matrix.of V) = _
  rw [hc]
  unfold coefficientInner
  rw [Complex.mul_re, hi, zero_mul, sub_zero]

end Yau.NodeProofs.P03Aux
