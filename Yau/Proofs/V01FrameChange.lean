import Yau.Proofs.V01PositiveMajorant
import Yau.Proofs.D05CotangentSymplectic
import Yau.Proofs.V03SpatialHessianTransport

/-! Fixed-chart majorants use the published geometric transition identities.
Only finite inverse and congruence algebra is performed here. -/

noncomputable section
open Matrix
open scoped Matrix Topology ContDiff Manifold
namespace Yau.Blueprint.V01Proof

theorem inverse_preserves_matrix_form
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T J : Matrix ι ι ℂ)
    (hT : IsUnit T) (hForm : T * J * Tᵀ = J) : T⁻¹ * J * T⁻¹ᵀ = J := by
  have hi : T⁻¹ * T = 1 :=
    Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
  have hit : Tᵀ * T⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  calc
    _ = T⁻¹ * (T * J * Tᵀ) * T⁻¹ᵀ := by rw [hForm]
    _ = (T⁻¹ * T) * J * (Tᵀ * T⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hi, hit, Matrix.one_mul, Matrix.mul_one]

theorem frameBivector_left_symplectic {n : ℕ} (T E : CotangentMatrix n)
    (hT : IsUnit T) (hForm : T * canonicalBivector * Tᵀ = canonicalBivector) :
    frameBivector (T * E) = frameBivector E := by
  unfold frameBivector
  rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  calc
    _ = E⁻¹ * (T⁻¹ * canonicalBivector * T⁻¹ᵀ) * E⁻¹ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [inverse_preserves_matrix_form T canonicalBivector hT hForm]

theorem frameInChart_isUnit {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) (z : ℂ)
    (hx : f z ∈ cotangentSource x) (hE : (E z).det ≠ 0) :
    IsUnit (frameInChart x f E z) := by
  have hT := Yau.Blueprint.V03Proof.cotangentTransition_mulVec_injective
    (f z).1 x (f z) (mem_extChartAt_source _) hx
  exact (Matrix.mulVec_injective_iff_isUnit.mp hT).mul
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hE))

theorem fixed_frameBivector {n : ℕ} {M : ComplexManifold n}
    (x : M.Carrier) (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) (z : ℂ)
    (hx : f z ∈ cotangentSource x) :
    frameBivector (frameInChart x f E z) = frameBivector (E z) := by
  have hT := Yau.Blueprint.V03Proof.cotangentTransition_mulVec_injective
    (f z).1 x (f z) (mem_extChartAt_source _) hx
  exact frameBivector_left_symplectic _ _ (Matrix.mulVec_injective_iff_isUnit.mp hT)
    (Yau.Blueprint.D05Proof.cotangentTransition_symplectic
      (f z).1 x (f z) (mem_extChartAt_source _) hx)

theorem centerTestHessian_fixed_chart {n q : ℕ} {X : KahlerManifold n}
    (d : VariationData X q) (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
    (hx : F.f 0 ∈ cotangentSource d.chart)
    (hTest : ContDiffAt ℝ 2 (fun z => d.test (cotangentChartInv d.chart z) F.s)
      (cotangentChart d.chart (F.f 0))) :
    centerTestHessian d F E =
      (frameInChart d.chart F.f E 0)ᴴ *
        leviMatrix (fun z => d.test (cotangentChartInv d.chart z) F.s)
          (cotangentChart d.chart (F.f 0)) cotangentDir *
      frameInChart d.chart F.f E 0 := by
  rw [centerTestHessian,
    Yau.Blueprint.V03Proof.spatialHessian_in_fixed_chart
      (fun y => d.test y F.s) d.chart hx hTest]
  simp only [frameInChart, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Yau.Blueprint.V01Proof
