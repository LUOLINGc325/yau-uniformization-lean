import Yau.LeafProofs.L14RectangularCalculus
import Yau.LeafProofs.L14CoefficientTransitions
import Yau.LeafProofs.L14CurvatureAlgebra

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem holomorphic_raised_identity_dbar {n r : ℕ}
    (T : ComplexVector n → ComplexVector n)
    (J : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (c : ComplexVector n → ℂ)
    (U V : ComplexVector n → Matrix (Fin n) (Fin r) ℂ) (z : ComplexVector n)
    (hT : DifferentiableAt ℂ T z)
    (hJ : ∀ p q, DifferentiableAt ℂ (fun w => J w p q) z)
    (hA : ∀ α β, DifferentiableAt ℂ (fun w => A w α β) z)
    (hc : DifferentiableAt ℂ c z)
    (hU : ∀ p α, DifferentiableAt ℝ (fun w => U w p α) (T z))
    (hV : ∀ p α, DifferentiableAt ℝ (fun w => V w p α) z)
    (hEq : (fun w => J w * V w * (A w)ᵀ) =ᶠ[𝓝 z] (fun w => c w • U (T w))) (i : Fin n) :
    J z * rectangularWirtBar V z i * (A z)ᵀ =
      c z • ∑ q, star (fderiv ℂ T z (stdVec i) q) • rectangularWirtBar U (T z) q := by
  have hJr p q := (hJ p q).restrictScalars ℝ
  have hAr α β := (hA β α).restrictScalars ℝ
  have hJV := rectangular_mul_differentiableAt J V z hJr hV
  have hUT p α := (hU p α).comp z (hT.restrictScalars ℝ)
  have he := rectangularWirtBar_congr _ _ z hEq i
  rw [rectangularWirtBar_mul (fun w => J w * V w) (fun w => (A w)ᵀ) z hJV hAr i,
    rectangularWirtBar_mul J V z hJr hV i,
    rectangularWirtBar_holomorphic J z hJ i,
    rectangularWirtBar_holomorphic (fun w => (A w)ᵀ) z (fun α β => hA β α) i,
    rectangularWirtBar_smul c (fun w => U (T w)) z (hc.restrictScalars ℝ) hUT i,
    wirtBar_eq_zero_of_complex_differentiable c z (stdVec i) hc,
    rectangularWirtBar_comp U T z hT hU i] at he
  simpa only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, zero_smul] using he

theorem raised_dbar_tensor_solve {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) ℂ) (A C : Matrix (Fin r) (Fin r) ℂ)
    (X Y : Fin n → Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hCA : C * A = 1)
    (hEq : ∀ i, J * X i * Aᵀ = J.det • ∑ q, star (J q i) • Y q) (α : Fin r) (i j : Fin n) :
    X i j α =
      (J.det • ∑ γ, C α γ • (Jᴴ * (Matrix.of fun q p => Y q p γ) * (J⁻¹)ᵀ)) i j := by
  have htranspose : Aᵀ * Cᵀ = 1 := by rw [← Matrix.transpose_mul, hCA, Matrix.transpose_one]
  have hsolve (i : Fin n) : X i =
      J⁻¹ * (J.det • ∑ q, star (J q i) • Y q) * Cᵀ := by
    have he := congrArg (fun B : Matrix (Fin n) (Fin r) ℂ => J⁻¹ * B * Cᵀ) (hEq i)
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hJ,
      htranspose, Matrix.mul_one] using he
  rw [hsolve]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def raisedOneCoefficientsMatrix (g : HermitianField M) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) : Matrix (Fin n) (Fin r) ℂ :=
  (hMat g a z)⁻¹ * oneCoefficientsMatrix (r := r) E u a z

theorem raisedOneCoefficientsMatrix_contDiffOn (g : Yau.SmoothMetric M) (u : NQForm E 1)
    (hu : SmoothForm (r := r) E u) (a : M.Carrier) (i : Fin n) (α : Fin r) :
    ContDiffOn ℝ ∞ (fun w => raisedOneCoefficientsMatrix (r := r) E g.form u a w i α)
      (localDomain (r := r) E a) := by
  change ContDiffOn ℝ ∞ (fun w => ∑ j, (hMat g.form a w)⁻¹ i j *
    coefficients (r := r) E u a w (fun _ => j) α) _
  apply ContDiffOn.sum
  intro j _
  exact ((L18Aux.hMat_inverse_contDiffOn g a i j).mono Set.inter_subset_left).mul (hu a (fun _ => j) α)

theorem chartTransitionJacobian_det_isUnit (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    IsUnit (Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p).det := by
  classical
  let y := chartInv b z
  let ba := chartFrameBasis a y hz.2.1
  let bb := chartFrameBasis b y ((extChartAt (ComplexModel n) b).map_target hz.1.1)
  rw [← chartFrameBasis_toMatrix_fderiv a b z hz.1.1 hz.2.1]
  exact ba.isUnit_det bb

theorem raisedOneCoefficientsMatrix_overlap (g : HermitianField M) (u : NQForm E 1)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    let J := Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p
    J * raisedOneCoefficientsMatrix (r := r) E g u b z *
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᵀ =
        J.det • raisedOneCoefficientsMatrix (r := r) E g u a (chartPt a (chartInv b z)) := by
  dsimp only
  unfold raisedOneCoefficientsMatrix
  rw [hMat_overlap E g a b z hz, coefficients_one_overlap_matrix E u a b z hz]
  exact raised_coefficients_change _ _ _ _ _ (chartTransitionJacobian_det_isUnit E a b z hz)
    (bundleFrameTransitionMatrix_mul_reverse E b a (chartInv b z) hz.1.2 hz.2.2)

theorem raisedOneCoefficientsMatrix_wirtBar_overlap (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) (i : Fin n) :
    let T := fun w => chartPt a (chartInv b w)
    let J := Matrix.of fun p q => fderiv ℂ T z (stdVec q) p
    J * rectangularWirtBar (raisedOneCoefficientsMatrix (r := r) E g.form u b) z i *
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᵀ =
        J.det • ∑ q, star (J q i) •
          rectangularWirtBar (raisedOneCoefficientsMatrix (r := r) E g.form u a) (T z) q := by
  let T := fun w => chartPt a (chartInv b w)
  let J := fun w => Matrix.of fun p q => fderiv ℂ T w (stdVec q) p
  let A := fun w => bundleFrameTransitionMatrix (r := r) E b a (chartInv b w)
  let U := raisedOneCoefficientsMatrix (r := r) E g.form u a
  let V := raisedOneCoefficientsMatrix (r := r) E g.form u b
  have hTz : ContDiffAt ℂ ∞ T z := L18Aux.chartTransition_contDiffAt b a hz.1.1 hz.2.1
  have hJz (p q : Fin n) : ContDiffAt ℂ ∞ (fun w => J w p q) z := by
    have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hTz.fderiv_right (m := ∞) (by simp)
    exact (contDiffAt_piLp 2).mp (hD.clm_apply
      (show ContDiffAt ℂ ∞ (fun _ : ComplexVector n => stdVec q) z from contDiffAt_const)) p
  have hAz (α β : Fin r) : ContDiffAt ℂ ∞ (fun w => A w α β) z :=
    bundleFrameTransitionMatrix_contDiffAt E hE b a b z hz.1.1 hz.1.2 hz.2.2 α β
  have hU (p : Fin n) (α : Fin r) : DifferentiableAt ℝ (fun w => U w p α) (T z) :=
    ((raisedOneCoefficientsMatrix_contDiffOn E g u hu a p α).contDiffAt
      ((localDomain_isOpen E a).mem_nhds (chartTransition_maps_bundleChartOverlap E a b hz))).differentiableAt (by simp)
  have hV (p : Fin n) (α : Fin r) : DifferentiableAt ℝ (fun w => V w p α) z :=
    ((raisedOneCoefficientsMatrix_contDiffOn E g u hu b p α).contDiffAt
      ((localDomain_isOpen E b).mem_nhds hz.1)).differentiableAt (by simp)
  have hEq : (fun w => J w * V w * (A w)ᵀ) =ᶠ[𝓝 z] (fun w => (J w).det • U (T w)) := by
    filter_upwards [(bundleChartOverlap_isOpen E a b).mem_nhds hz] with w hw
    exact raisedOneCoefficientsMatrix_overlap E g.form u a b w hw
  exact holomorphic_raised_identity_dbar T J A (fun w => (J w).det) U V z
    (hTz.differentiableAt (by simp))
    (fun p q => (hJz p q).differentiableAt (by simp))
    (fun α β => (hAz α β).differentiableAt (by simp))
    ((holomorphic_determinant_contDiffAt J z hJz).differentiableAt (by simp)) hU hV hEq i

def raisedBarTensor (g : HermitianField M) (u : NQForm E 1) (a : M.Carrier)
    (z : ComplexVector n) (α : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => rectangularWirtBar (raisedOneCoefficientsMatrix (r := r) E g u a) z i j α

theorem raisedBarTensor_overlap (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) (α : Fin r) :
    let J := Matrix.of fun p q => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec q) p
    raisedBarTensor (r := r) E g.form u b z α =
      J.det • ∑ γ, bundleFrameTransitionMatrix (r := r) E a b (chartInv b z) α γ •
        (Jᴴ * raisedBarTensor (r := r) E g.form u a (chartPt a (chartInv b z)) γ * (J⁻¹)ᵀ) := by
  let J := Matrix.of fun p q => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec q) p
  let A := bundleFrameTransitionMatrix (r := r) E b a (chartInv b z)
  let C := bundleFrameTransitionMatrix (r := r) E a b (chartInv b z)
  let X := rectangularWirtBar (raisedOneCoefficientsMatrix (r := r) E g.form u b) z
  let Y := rectangularWirtBar (raisedOneCoefficientsMatrix (r := r) E g.form u a) (chartPt a (chartInv b z))
  have hEq (i : Fin n) : J * X i * Aᵀ = J.det • ∑ q, star (J q i) • Y q :=
    raisedOneCoefficientsMatrix_wirtBar_overlap E hE g u hu a b z hz i
  ext i j
  exact raised_dbar_tensor_solve J A C X Y (chartTransitionJacobian_det_isUnit E a b z hz)
    (bundleFrameTransitionMatrix_mul_reverse E a b (chartInv b z) hz.2.2 hz.1.2) hEq α i j

end Yau.LeafProofs.L14Aux
