import Yau.LeafProofs.L14Transitions

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficients_at_chartPt {q : ℕ} (u : NQForm E q) (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (I : Fin q → Fin n) :
    coefficients (r := r) E u a (chartPt a x) I =
      (localTriv (r := r) E a).continuousLinearMapAt ℂ x
        (((u x).1 (fun k => chartVec a x (stdVec (I k)))) (fun k => chartVec a x (stdVec k))) := by
  let F : M.Carrier → ComplexVector r := fun y =>
    (localTriv (r := r) E a).continuousLinearMapAt ℂ y
      (((u y).1 (fun k => chartVec a y (stdVec (I k)))) (fun k => chartVec a y (stdVec k)))
  exact congrArg F (chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx))

set_option backward.isDefEq.respectTransparency false in
theorem coefficients_one_overlap (u : NQForm E 1) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) (j : Fin n) :
    coefficients (r := r) E u b z (fun _ => j) =
      topBundleTransition (r := r) E a b z
        (∑ p, star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) p) •
          coefficients (r := r) E u a (chartPt a (chartInv b z)) (fun _ => p)) := by
  classical
  let y := chartInv b z
  have hya : y ∈ bundleChartSource (r := r) E a := hz.2
  have hyb : y ∈ bundleChartSource (r := r) E b :=
    ⟨(extChartAt (ComplexModel n) b).map_target hz.1.1, hz.1.2⟩
  let ba := chartFrameBasis a y hya.1
  let bb := chartFrameBasis b y hyb.1
  let d := bundleFrameBasis (r := r) E a y hya.2
  let V := fun p => ((u y).1 (fun _ => ba p)) ba
  have hvalue : ((u y).1 (fun _ => bb j)) bb =
      (ba.toMatrix bb).det • ∑ p, star (ba.coord p (bb j)) • V p := by
    have he := congrArg (fun P : (TangentVector M y) [⋀^Fin n]→ₗ[ℂ] E y => P bb)
      (antiOne_apply_basis_expansion ba (u y).1 (u y).2 (bb j))
    simp only [sum_apply, AlternatingMap.smul_apply] at he
    rw [he, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [alternating_apply_basis_change d ba bb ((u y).1 (fun _ => ba p))]
    exact smul_comm _ _ _
  have hJ (p : Fin n) : ba.coord p (bb j) =
      fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) p := by
    rw [chartFrameBasis_coord]
    rw [show bb j = chartVec b y (stdVec j) from chartFrameBasis_apply b y hyb.1 j]
    exact (congrArg (fun v : ComplexVector n => v p)
      (L18Aux.chartTransition_fderiv b a hz.1.1 hya.1 (stdVec j))).symm
  have hcoeffA (p : Fin n) :
      coefficients (r := r) E u a (chartPt a y) (fun _ => p) =
        (localTriv (r := r) E a).continuousLinearMapAt ℂ y (V p) := by
    rw [coefficients_at_chartPt E u a y hya.1]
    simp only [V, ba, chartFrameBasis_apply]
    congr 1
    congr 1
    exact funext (fun k => (chartFrameBasis_apply a y hya.1 k).symm)
  have hcoord (p : Fin n) :
      ((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) y : ComplexVector r →L[ℂ] ComplexVector r)
        (coefficients (r := r) E u a (chartPt a y) (fun _ => p)) =
          (localTriv (r := r) E b).continuousLinearMapAt ℂ y (V p) := by
    change (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) y
      (coefficients (r := r) E u a (chartPt a y) (fun _ => p)) = _
    rw [hcoeffA, bundleCoordChange_apply E a b y hya.2 hyb.2,
      Trivialization.symmL_continuousLinearMapAt _ hya.2]
  have hd : (fun k => chartVec b y (stdVec k)) = bb :=
    funext (fun k => (chartFrameBasis_apply b y hyb.1 k).symm)
  have hdj : (fun _ : Fin 1 => chartVec b y (stdVec j)) = (fun _ => bb j) :=
    funext (fun _ => (chartFrameBasis_apply b y hyb.1 j).symm)
  change (localTriv (r := r) E b).continuousLinearMapAt ℂ y
    (((u y).1 (fun _ => chartVec b y (stdVec j))) (fun k => chartVec b y (stdVec k))) = _
  rw [hd, hdj, hvalue, map_smul, map_sum]
  simp_rw [map_smul, hJ]
  rw [chartFrameBasis_toMatrix_fderiv a b z hz.1.1 hya.1]
  unfold topBundleTransition
  simp only [ContinuousLinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hcoord]
  exact smul_comm _ _ _

def oneCoefficientsMatrix (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n) (Fin r) ℂ := fun i α => coefficients (r := r) E u a z (fun _ => i) α

set_option backward.isDefEq.respectTransparency false in
theorem coefficients_one_overlap_matrix (u : NQForm E 1) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    let J := Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p
    oneCoefficientsMatrix (r := r) E u b z =
      J.det • (Jᴴ * oneCoefficientsMatrix (r := r) E u a (chartPt a (chartInv b z)) *
        (bundleFrameTransitionMatrix (r := r) E a b (chartInv b z))ᵀ) := by
  let J := Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p
  let F := oneCoefficientsMatrix (r := r) E u a (chartPt a (chartInv b z))
  let C := (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) (chartInv b z)
  ext i α
  change coefficients (r := r) E u b z (fun _ => i) α = _
  rw [coefficients_one_overlap E u a b z hz i]
  let Lα : ComplexVector r →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ α).comp C.toLinearMap
  change J.det * Lα (∑ p, star (J p i) • coefficients (r := r) E u a
    (chartPt a (chartInv b z)) (fun _ => p)) =
      J.det * (Jᴴ * F * (bundleFrameTransitionMatrix (r := r) E a b (chartInv b z))ᵀ) i α
  congr 1
  simp only [map_sum, map_smul, smul_eq_mul]
  have he (p : Fin n) : Lα (coefficients (r := r) E u a (chartPt a (chartInv b z)) (fun _ => p)) =
      ∑ β, C (stdVec β) α * F p β :=
    complexLinear_apply_coordinates C _ α
  simp_rw [he]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    bundleFrameTransitionMatrix, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro p _
  ring

end Yau.LeafProofs.L14Aux
