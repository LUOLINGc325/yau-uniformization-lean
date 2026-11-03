import Yau.Proofs.V04SymplecticSubmeanWeighted
import Yau.Proofs.V04SymplecticSubmeanMatrix
import Yau.Proofs.D05FrameBivector

open scoped Topology ContDiff Matrix
open MeasureTheory Set
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem average_finite_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) :
    circleAverage (fun θ ↦ ∑ i ∈ s, u i θ) = ∑ i ∈ s, circleAverage (u i) := by
  unfold circleAverage
  rw [intervalIntegral.integral_finsetSum (fun i hi ↦ (hu i hi).intervalIntegrable _ _)]
  rw [Finset.mul_sum]

/-- A finite matrix of genuine closed-disc holomorphic entries obeys the
same weighted squared-norm submean, including empty indices. -/
theorem weighted_matrix_submean {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ℝ → ℝ} (hw : ∀ θ, 0 < w θ) (hc : ContDiff ℝ ∞ w)
    (hp : Function.Periodic w (2 * Real.pi))
    (Z : ℂ → Matrix ι κ ℂ)
    (hZ : ∀ i j, ContDiffOn ℂ ∞ (fun z ↦ Z z i j) (Metric.closedBall (0 : ℂ) 1)) :
    Real.exp (circleAverage (fun θ ↦ Real.log (w θ))) * matrixFrobSq (Z 0) ≤
      circleAverage (fun θ ↦ w θ * matrixFrobSq (Z (circlePoint θ))) := by
  classical
  have hentry (i : ι) (j : κ) : Continuous (fun θ ↦ w θ * ‖Z (circlePoint θ) i j‖ ^ 2) :=
    hc.continuous.mul (((hZ i j).continuousOn.comp_continuous circlePoint_contDiff.continuous
      (fun θ ↦ circlePoint_mem_closedBall θ)).norm.pow 2)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦
    Finset.sum_le_sum (s := Finset.univ) (fun j hj ↦
      weighted_closedDisc_square_submean hw hc hp (hZ i j)))
  have hright : circleAverage (fun θ ↦ w θ * matrixFrobSq (Z (circlePoint θ))) =
      ∑ i, ∑ j, circleAverage (fun θ ↦ w θ * ‖Z (circlePoint θ) i j‖ ^ 2) := by
    simp only [matrixFrobSq, Finset.mul_sum]
    rw [average_finite_sum Finset.univ _ (fun i hi ↦ continuous_finsetSum _ (fun j hj ↦ hentry i j))]
    apply Finset.sum_congr rfl
    intro i hi
    exact average_finite_sum Finset.univ _ (fun j hj ↦ hentry i j)
  rw [hright]
  simpa only [matrixFrobSq, Finset.mul_sum] using hs

/-- The same factor and actual frame give the genuine holomorphic tensor. -/
def transformedTensor {n : ℕ} (E H : ℂ → CotangentMatrix n) (z : ℂ) : CotangentMatrix n :=
  H z * frameBivector (E z) * (H z)ᵀ

theorem transformedTensor_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} {f : ℂ → CotangentPoint M}
    {E H : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame G f E)
    (hH : ∀ i j, ContDiffOn ℂ ∞ (fun z ↦ H z i j) (Metric.closedBall (0 : ℂ) 1))
    (i j : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun z ↦ transformedTensor E H z i j) (Metric.closedBall (0 : ℂ) 1) := by
  unfold transformedTensor
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact ContDiffOn.sum fun b hb ↦
    (ContDiffOn.sum fun a ha ↦ (hH i a).mul (D05Proof.frameBivector_entry_contDiffOn hE.1 a b)).mul
      (hH j b)

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
