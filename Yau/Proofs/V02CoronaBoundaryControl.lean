import Yau.Proofs.V02CoronaSolution
import Yau.Proofs.V02FiniteTraceControl
import Yau.Proofs.V03OuterUniqueness

/-! Actual corona coefficients inherit uniform supremum and Fourier bounds
from the same damped canonical correction. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {ι : Type*} [Fintype ι]

def coronaBoundaryTerm (a σ : ι → ℂ → ℂ) (α : ℂ → ℂ)
    (i : ι) : Option ι → ℝ → ℂ
  | none, θ => α (circlePoint θ) * σ i (circlePoint θ)
  | some j, θ => (α (circlePoint θ) * coronaDbarCorrection σ i j (circlePoint θ)) *
      a j (circlePoint θ)

theorem coronaBoundaryTerm_sum (a σ : ι → ℂ → ℂ) (α : ℂ → ℂ) (i : ι) (θ : ℝ) :
    ∑ k : Option ι, coronaBoundaryTerm a σ α i k θ =
      α (circlePoint θ) * coronaSolution a σ i (circlePoint θ) := by
  simp only [Fintype.sum_option, coronaBoundaryTerm, coronaSolution, mul_add,
    Finset.mul_sum, mul_assoc]

def coronaCoefficientSupBound (ι : Type*) [Fintype ι] (M N : ℝ) : ℝ :=
  (Fintype.card (Option ι) : ℝ) * max M (N * M)

def coronaCoefficientDSqBound (ι : Type*) [Fintype ι] (M D N Q : ℝ) : ℝ :=
  (Fintype.card (Option ι) : ℝ) ^ 2 *
    max (2 * M ^ 2 + 2 * D) (2 * M ^ 2 * Q + 2 * N ^ 2 * D)

theorem coronaSolution_damped_uniform_control
    {a σ : ι → ℂ → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (a i) (Metric.closedBall (0 : ℂ) 1))
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, σ i z * a i z = 1)
    {α : ℂ → ℂ} (hα : ContDiffOn ℂ ∞ α (Metric.closedBall (0 : ℂ) 1))
    {M D N Q : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (haM : ∀ i θ, ‖a i (circlePoint θ)‖ ≤ M)
    (hσM : ∀ i θ, ‖σ i (circlePoint θ)‖ ≤ M)
    (haD : ∀ i, boundaryDSq (fun θ (_ : Unit) => a i (circlePoint θ)) ≤ ENNReal.ofReal D)
    (hσD : ∀ i, boundaryDSq (fun θ (_ : Unit) => σ i (circlePoint θ)) ≤ ENNReal.ofReal D)
    (hα1 : ∀ θ, ‖α (circlePoint θ)‖ ≤ 1)
    (hαD : boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ)) ≤ 1)
    (hQN : ∀ i j θ, ‖α (circlePoint θ) * coronaDbarCorrection σ i j (circlePoint θ)‖ ≤ N)
    (hQD : ∀ i j, boundaryDSq (fun θ (_ : Unit) =>
      α (circlePoint θ) * coronaDbarCorrection σ i j (circlePoint θ)) ≤ ENNReal.ofReal Q) :
    0 ≤ coronaCoefficientSupBound ι M N ∧ 0 ≤ coronaCoefficientDSqBound ι M D N Q ∧ ∀ i,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ‖α z * coronaSolution a σ i z‖ ≤ coronaCoefficientSupBound ι M N) ∧
      boundaryDSq (fun θ (_ : Unit) =>
        α (circlePoint θ) * coronaSolution a σ i (circlePoint θ)) ≤
          ENNReal.ofReal (coronaCoefficientDSqBound ι M D N Q) := by
  let V : ℝ := max M (N * M)
  let T : ℝ := max (2 * M ^ 2 + 2 * D) (2 * M ^ 2 * Q + 2 * N ^ 2 * D)
  have hV : 0 ≤ V := hM.trans (le_max_left _ _)
  have hT : 0 ≤ T := (by positivity : 0 ≤ 2 * M ^ 2 + 2 * D).trans (le_max_left _ _)
  change 0 ≤ (Fintype.card (Option ι) : ℝ) * V ∧
    0 ≤ (Fintype.card (Option ι) : ℝ) ^ 2 * T ∧ _
  refine ⟨by positivity, by positivity, fun i => ?_⟩
  have hαc : Continuous (fun θ => α (circlePoint θ)) := hα.continuousOn.comp_continuous
    V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hac (j : ι) : Continuous (fun θ => a j (circlePoint θ)) :=
    (ha j).continuousOn.comp_continuous
      V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hσc (j : ι) : Continuous (fun θ => σ j (circlePoint θ)) :=
    (hσ j).continuousOn.comp_continuous
      V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hQc (j : ι) : Continuous (fun θ => coronaDbarCorrection σ i j (circlePoint θ)) :=
    (coronaDbarCorrection_contDiffOn hσ i j).continuousOn.comp_continuous
      V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have htc (k : Option ι) : Continuous (coronaBoundaryTerm a σ α i k) := by
    cases k with
    | none => exact hαc.mul (hσc i)
    | some j => exact (hαc.mul (hQc j)).mul (hac j)
  have htp (k : Option ι) : Function.Periodic (coronaBoundaryTerm a σ α i k) (2 * Real.pi) := by
    cases k with
    | none => exact V03Proof.circleTrace_periodic (fun z => α z * σ i z)
    | some j =>
        exact V03Proof.circleTrace_periodic (fun z => (α z * coronaDbarCorrection σ i j z) * a j z)
  have htV (k : Option ι) (θ : ℝ) : ‖coronaBoundaryTerm a σ α i k θ‖ ≤ V := by
    cases k with
    | none =>
        have hh : ‖coronaBoundaryTerm a σ α i none θ‖ ≤ M := by
          simpa only [coronaBoundaryTerm, norm_mul, one_mul] using
            mul_le_mul (hα1 θ) (hσM i θ) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        exact hh.trans (le_max_left _ _)
    | some j =>
        have hh : ‖coronaBoundaryTerm a σ α i (some j) θ‖ ≤ N * M := by
          simpa only [coronaBoundaryTerm, norm_mul] using
            mul_le_mul (hQN i j θ) (haM j θ) (norm_nonneg _) hN
        exact hh.trans (le_max_right _ _)
  have htD (k : Option ι) : boundaryDSq (fun θ (_ : Unit) =>
      coronaBoundaryTerm a σ α i k θ) ≤ ENNReal.ofReal T := by
    cases k with
    | none =>
        have hh := finiteTrace_product_boundaryDSq_le hαc (hσc i)
          (V03Proof.circleTrace_periodic α) (V03Proof.circleTrace_periodic (σ i))
          (by norm_num : (0 : ℝ) ≤ 1) hM (by norm_num : (0 : ℝ) ≤ 1) hD
          hα1 (hσM i) (by simpa using hαD) (hσD i)
        have he : 2 * M ^ 2 * 1 + 2 * (1 : ℝ) ^ 2 * D = 2 * M ^ 2 + 2 * D := by ring
        rw [he] at hh
        exact hh.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    | some j =>
        exact (finiteTrace_product_boundaryDSq_le (hαc.mul (hQc j)) (hac j)
          (V03Proof.circleTrace_periodic (fun z => α z * coronaDbarCorrection σ i j z))
          (V03Proof.circleTrace_periodic (a j)) hN hM hQ hD (hQN i j) (haM j)
          (hQD i j) (haD j)).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  constructor
  · apply V03Proof.norm_le_of_circle_bound
      (hα.mul (coronaSolution_complex_contDiffOn ha hσ hnorm i))
    intro θ
    rw [← coronaBoundaryTerm_sum]
    exact finiteTrace_sum_norm_le _ htV θ
  have hh := finiteTrace_sum_boundaryDSq_le htc htp hT htD
  change boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ) *
    coronaSolution a σ i (circlePoint θ)) ≤ ENNReal.ofReal ((Fintype.card (Option ι) : ℝ) ^ 2 * T)
  simpa only [coronaBoundaryTerm_sum] using hh

end Yau.Blueprint.V02Proof
