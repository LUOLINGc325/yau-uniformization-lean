import Yau.Proofs.F01RayleighChartInvariant
import Yau.Proofs.F01FixedRayleighSmooth
import Yau.Proofs.F01DiagonalRayleigh
import Yau.Proofs.F01ConformalSmooth

/-! The fixed-coordinate Rayleigh quotient is an actual smooth lower
support for the largest conformal relative eigenvalue, with equality at center. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalField_pullbackMatrix (g : HermitianField M) (f : M.Carrier → ℝ)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    pullbackMatrix (conformalField g f) e z =
      (Real.exp (f (e z)) : ℂ) • pullbackMatrix g e z := rfl

theorem diagonal_conformal_rayleigh_contact (hn : 0 < n)
    (g k : HermitianField M) (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hs : (0 : ComplexVector n) ∈ e.source)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hg0 : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ)
    (hk0 : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) :
    ∃ j : Fin n,
      let W := fun z => matrixRayleigh (pullbackMatrix (conformalField g f) e z)
        (pullbackMatrix k e z) (Pi.single j 1)
      0 < values j ∧
      ContDiffOn ℝ ∞ W e.source ∧
      (∀ z ∈ e.source, W z ≤ metricLargestRayleigh (conformalField g f) k (e z)) ∧
      W 0 = metricLargestRayleigh (conformalField g f) k (e 0) ∧
      W 0 = values j / Real.exp (f (e 0)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ values Finset.univ_nonempty
  have hsingle (i : Fin n) : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro h
    have hh := congrFun h i
    simpa using hh
  have hjpos : 0 < values j := by
    have hp := matrixQuadraticValue_pos (pullbackMatrix_posDef k e he hei hs) (hsingle j)
    simpa only [matrixQuadraticValue_single, hk0, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hp
  have hα0 : pullbackMatrix (conformalField g f) e 0 =
      (Real.exp (f (e 0)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [conformalField_pullbackMatrix, hg0]
  have hmaxvalue : metricLargestRayleigh (conformalField g f) k (e 0) =
      values j / Real.exp (f (e 0)) := by
    rw [← largestRayleigh_pullback_eq (conformalField g f) k e he hei hs, hα0, hk0]
    exact largestMatrixRayleigh_real_diagonal values j
      (fun i => hmax i (Finset.mem_univ i)) hjpos.le (Real.exp_pos _)
  refine ⟨j, hjpos, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (fixed_rayleigh_contDiffAt (conformalField g f) k
      (conformalField_metricSmooth hg hf) hk e he hei hz (hsingle j)).contDiffWithinAt
  · intro z hz
    exact fixed_chart_rayleigh_le_largest (conformalField g f) k e he hei hz _
  · dsimp only
    rw [hmaxvalue, matrixRayleigh_single, hα0, hk0]
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Complex.ofReal_re]
  · dsimp only
    rw [matrixRayleigh_single, hα0, hk0]
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Complex.ofReal_re]

end Yau.NodeProofs.F01Aux
