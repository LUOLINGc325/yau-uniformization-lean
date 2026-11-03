import Yau.Proofs.F01RestrictedDiagonalNormalChart
import Yau.Proofs.F01ConformalRayleighContact

/-! Actual local Rayleigh supports on the conformal approximation manifold.
The chart, its zero background jet and its maximizing direction are constructed. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_restricted_conformal_rayleigh_support (g : SmoothMetric M)
    (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))
    (k : HermitianField (openConnectedManifold M S hS)) (hk : MetricSmooth k)
    (f : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f)
    (a : (openConnectedManifold M S hS).Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier,
    ∃ values : Fin n → ℝ, ∃ j : Fin n,
      let g0 := openRestrictedField M S hS g.form
      let W := fun z => matrixRayleigh (pullbackMatrix (conformalField g0 f) e z)
        (pullbackMatrix k e z) (Pi.single j 1)
      e 0 = a ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      pullbackMatrix g0 e 0 = 1 ∧
      (∀ i j, fderiv ℝ (fun z => pullbackMatrix g0 e z i j) 0 = 0) ∧
      pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) ∧
      0 < values j ∧ ContDiffOn ℝ ∞ W e.source ∧
      (∀ z ∈ e.source, W z ≤ metricLargestRayleigh (conformalField g0 f) k (e z)) ∧
      W 0 = metricLargestRayleigh (conformalField g0 f) k a ∧
      W 0 = values j / Real.exp (f a) := by
  obtain ⟨e, he0, hs, he, hei, hg0, hd0, values, hdiag⟩ :=
    exists_restricted_diagonal_normal_chart g S hS k a
  obtain ⟨j, hj, hW, hle, hcontact, hvalue⟩ := diagonal_conformal_rayleigh_contact
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos M)
    (openRestrictedField M S hS g.form) k
    (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g))
    hk f hf e hs (he.mdifferentiableOn (by simp)) (hei.mdifferentiableOn (by simp))
    hg0 values hdiag
  refine ⟨e, values, j, he0, hs, he, hei, hg0, hd0, hdiag, hj, hW, hle, ?_, ?_⟩
  · simpa only [he0] using hcontact
  · simpa only [he0] using hvalue

end Yau.NodeProofs.F01Aux
