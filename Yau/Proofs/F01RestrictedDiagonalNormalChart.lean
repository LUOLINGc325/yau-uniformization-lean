import Yau.Proofs.F01RestrictedNormalChart
import Yau.Proofs.F01NormalChartDiagonalization
import Yau.Proofs.F01OpenMetricSmooth

/-! A normal holomorphic chart on the actual open component, diagonalizing
any actual second Hermitian metric while retaining the ambient real zero jet. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_restricted_diagonal_normal_chart (g : SmoothMetric M)
    (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))
    (k : HermitianField (openConnectedManifold M S hS))
    (a : (openConnectedManifold M S hS).Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier,
      e 0 = a ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1 ∧
      (∀ i j, fderiv ℝ (fun z =>
        pullbackMatrix (openRestrictedField M S hS g.form) e z i j) 0 = 0) ∧
      ∃ values : Fin n → ℝ,
        pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  obtain ⟨e, he0, hs, he, hei, hg0, hd0⟩ :=
    exists_restricted_real_normal_chart g S hS a
  obtain ⟨q, hq0, hqs, hq, hqi, hqg, hqd, values, hqk⟩ :=
    diagonalize_second_metric_in_normal_chart (openRestrictedField M S hS g.form) k
      (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g))
      e hs he hei hg0 hd0
  exact ⟨q, hq0.trans he0, hqs, hq, hqi, hqg, hqd, values, hqk⟩

end Yau.NodeProofs.F01Aux
