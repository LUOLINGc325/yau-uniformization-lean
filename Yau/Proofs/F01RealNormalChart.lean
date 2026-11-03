import Yau.Proofs.F01NormalHolomorphicChart
import Yau.Proofs.F01HermitianZeroJet

/-! Actual holomorphic Kähler normal coordinates with the whole real first
metric jet zero, not only a formally chosen complex frame. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_real_normal_holomorphic_chart (g : SmoothMetric M) (k : HermitianField M)
    (p : M.Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      e 0 = p ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      pullbackMatrix g.form e 0 = 1 ∧
      (∀ i j, fderiv ℝ (fun z => pullbackMatrix g.form e z i j) 0 = 0) ∧
      ∃ values : Fin n → ℝ,
        pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  obtain ⟨e, hcenter, hsource, he, hei, hg, hz, values, hk⟩ :=
    exists_normal_holomorphic_chart g k p
  refine ⟨e, hcenter, hsource, he, hei, hg, ?_, values, hk⟩
  intro i j
  exact hermitian_matrix_real_first_jet_zero (pullbackMatrix g.form e) 0
    (pullbackMatrix_isHermitian g.form e) hz i j

end Yau.NodeProofs.F01Aux
