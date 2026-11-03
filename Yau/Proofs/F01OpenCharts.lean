import Yau.Proofs.F01OpenRestriction

/-! The actual restricted charts agree with the ambient charts through the
inclusion. These statements retain target membership for inverse charts. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem complex_extend_eq {A : Type*} [TopologicalSpace A]
    (e : OpenPartialHomeomorph A (ComplexVector n)) :
    e.extend (ComplexModel n) = e.toPartialEquiv := by
  change e.toPartialEquiv.trans (PartialEquiv.refl _) = e.toPartialEquiv
  exact PartialEquiv.trans_refl _

theorem openInclusion_chartAt (a : (openConnectedManifold M S hS).Carrier) :
    chartAt (ComplexVector n) a = (chartAt (ComplexVector n) a.val).subtypeRestr ⟨a⟩ := rfl

theorem openInclusion_chartPt (a b : (openConnectedManifold M S hS).Carrier) :
    chartPt a b = chartPt a.val b.val := rfl

theorem openInclusion_chartTarget_subset (a : (openConnectedManifold M S hS).Carrier) :
    chartTarget a ⊆ chartTarget a.val := by
  simp only [chartTarget, extChartAt, complex_extend_eq]
  rw [openInclusion_chartAt M S hS a]
  exact (chartAt (ComplexVector n) a.val).subtypeRestr_target_subset (s := S) ⟨a⟩

theorem openInclusion_chartInv (a : (openConnectedManifold M S hS).Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    (chartInv a z).val = chartInv a.val z := by
  change S at a
  dsimp [openConnectedManifold] at hz ⊢
  have hz' : z ∈ ((chartAt (ComplexVector n) a.val).subtypeRestr ⟨a⟩).target := by
    simpa [chartTarget, extChartAt, ComplexModel, Opens.chartAt_eq] using hz
  simpa [chartInv, extChartAt, ComplexModel, Opens.chartAt_eq] using
    (chartAt (ComplexVector n) a.val).subtypeRestr_symm_apply (U := S) ⟨a⟩ hz'

end Yau.NodeProofs.F01Aux
