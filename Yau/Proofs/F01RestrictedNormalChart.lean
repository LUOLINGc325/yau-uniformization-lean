import Yau.Proofs.F01RealNormalChart
import Yau.Proofs.F01RestrictedGram

/-! Ambient Kähler normal coordinates restrict to the actual open component.
The restricted field is used directly; completeness of that field is not assumed. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_restricted_real_normal_chart (g : SmoothMetric M)
    (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))
    (a : (openConnectedManifold M S hS).Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier,
      e 0 = a ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1 ∧
      (∀ i j, fderiv ℝ (fun z =>
        pullbackMatrix (openRestrictedField M S hS g.form) e z i j) 0 = 0) := by
  obtain ⟨e, he0, hs0, he, hei, hg0, hdg0, values, _⟩ :=
    exists_real_normal_holomorphic_chart g g.form a.val
  let q := openRestrictedChart M S hS e
  have hq0 : (0 : ComplexVector n) ∈ q.source :=
    mem_targetRestriction_source e S hS.nonempty.to_subtype hs0 (by rw [he0]; exact a.property)
  have hqeq : q 0 = a := by
    apply Subtype.ext
    exact (targetRestriction_value e S hS.nonempty.to_subtype hq0).trans he0
  have hgram : ∀ i j,
      (fun z => pullbackMatrix (openRestrictedField M S hS g.form) q z i j)
        =ᶠ[𝓝 (0 : ComplexVector n)] (fun z => pullbackMatrix g.form e z i j) := by
    intro i j
    filter_upwards [q.open_source.mem_nhds hq0] with z hz
    exact openRestrictedField_targetRestriction_coefficient M S hS g.form e he hz i j
  refine ⟨q, hqeq, hq0,
    targetRestriction_contMDiffOn e S hS.nonempty.to_subtype he,
    targetRestriction_inverse_contMDiffOn e S hS.nonempty.to_subtype hei, ?_, ?_⟩
  · ext i j
    exact ((hgram i j).eq_of_nhds).trans (congrFun (congrFun hg0 i) j)
  · intro i j
    exact (hgram i j).fderiv_eq.trans (hdg0 i j)

end Yau.NodeProofs.F01Aux
