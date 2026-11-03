import Yau.Proofs.C01RicciTimeBoundary
import Yau.Proofs.C01RicciNonnegative

/-! Initial strict Ricci positivity persists for a genuine interval:
the actual determinant is continuous from the right, and the already proved
positive-time Ricci matrices are positive semidefinite. -/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_posDef_initial_interval
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (hzero : (ricci (h 0) x).PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc 0 ε, (ricci (h t) x).PosDef := by
  have hd : ContDiffOn ℝ ∞ (fun t => (ricci (h t) x).det) (Set.Ici 0) :=
    Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_det
      (fun i j => localizedFlow_ricci_time_contDiffOn_nonneg hflow x i j)
  have hnz : (ricci (h 0) x).det ≠ 0 :=
    (hzero.isUnit.map Matrix.detMonoidHom).ne_zero
  have hc : Tendsto (fun t => (ricci (h t) x).det) (𝓝[Set.Ici 0] 0)
      (𝓝 (ricci (h 0) x).det) :=
    hd.continuousOn.continuousWithinAt (by change (0 : ℝ) ≤ 0; exact le_rfl)
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp (hc.eventually_ne hnz)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · simpa only [ht0] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact (localizedFlow_ricci_posSemidef_posTime hflow hjoint x htpos).posDef_iff_det_ne_zero.mpr
      (hsub ht)

end Yau.NodeProofs.C01Aux
