import Yau.Proofs.P06HodgeRegularityHeatEquation
import Yau.Proofs.P06HodgeSpectral

/-! Actual canonical positive heat representatives, with the prescribed
value at zero. The geometric representative is the proved Reg construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem exists_canonical_actual_heat {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ∃ U : ℝ → RealForm M k, U 0=A ∧ SmoothFormTime U (Set.Ioi 0) ∧
      FormHeatEquation g.form U ∧ ∀ t, 0 < t →
        ∃ hUt : L2RealForm g.form μ (U t), realizeActualForm g μ (U t) hUt =
          hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA) := by
  obtain ⟨V,hV,hVPDE,hVR⟩ := hodgeStrongPath_geometric_regularity g μ hμ
    (fun t => hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA))
    (hodgeHeatHilbert_strongPath g μ hμ k (realizeActualForm g μ A hA))
  let U : ℝ → RealForm M k := fun t => if 0<t then V t else A
  have hPos : ∀ t, 0 < t → U t=V t := fun t ht => if_pos ht
  refine ⟨U,by simp only [U,lt_self_iff_false,ite_false],?_,?_,?_⟩
  · intro x I
    apply (hV x I).congr
    intro p hp
    rw [hPos p.2 hp.2]
  · intro x z hz t ht I
    have hGerm : (fun s => formComponents (U s) x z I) =ᶠ[𝓝 t]
        (fun s => formComponents (V s) x z I) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [hPos s hs]
    rw [hPos t ht]
    exact (hVPDE x z hz t ht I).congr_of_eventuallyEq hGerm
  · intro t ht
    obtain ⟨hVt,hRt⟩ := hVR t ht
    have hUt : L2RealForm g.form μ (U t) := by rw [hPos t ht]; exact hVt
    refine ⟨hUt,?_⟩
    simpa only [hPos t ht] using hRt

end Yau.NodeProofs.P06Aux.CylinderReg
