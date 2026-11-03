import Yau.Proofs.F04SmoothPhysicalTime
import Yau.Proofs.F04SpaceTimeLaplacian
import Yau.Blueprint.Stages

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- Genuine closed physical smoothness carries the actual forced heat
 equation from positive time to BOTH closed time faces. -/
theorem physical_forced_equation_closed_of_positive
    {n : ℕ} (X : KahlerManifold n) (h : Flow X) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) {v f : STF X}
    (hv : SmoothSpaceTime v (Icc 0 T)) (hf : SmoothSpaceTime f (Icc 0 T))
    (hEq : ∀ x t, t ∈ Ioo 0 T → heatOp h (Icc 0 T) v x t = f x t) :
    ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) v x t = f x t := by
  have hTime := smoothSpaceTime_timeDerivative_smooth hT hv
  have hLap := metricFamily_laplacian_spaceTime_smooth h hT hh hv
  have hHC : ContinuousOn (fun p : Pt X × ℝ => heatOp h (Icc 0 T) v p.1 p.2) (univ ×ˢ Icc 0 T) :=
    smoothSpaceTime_continuousOn (fun c => (hTime c).sub (hLap c))
  have hFC := smoothSpaceTime_continuousOn hf
  intro x t ht
  have hL : ContinuousOn (fun s => heatOp h (Icc 0 T) v x s) (Icc 0 T) :=
    hHC.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨mem_univ x,hs⟩)
  have hF : ContinuousOn (f x) (Icc 0 T) :=
    hFC.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨mem_univ x,hs⟩)
  have he : EqOn (fun s => heatOp h (Icc 0 T) v x s) (f x) (Ioo 0 T) := fun s hs => hEq x s hs
  exact (he.of_subset_closure hL hF Ioo_subset_Icc_self
    (show Icc (0 : ℝ) T ⊆ closure (Ioo 0 T) by rw [closure_Ioo hT.ne])) ht

end Yau.F04Proof
