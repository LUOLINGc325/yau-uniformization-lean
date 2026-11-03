import Yau.Proofs.V04WallErrorInverseSpatial
import Yau.Proofs.V03MetricTime

/-! The Kähler symmetries needed by the finite inverse-metric identity,
including every fixed slice of the physical closed time domain. -/

open Filter
open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.G01Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_slice {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) : MetricSmooth (h t) := by
  intro x a b
  have hmap : Set.MapsTo (fun z : ComplexVector n => (z, t))
      (chartTarget x) (chartTarget x ×ˢ I) := fun z hz => ⟨hz, ht⟩
  exact (hh x a b).comp ((contDiff_id.prodMk contDiff_const).contDiffOn) hmap

theorem kahler_hMat_mixed_pair_symmetry
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (i j p q : Fin n) :
    wirt (fun w => wirtBar (fun u => hMat h x u p q) w (stdVec i)) z (stdVec j) =
      wirt (fun w => wirtBar (fun u => hMat h x u i j) w (stdVec p)) z (stdVec q) := by
  have hOp := isOpen_extChartAt_target (I := ComplexModel n) x
  have hF (a b : Fin n) : ContDiffAt ℝ 2 (fun w => hMat h x w a b) z :=
    ((Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth h hs x a b).contDiffAt
      (hOp.mem_nhds hz)).of_le (by simp)
  have hbar : (fun w => wirtBar (fun u => hMat h x u p q) w (stdVec i)) =ᶠ[𝓝 z]
      (fun w => wirtBar (fun u => hMat h x u i q) w (stdVec p)) := by
    filter_upwards [hOp.mem_nhds hz] with w hw
    exact kahler_hMat_wirtBar_symm h hs hk x w hw i p q
  have hhol : (fun w => wirt (fun u => hMat h x u i q) w (stdVec j)) =ᶠ[𝓝 z]
      (fun w => wirt (fun u => hMat h x u i j) w (stdVec q)) := by
    filter_upwards [hOp.mem_nhds hz] with w hw
    exact kahler_hMat_wirt_symm h hs hk x w hw j q i
  calc
    _ = wirt (fun w => wirtBar (fun u => hMat h x u i q) w (stdVec p)) z (stdVec j) := by
      simp only [wirt, hbar.fderiv_eq (𝕜 := ℝ)]
    _ = wirtBar (fun w => wirt (fun u => hMat h x u i q) w (stdVec j)) z (stdVec p) :=
      Yau.LeafProofs.L14Aux.wirt_wirtBar_comm _ z (hF i q) (stdVec p) (stdVec j)
    _ = wirtBar (fun w => wirt (fun u => hMat h x u i j) w (stdVec q)) z (stdVec p) := by
      simp only [wirtBar, hhol.fderiv_eq (𝕜 := ℝ)]
    _ = _ :=
      (Yau.LeafProofs.L14Aux.wirt_wirtBar_comm _ z (hF i j) (stdVec p) (stdVec q)).symm

end Yau.Blueprint.V04Proof.WallErrorAux
