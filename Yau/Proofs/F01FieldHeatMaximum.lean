import Yau.Proofs.F01NormalizedChart
import Yau.Proofs.F01HeatChartNaturality
import Yau.Proofs.F01ClosedTimeSlices
import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01MetricEntryLog

/-! The actual native Hermitian heat operator is nonnegative at a
positive-time maximum, including the terminal time face. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem fieldHeatWithin_nonneg_at_max
    (h : ℝ → HermitianField M) (F : M.Carrier → ℝ → ℝ) {x : M.Carrier} {t T : ℝ}
    (hF : SmoothSpaceTime F (Icc 0 T)) (ht : 0 < t) (htT : t ≤ T)
    (hmax : IsMaxOn (fun p : M.Carrier × ℝ => F p.1 p.2) (univ ×ˢ Icc 0 T) (x, t)) :
    0 ≤ fieldHeatWithin h (Icc 0 T) (fun s y => F y s) x t := by
  obtain ⟨e, he0, hs, heSmooth, heiSmooth, hnormal, values, hdiag⟩ :=
    exists_normalized_holomorphic_chart (h t) (h t) x
  have he := heSmooth.mdifferentiableOn (by simp)
  have hei := heiSmooth.mdifferentiableOn (by simp)
  have hv (i : Fin n) : 0 < values i := by
    have hp := pullback_diagonal_pos (h t) e he hei hs i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hp
  let Fc := fun p : ComplexVector n × ℝ => F (e p.1) p.2
  obtain ⟨hspace, htime⟩ := closed_slab_slice_jets (smoothSpaceTime_holomorphic_chart hF e he)
    e.open_source hs (show t ∈ Icc 0 T from ⟨ht.le, htT⟩)
  have hmaxSpace : IsLocalMax (fun w => Fc (w, t)) 0 := by
    change ∀ᶠ w in 𝓝 0, F (e w) t ≤ F (e 0) t
    filter_upwards [e.open_source.mem_nhds hs] with w hw
    rw [he0]
    exact hmax (show (e w, t) ∈ univ ×ˢ Icc 0 T from ⟨mem_univ _, ht.le, htT⟩)
  have hmaxTime : IsMaxOn (fun s => Fc (0, s)) (Icc 0 T) t := by
    intro s hsI
    change F (e 0) s ≤ F (e 0) t
    rw [he0]
    exact hmax (show (x, s) ∈ univ ×ˢ Icc 0 T from ⟨mem_univ _, hsI⟩)
  have hnonneg := diagonalHeatWithin_nonneg_at_max values hv Fc ht htT hspace hmaxSpace htime hmaxTime
  rw [diagonalHeatWithin_holomorphic_chart h (fun s y => F y s) (Icc 0 T) e he hei hs t
    (smoothSpaceTime_slice hF ⟨ht.le, htT⟩) values hdiag] at hnonneg
  simpa only [he0] using hnonneg

end Yau.NodeProofs.F01Aux
