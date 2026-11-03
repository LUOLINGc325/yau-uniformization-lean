import Yau.Proofs.F01ClosedWirtingerSmooth
import Yau.Proofs.F01MetricFamilyEntries

/-! Actual spatial logarithmic determinant and Ricci jets are jointly
smooth up to the original closed time faces. -/
noncomputable section
open Set
open scoped ContDiff Matrix Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_logDet_joint_smooth (h : ℝ → HermitianField M)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => logDet (h p.2) a p.1)
      (chartTarget a ×ˢ I) := by
  have hd := Complex.reCLM.contDiff.comp_contDiffOn
    (Yau.LeafProofs.L12Aux.contDiffOn_matrix_det
      (fun i j => metricFamily_hMat_contDiffOn h hh a i j))
  exact hd.log (fun p hp => (Yau.LeafProofs.L12Aux.hMat_det_re_pos
    (h p.2) a hp.1).ne')

theorem metricFamily_gMat_time_smooth (h : ℝ → HermitianField M)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => gMat (h t) a i j) I :=
  (metricFamily_hMat_contDiffOn h hh a i j).comp
    (contDiffOn_const.prodMk contDiffOn_id)
    (fun t ht => ⟨mem_extChartAt_target a, ht⟩)

theorem metricFamily_ricci_time_smooth (h : ℝ → HermitianField M)
    {I : Set ℝ} (hI : UniqueDiffOn ℝ I) (hh : MetricFamilySmooth h I)
    (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => ricci (h t) a i j) I := by
  have hl := closed_slab_leviC_smooth
    (isOpen_extChartAt_target (I := ComplexModel n) a) hI
    (metricFamily_logDet_joint_smooth h hh a) i j
  have ht := hl.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun t ht => ⟨mem_extChartAt_target a, ht⟩)
  exact ht.neg

end Yau.NodeProofs.F01Aux
