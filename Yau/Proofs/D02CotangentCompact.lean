import Yau.LeafProofs.L17ChartNaturality
import Yau.Proofs.V03MetricSmooth
import Yau.Proofs.V03DualTransport
import spec.WORKPACKAGES.«04».SPLICE_REPAIR.BridgeTargets

/-! Compact sets and metric boxes in the actual induced cotangent atlas.
The real metric is always the realification of the indicated Hermitian field. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- The frozen D02.00a statement for the same metric. -/
theorem sameMetricSmoothness : SpliceRepair.SameMetricSmoothness := by
  intro n M g _
  exact Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g

/-- Generic metric smoothness suffices for the actual dual quadratic form. -/
theorem dualNormChart_contDiffOn_of_metricSmooth
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n => dualNormChart g x p.1 p.2)
      (cotangentTarget x) := by
  have hξ (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n => p.2 i)
      (cotangentTarget x) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp contDiff_snd).contDiffOn
  have hinv (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n => (hMat g x p.1)⁻¹ i j) (cotangentTarget x) :=
    (entrywise_matrix_inv_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x)
      (fun z hz => ne_of_gt (hMat_posDef g x z hz).det_pos) i j).comp
        contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n =>
      ∑ i, star (p.2 i) * ∑ j, (hMat g x p.1)⁻¹ j i * p.2 j)
      (cotangentTarget x) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i)).mul
      (ContDiffOn.sum fun j _ => (hinv j i).mul (hξ j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

/-- The projection of an intrinsic compact is compact in the original base topology. -/
theorem cotangentCompact_projection {L : Set (CotangentPoint M)}
    (hL : CotangentCompact L) : IsCompact (Prod.fst '' L) := by
  obtain ⟨r, x, C, hC, rfl⟩ := hL
  rw [Set.image_iUnion]
  apply isCompact_iUnion
  intro i
  have h := (hC i).1.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) (x i)).continuousOn.comp
      continuous_fst.continuousOn (fun p hp => (hC i).2 hp |>.1))
  simpa only [Set.image_image, Function.comp_def, cotangentChartInv, chartInv] using h

/-- The exact D02.35a enclosure. The witnesses depend on the one compact set. -/
theorem cotangentCompactEnclosure : SpliceRepair.CotangentCompactEnclosure := by
  intro n M g hg L hL
  obtain ⟨r, x, C, hC, hLeq⟩ := hL
  let Q : Fin r → CotangentCoord n → ℝ :=
    fun i p => dualNormChart g (x i) p.1 p.2
  have hQ (i : Fin r) : ContinuousOn (Q i) (C i) :=
    (dualNormChart_contDiffOn_of_metricSmooth g hg (x i)).continuousOn.mono (hC i).2
  have hcompact : IsCompact (⋃ i, Q i '' C i) :=
    isCompact_iUnion fun i => (hC i).1.image_of_continuousOn (hQ i)
  obtain ⟨R, hR⟩ := hcompact.bddAbove
  refine ⟨Prod.fst '' L, max R 0, cotangentCompact_projection ⟨r, x, C, hC, hLeq⟩, ?_⟩
  intro y hy
  refine ⟨Set.mem_image_of_mem Prod.fst hy, ?_⟩
  rw [hLeq] at hy
  obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
  rw [dualNorm_cotangentChartInv g (x i) ((hC i).2 hp)]
  exact (hR (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem (Q i) hp⟩)).trans
    (le_max_left R 0)

end Yau.NodeProofs.D02Aux
