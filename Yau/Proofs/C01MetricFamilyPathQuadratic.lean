import Yau.Proofs.C01MetricQuadraticJets
import Yau.LeafProofs.L23FieldMetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! In a fixed genuine chart the actual real metric is jointly smooth,
and its evaluation on a C3 path velocity is jointly C2. No moving
coordinate frame or completeness is assumed. -/

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_realMetricInChart_contDiffOn
    (h : ℝ → HermitianField M) (I : Set ℝ) (hfamily : MetricFamilySmooth h I) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => realMetricInChart (h p.2) x p.1)
      (chartTarget x ×ˢ I) := by
  apply contDiffOn_realBilin_of_basis
  intro a b
  apply (hfamily x a b).congr
  intro p hp
  exact underlyingRealRiemannianMetric_frame (h p.2) x p.1 hp.1 a b

def fixedChartPathSpeedSq
    (h : ℝ → HermitianField M) (x : M.Carrier) (Z : ℝ → ComplexVector n) (p : ℝ × ℝ) : ℝ :=
  realMetricInChart (h p.1) x (Z p.2) (deriv Z p.2) (deriv Z p.2)

theorem fixedChartPathSpeedSq_contDiffOn
    (h : ℝ → HermitianField M) (I J : Set ℝ) (hfamily : MetricFamilySmooth h I)
    (hJ : IsOpen J) (x : M.Carrier) (Z : ℝ → ComplexVector n)
    (hZ : ContDiffOn ℝ 3 Z J) (hmap : Set.MapsTo Z J (chartTarget x)) :
    ContDiffOn ℝ 2 (fixedChartPathSpeedSq h x Z) (I ×ˢ J) := by
  have hD : ContDiffOn ℝ 2 (deriv Z) J :=
    ContDiffOn.deriv_of_isOpen (m := 2) hZ hJ (by norm_num)
  have hZ₂ : ContDiffOn ℝ 2 Z J := hZ.of_le (by norm_num)
  let F : (ComplexVector n × ℝ) → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
    fun p => realMetricInChart (h p.2) x p.1
  have hF : ContDiffOn ℝ 2 F (chartTarget x ×ˢ I) :=
    (metricFamily_realMetricInChart_contDiffOn h I hfamily x).of_le (by simp)
  let G : ℝ × ℝ → ComplexVector n × ℝ := fun p => (Z p.2, p.1)
  have hZG : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Z p.2) (I ×ˢ J) :=
    hZ₂.comp contDiffOn_snd (fun p hp => hp.2)
  have hG : ContDiffOn ℝ 2 G (I ×ˢ J) := hZG.prodMk contDiffOn_fst
  have hGF : Set.MapsTo G (I ×ˢ J) (chartTarget x ×ˢ I) :=
    fun p hp => ⟨hmap hp.2, hp.1⟩
  have hm : ContDiffOn ℝ 2 (F ∘ G) (I ×ˢ J) := hF.comp hG hGF
  have hV : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => deriv Z p.2) (I ×ˢ J) :=
    hD.comp contDiffOn_snd (fun p hp => hp.2)
  have H := (hm.clm_apply hV).clm_apply hV
  exact H

end Yau.NodeProofs.C01Aux
