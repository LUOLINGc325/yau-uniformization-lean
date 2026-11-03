import Yau.Proofs.P01BusemannLimit
import spec.CHAIN.CONTRACTS
import Yau.LeafProofs.L12

noncomputable section
open Filter
open scoped Topology NNReal

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux

theorem uniformOn_compact_of_common_lipschitz {E : Type*} [MetricSpace E]
    (f : ℕ → E → ℝ) (b : E → ℝ)
    (hlip : ∀ j x y, |f j x - f j y| ≤ dist x y)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (b x)))
    (K : Set E) (hK : IsCompact K) : TendstoUniformlyOn f b atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLipK (j : ℕ) : LipschitzWith 1 (fun x : K => f j x) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa only [Real.dist_eq, Subtype.dist_eq] using hlip j x y
  have hEqui : Equicontinuous (fun j (x : K) => f j x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 hLipK).equicontinuous
  have hPoint : Tendsto (fun j (x : K) => f j x) atTop (𝓝 (fun x : K => b x)) :=
    tendsto_pi_nhds.mpr (fun x => hlim x)
  have H := (hEqui.tendsto_uniformFun_iff_pi atTop (fun x : K => b x)).mpr hPoint
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp H

def signedDistanceSeq {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (ray : ℝ≥0 → Pt X) (j : ℕ) (x : Pt X) : ℝ :=
  distFrom X.metric.form o (ray j) - distFrom X.metric.form x (ray j)

theorem signedDistanceSeq_lipschitz {n : ℕ} (X : KahlerManifold n)
    (o : Pt X) (ray : ℝ≥0 → Pt X) (j : ℕ) (x y : Pt X) :
    |signedDistanceSeq X o ray j x - signedDistanceSeq X o ray j y| ≤
      distFrom X.metric.form x y := by
  letI := inducedMetricSpace X.metric
  exact P01Aux.signedDistanceSequence_sub_abs_le o ray x y j

theorem busemann_continuous {n : ℕ} (X : KahlerManifold n) (b : Pt X → ℝ)
    (hlip : ∀ x y, |b x - b y| ≤ distFrom X.metric.form x y) : Continuous b := by
  letI := inducedMetricSpace X.metric
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.dist_eq]
  exact hlip x y

theorem busemann_uniformOn_compact {n : ℕ} (X : KahlerManifold n)
    (o : Pt X) (ray : ℝ≥0 → Pt X) (b : Pt X → ℝ)
    (hlim : ∀ x, Tendsto (fun j : ℕ => signedDistanceSeq X o ray j x) atTop (𝓝 (b x)))
    (_hlip : ∀ x y, |b x - b y| ≤ distFrom X.metric.form x y)
    (K : Set (Pt X)) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j x => signedDistanceSeq X o ray j x) b atTop K := by
  letI := inducedMetricSpace X.metric
  exact uniformOn_compact_of_common_lipschitz _ b
    (signedDistanceSeq_lipschitz X o ray) hlim K hK

theorem busemann_le_distance {n : ℕ} (X : KahlerManifold n)
    (o : Pt X) (ray : ℝ≥0 → Pt X) (b : Pt X → ℝ)
    (hlim : ∀ x, Tendsto (fun j : ℕ => signedDistanceSeq X o ray j x) atTop (𝓝 (b x)))
    (hlip : ∀ x y, |b x - b y| ≤ distFrom X.metric.form x y) :
    b o = 0 ∧ ∀ x, b x ≤ distFrom X.metric.form o x := by
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (b o)) := by
    simpa only [signedDistanceSeq, sub_self] using hlim o
  have hb0 : b o = 0 := tendsto_nhds_unique hz tendsto_const_nhds
  refine ⟨hb0, ?_⟩
  intro x
  have H := (abs_le.mp (hlip o x)).1
  rw [hb0] at H
  linarith

end Yau.NodeProofs.P02Aux
