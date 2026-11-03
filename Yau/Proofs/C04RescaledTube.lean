import Yau.Proofs.C04RescaledTubeWindowBounds
import Yau.Proofs.C04RescaledTubeScalarBound
import Yau.Proofs.C04RescaledTubeRealFlow
import Yau.Proofs.C04RescaledTubePointwise
import Yau.Proofs.C04RescaledTubeLocalJets
import Yau.Proofs.C04MetricTimeComparison

/-! Intrinsic all-order curvature tubes on fixed central rescaled balls.
The one discarded sequence prefix and the time radius precede the spatial
radius. Every bound is proved from the original localized flow and Harnack
completeness, with the original local curvature derivative theorem. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs C04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem rescaled_central_ball_curvature_jets (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (a K : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hK : 1 ≤ K) (S tw : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (hwindow : ∀ i t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S i →
      ρ o t' = a * S i → clockSpeed o h t ≤ K * clockSpeed o h t')
    (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hmiddle : ∀ i, 5 * S i / 4 ≤ ρ o (tw i) ∧ ρ o (tw i) ≤ 7 * S i / 4) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ N : ℕ, ∀ r : ℝ, 0 < r →
      ∃ b : ℝ, 0 < b ∧ ∃ Kjet : ℕ → ℝ, (∀ m, 0 < Kjet m) ∧
        ∀ i : ℕ, N ≤ i → ∀ hRi : 0 < scalarCurvature (h (tw i)) o,
          ∀ p ∈ distBall (scaleField (scalarCurvature (h (tw i)) o) hRi (h (tw i))) o r,
            ∀ z : ℝ, |z| < θ →
              let R := scalarCurvature (h (tw i)) o
              let k := scaleField R hRi (h (tw i + z / R))
              0 < tw i + z / R ∧ MetricSmooth k ∧ KahlerClosed k ∧
                IsCompleteDistance (lengthDist k) ∧
                ∀ m : ℕ, ∀ x ∈ distBall k p (2 * b), curvatureJetNorm k m x ≤ Kjet m := by
  obtain ⟨δ, B, hδ, hB, N, hN⟩ := rescaled_window_base_bounds X o h U P ρ hf hH
    a K ha ha1 hK S tw hS hwindow htw htwinf hmiddle
  let θ := δ / 8
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let R : ℕ → ℝ := fun i => scalarCurvature (h (tw i)) o
  have hR (i : ℕ) : 0 < R i := scalar_pos X o h hH (htw i).le o
  let g : ℕ → ℝ → HermitianField X.manifold :=
    fun i z => scaleField (R i) (hR i) (h (tw i + z / R i))
  let I := Set.Icc (-2 * θ) (2 * θ)
  have hbase (i : ℕ) (hi : N ≤ i) (z : ℝ) (hz : |z| ≤ 8 * θ) :
      0 < tw i + z / R i ∧ scalarCurvature (g i z) o ≤ B := by
    apply (hN i hi).2 (hR i) z
    dsimp only [θ] at hz
    linarith
  have hq (i : ℕ) (hi : N ≤ i) : 16 * θ ≤ tw i * R i := by
    have hh := (hN i hi).1
    change 8 * δ ≤ tw i * R i at hh
    dsimp only [θ]
    linarith
  have htime (i : ℕ) (hi : N ≤ i) (t : ℝ) (ht : t ∈ I) :
      0 < tw i + t / R i := by
    apply (hbase i hi t ?_).1
    apply abs_le.2
    constructor <;> linarith [ht.1, ht.2]
  have hs (i : ℕ) (hi : N ≤ i) (t : ℝ) (ht : t ∈ I) : MetricSmooth (g i t) :=
    metricSmooth_scale (R i) (hR i) _
      (localizedFlow_metricSmooth X o h U P ρ hf (htime i hi t ht).le)
  have hk (i : ℕ) (hi : N ≤ i) (t : ℝ) (ht : t ∈ I) : KahlerClosed (g i t) :=
    kahlerClosed_scale (R i) (hR i) _
      (localizedFlow_metricSmooth X o h U P ρ hf (htime i hi t ht).le)
      (hf.1.2.2.1 _ (htime i hi t ht).le)
  have hc (i : ℕ) (hi : N ≤ i) (t : ℝ) (ht : t ∈ I) :
      IsCompleteDistance (lengthDist (g i t)) :=
    complete_scale (R i) (hR i) _
      (localizedFlow_metricSmooth X o h U P ρ hf (htime i hi t ht).le)
      (hH.2.1 _ (htime i hi t ht))
  have hflow (i : ℕ) (hi : N ≤ i) : LocalRealRicciFlow (g i) Set.univ I 1 :=
    rescaled_local_real_flow X o h U P ρ hf (tw i) (R i) (hR i) Set.univ I (htime i hi)
  obtain ⟨Cn, hCn, hpoint⟩ := scaled_pointwise_bounds n
  have hpointi (i : ℕ) (hi : N ≤ i) (t : ℝ) (ht : t ∈ I) (x : Pt X) :
      (ricci (g i t) x).PosSemidef ∧
      HermLE (ricci (g i t) x) (((scalarCurvature (g i t) x : ℝ) : ℂ) • gMat (g i t) x) ∧
      curvatureJetNorm (g i t) 0 x ≤ Cn * scalarCurvature (g i t) x :=
    hpoint X.manifold (h (tw i + t / R i))
      (localizedFlow_metricSmooth X o h U P ρ hf (htime i hi t ht).le)
      (hf.1.2.2.1 _ (htime i hi t ht).le) (hH.1 _ (htime i hi t ht).le) (R i) (hR i) x
  refine ⟨θ, hθ, N, ?_⟩
  intro r hr
  obtain ⟨A, hA, hAbound⟩ := rescaled_central_scalar_bound X o h U P ρ hf hH θ B r hθ hr hB
  have hscalar (i : ℕ) (hi : N ≤ i) (x : Pt X)
      (hx : x ∈ distBall (g i 0) o (r + 2)) (t : ℝ) (ht : t ∈ I) :
      scalarCurvature (g i t) x ≤ A := by
    apply hAbound (tw i) (R i) (hR i) (hq i hi) (hbase i hi) x
    · simpa only [g, zero_div, add_zero] using hx
    · exact ht
  let D : Set (ℕ × Pt X) := {q | N ≤ q.1 ∧ q.2 ∈ distBall (g q.1 0) o (r + 2)}
  obtain ⟨Λ, hΛ, hcompare⟩ := fixed_domain_metric_comparison
    (fun q : ℕ × Pt X => fun t => gMat (g q.1 t) q.2)
    (fun q : ℕ × Pt X => fun t => ricci (g q.1 t) q.2) D hθ.le hA.le
    (fun q hq t ht => L18Aux.hMat_posDef (g q.1 t) q.2 (chartPt q.2 q.2)
      (mem_extChartAt_target q.2))
    (fun q hq t ht a b => rescaled_gMat_hasDerivAt X o h U P ρ hf
      (tw q.1) (R q.1) (hR q.1) q.2 t (htime q.1 hq.1 t ht) a b)
    (fun q hq t ht => (hpointi q.1 hq.1 t ht q.2).1)
    (fun q hq t ht => HermLE_scalar_upper
      (L18Aux.hMat_posDef (g q.1 t) q.2 (chartPt q.2 q.2) (mem_extChartAt_target q.2)).posSemidef
      (hpointi q.1 hq.1 t ht q.2).2.1 (hscalar q.1 hq.1 q.2 hq.2 t ht))
  let Kcurv := 1 + Cn * A
  have hKcurv : 0 < Kcurv := by dsimp [Kcurv]; positivity
  obtain ⟨b, hb, Kjet, hKjet, hjets⟩ := uniform_current_ball_jets n (dimension_pos X.manifold)
    θ r Kcurv Λ hθ hr hKcurv hΛ
  refine ⟨b, hb, Kjet, hKjet, ?_⟩
  intro i hi hRi p hp z hz
  have hzabs := abs_lt.1 hz
  have hzI : z ∈ I := ⟨by linarith [hzabs.1], by linarith [hzabs.2]⟩
  have hp' : p ∈ distBall (g i 0) o r := by simpa only [g, zero_div, add_zero] using hp
  have hj := hjets X.manifold (g i) o (hflow i hi) (hk i hi) (hc i hi)
    (fun x hx t ht => (hpointi i hi t ht x).2.2 |>.trans
      ((mul_le_mul_of_nonneg_left (hscalar i hi x hx t ht) hCn.le).trans (by dsimp [Kcurv]; linarith)))
    (fun x hx u hu v hv => hcompare (i, x) ⟨hi, hx⟩ u hu v hv) p hp' z hz
  exact ⟨htime i hi z hzI, hs i hi z hzI, hk i hi z hzI, hc i hi z hzI, hj⟩

end Yau.Proofs.C04RescaledTubeAux
