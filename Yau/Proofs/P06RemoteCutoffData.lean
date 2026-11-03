import Yau.Proofs.P06SmallTimeTail
import Yau.Proofs.P06CutoffTailData

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.RemoteCutoff
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Davies CutoffTail
variable {n k : ℕ}

/-- One fixed cutoff agrees with the original datum around a prescribed
compact set. All later cutoff differences have a uniform Gaussian remote
tail at small time, in the original all-degree Hodge Hilbert space. -/
theorem exists_remote_cutoff_data (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, formNormSq X.metric.form A x ≤ B ^ 2)
    (F : Set (Pt X)) (hF : IsCompact F) :
    ∃ R : ℝ, 0 < R ∧ ∃ J : ℕ, 1 ≤ J ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ a : ℝ, 0 < a ∧
      F ⊆ distBall X.metric.form o R ∧
      (∀ y ∈ distBall X.metric.form o R, cutoffScalar χ J y = 1) ∧
      ∀ l, J ≤ l → ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ s : ℝ, 0 < s → s ≤ 2 * τ →
        ‖indicator X.metric μ F hF.isClosed.measurableSet
          (hodgeHeatHilbert X.metric μ hμ k s
            (cutoffDatum X.metric μ hμ o χ hχ A hA l - cutoffDatum X.metric μ hμ o χ hχ A hA J))‖ ≤
          C * Real.exp (-a / τ) := by
  obtain ⟨r, hr, hFr⟩ := exists_pos_ball_contains_compact X.metric o hF
  obtain ⟨M, hM⟩ := (radius_tendsto.eventually (eventually_ge_atTop (2 * r))).exists
  obtain ⟨J, hJ, hplateau⟩ := cutoffScalar_eventually_one_on_ball X.metric o o χ hχ
    (radius M) (radius_pos M)
  obtain ⟨G, hG, C₀, hC₀, htail⟩ := SmallTimeTail.remote_smallTime_bound (k := k) X μ hμ o r hr
  have hR : 0 < radius M := radius_pos M
  let a : ℝ := radius M ^ 2 / (32 * G ^ 2)
  have ha : 0 < a := div_pos (sq_pos_of_pos (radius_pos M))
    (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
  refine ⟨radius M, radius_pos M, J, hJ, C₀ * B * radius M ^ n, by positivity, a, ha, ?_, ?_, ?_⟩
  · intro x hx
    apply (L12Aux.mem_distBall_iff X.metric o x (radius_pos M)).mpr
    exact ((L12Aux.mem_distBall_iff X.metric o x hr).mp (hFr hx)).trans_le (by linarith)
  · exact hplateau J le_rfl
  · intro l hl τ hτ hτ1 s hs hsτ
    let D : RealForm X.manifold k := cutoffForm χ A l - cutoffForm χ A J
    let hDl := cutoffForm_l2 X.metric μ hμ o χ hχ A hA l
    let hDJ := cutoffForm_l2 X.metric μ hμ o χ hχ A hA J
    let hD := l2RealForm_sub X.metric μ _ _ hDl hDJ
    have hcD : CompactlySupportedRealForm D := compactlySupported_sub _ _
      (cutoffForm_compact X.metric o χ hχ A l) (cutoffForm_compact X.metric o χ hχ A J)
    have hbD : ∀ x, formNormSq X.metric.form D x ≤ B ^ 2 :=
      cutoff_difference_bound X.metric o o χ χ hχ hχ A B hb l J
    have hzero : ballProjection X.metric μ o M (realizeActualForm X.metric μ D hD) = 0 := by
      apply indicator_realize_zero_on X.metric μ _ _ D hD
      intro x hx
      change cutoffScalar χ l x • A x - cutoffScalar χ J x • A x = 0
      rw [hplateau l hl x hx, hplateau J le_rfl x hx, one_smul, sub_self]
    have hdatum : realizeActualForm X.metric μ D hD =
        cutoffDatum X.metric μ hμ o χ hχ A hA l - cutoffDatum X.metric μ hμ o χ hχ A hA J :=
      realizeActualForm_sub X.metric μ _ _ hDl hDJ
    have hnorm := htail M hM B hB τ hτ hτ1 D hD hcD hbD hzero s hs hsτ
    rw [hdatum] at hnorm
    calc
      _ ≤ ‖indicator X.metric μ (distBall X.metric.form o r)
          (L12Aux.measurableSet_distBall X.metric o r)
          (hodgeHeatHilbert X.metric μ hμ k s
            (cutoffDatum X.metric μ hμ o χ hχ A hA l - cutoffDatum X.metric μ hμ o χ hχ A hA J))‖ :=
        indicator_norm_mono X.metric μ F _ hF.isClosed.measurableSet _ hFr _
      _ ≤ _ := by simpa only [a, neg_div, div_div, mul_assoc] using hnorm

end Yau.NodeProofs.P06Aux.RemoteCutoff
