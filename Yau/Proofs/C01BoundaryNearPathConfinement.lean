import Yau.Proofs.C01SmoothSegmentLength
import Yau.Proofs.C01CompactNormCoercivity

/-! Near-minimizers to a genuine boundary-distance minimizing point
stay in a larger original compact ball. An excursion must pay both the
first-exit minimum and a positive annular crossing cost. -/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_boundary_nearPath_confinement
    (hflow : LocalizedFlow X o h U P ρ) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) (y : Pt X) (hy : y ∈ initialDistanceSphere X.metric o L)
    (hmin : inducedDistance (h a) o y = exitDistanceProfile X.metric (h a) o L) :
    letI := manifold_realSmooth X.manifold
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : ℝ → Pt X)
      (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f),
      f 0 = o → f 1 = y →
      curveLength (h a) (piecewiseC1Curve_of_contMDiff hf) < inducedDistance (h a) o y + δ →
      Set.MapsTo f (Set.Icc (0 : ℝ) 1) {x | inducedDistance X.metric.form o x ≤ L + 1} := by
  letI := manifold_realSmooth X.manifold
  let k := h a
  have hk : MetricSmooth k := localizedFlow_metricSmooth_nonneg hflow a ha
  let K : Set (Pt X) := {x | inducedDistance X.metric.form o x ≤ L + 1}
  obtain ⟨ell, hell, hb⟩ := localizedFlow_compact_speed_lower_bound hflow a ha K
    (isCompact_inducedDistance_sublevel X.metric o (L + 1))
  refine ⟨ell / 2, half_pos hell, ?_⟩
  intro f hf hf₀ _hf₁ hlen s hs
  by_contra hescape
  have hfar : L + 1 < inducedDistance X.metric.form o (f s) := lt_of_not_ge hescape
  have hc : Continuous (fun t => inducedDistance X.metric.form o (f t)) :=
    ((Yau.LeafProofs.L12Aux.continuous_inducedDistance X.metric).comp
      (continuous_const.prodMk continuous_id)).comp hf.continuous
  obtain ⟨v, hv, hhitv, hinside⟩ := exists_first_exit_level hs.1 hc.continuousOn
    (by simpa only [hf₀, X.metric.induced_distance_eq_zero.mpr rfl] using (show 0 < L + 1 by linarith)) hfar.le
  obtain ⟨u, hu, hhitu, _⟩ := exists_first_exit_level hv.1.le hc.continuousOn
    (by simpa only [hf₀, X.metric.induced_distance_eq_zero.mpr rfl] using hL)
    (by rw [hhitv]; linarith)
  have hhit : f u ∈ initialDistanceSphere X.metric o L := hhitu
  have hprefix := exit_profile_le_actualPathELength_at_hit X.metric k hk o L hL.le f hf hf₀ u hu.1.le hhit
  have hdist : 1 ≤ inducedDistance X.metric.form (f u) (f v) := by
    have htri := X.metric.induced_distance_triangle o (f u) (f v)
    rw [hhitu, hhitv] at htri
    linarith
  have hreal : ENNReal.ofReal (1 : ℝ) ≤ actualPathELength X.metric.form f u v :=
    (ENNReal.ofReal_le_ofReal hdist).trans
      (distance_le_smooth_segment_length X.metric.form (metricSmooth_of_smoothMetric X.metric) f hf u v hu.2)
  have himage : Set.MapsTo f (Set.Icc u v) K := by
    intro t ht
    exact hinside t ⟨hu.1.le.trans ht.1, ht.2⟩
  have hsegment : ENNReal.ofReal ell ≤ actualPathELength k f u v := by
    have H := (mul_le_mul_of_nonneg_left hreal (show 0 ≤ ENNReal.ofReal ell from zero_le)).trans
      (actualPathELength_lower_of_speedSq_lower X.metric.form k K ell hell.le hb f himage)
    simpa only [ENNReal.ofReal_one, mul_one] using H
  have hwhole : ENNReal.ofReal (exitDistanceProfile X.metric k o L + ell) ≤
      ENNReal.ofReal (curveLength k (piecewiseC1Curve_of_contMDiff hf)) := by
    rw [ENNReal.ofReal_add (exitDistanceProfile_pos X.metric k hk o L hL).le hell.le]
    calc
      _ ≤ actualPathELength k f 0 u + actualPathELength k f u v := add_le_add hprefix hsegment
      _ = actualPathELength k f 0 v := actualPathELength_add k f hu.1.le hu.2
      _ ≤ actualPathELength k f 0 1 := actualPathELength_mono k f le_rfl (hv.2.trans hs.2)
      _ = _ := actualPathELength_full_of_contMDiff k hk f hf
  have hbound := (ENNReal.ofReal_le_ofReal_iff
    (curveLength_nonneg k (piecewiseC1Curve_of_contMDiff hf))).mp hwhole
  rw [hmin] at hlen
  change curveLength k (piecewiseC1Curve_of_contMDiff hf) < exitDistanceProfile X.metric k o L + ell / 2 at hlen
  linarith

end Yau.NodeProofs.C01Aux
