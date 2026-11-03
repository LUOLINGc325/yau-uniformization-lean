import Yau.Proofs.P06CutoffTailData
import Yau.Proofs.P06ScalarUniquenessRicciPositive

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder

namespace Yau.NodeProofs.P06Aux.CutoffTail
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Two completely arbitrary original cutoff families applied to the same
bounded smooth form have a common localized heat limit, uniformly down to
initial time on every finite time slab. -/
theorem localizedCauchy_of_nonnegativeRicci
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o o' : M.Carrier) (χ χ' : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) (hχ' : MetricCutoffFamily g.form o' χ')
    (A : RealForm M k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B ^ 2)
    (K : Set M.Carrier) (hcK : IsCompact K)
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j l, N ≤ j → N ≤ l → ∀ t, 0 < t → t ≤ T →
      ‖indicator g μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert g μ hμ k t (cutoffDatum g μ hμ o χ hχ A hA j) -
          hodgeHeatHilbert g μ hμ k t (cutoffDatum g μ hμ o' χ' hχ' A hA l))‖ < ε := by
  obtain ⟨r, hr, hKr⟩ := exists_pos_ball_contains_compact g o hcK
  obtain ⟨J, hJ⟩ := exists_uniform_local_tail (k := k) g hK hRic μ hμ o r T |B| hr hT
    (abs_nonneg B) ε hε
  obtain ⟨N₁, hN₁, hone⟩ := cutoffScalar_eventually_one_on_ball g o o χ hχ
    (radius J) (radius_pos J)
  obtain ⟨N₂, hN₂, hone'⟩ := cutoffScalar_eventually_one_on_ball g o' o χ' hχ'
    (radius J) (radius_pos J)
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro j l hj hl t ht htT
  let D := cutoffForm χ A j - cutoffForm χ' A l
  have hD : L2RealForm g.form μ D := l2RealForm_sub g μ _ _
    (cutoffForm_l2 g μ hμ o χ hχ A hA j) (cutoffForm_l2 g μ hμ o' χ' hχ' A hA l)
  have hcD : CompactlySupportedRealForm D := compactlySupported_sub _ _
    (cutoffForm_compact g o χ hχ A j) (cutoffForm_compact g o' χ' hχ' A l)
  have hbD : ∀ x, formNormSq g.form D x ≤ |B| ^ 2 := by
    intro x
    simpa only [sq_abs] using cutoff_difference_bound g o o' χ χ' hχ hχ' A B hb j l x
  have hz : ballProjection g μ o J (realizeActualForm g μ D hD) = 0 := by
    apply indicator_realize_zero_on g μ _ _ D hD
    intro x hx
    have h₁ := hone j ((le_max_left N₁ N₂).trans hj) x hx
    have h₂ := hone' l ((le_max_right N₁ N₂).trans hl) x hx
    change cutoffScalar χ j x • A x - cutoffScalar χ' l x • A x = 0
    rw [h₁, h₂, sub_self]
  have htD := hJ D hD hcD hbD hz t ht htT
  have he : realizeActualForm g μ D hD =
      cutoffDatum g μ hμ o χ hχ A hA j - cutoffDatum g μ hμ o' χ' hχ' A hA l :=
    realizeActualForm_sub g μ _ _ _ _
  calc
    _ = ‖indicator g μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ D hD))‖ := by simp only [he, map_sub]
    _ ≤ ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ D hD))‖ :=
      indicator_norm_mono g μ _ _ _ _ hKr _
    _ < ε := htD

/-- Original-manifold endpoint: Ricci nonnegativity is proved from the
original geometry, and is not an extra assumption on P06. -/
theorem localizedCauchy (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o o' : Pt X) (χ χ' : ℕ → Pt X → ℝ)
    (hχ : MetricCutoffFamily X.metric.form o χ)
    (hχ' : MetricCutoffFamily X.metric.form o' χ')
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B ^ 2)
    (K : Set (Pt X)) (hcK : IsCompact K)
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j l, N ≤ j → N ≤ l → ∀ t, 0 < t → t ≤ T →
      ‖indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j) -
          hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o' χ' hχ' A hA l))‖ < ε :=
  localizedCauchy_of_nonnegativeRicci X.metric X.kahler_metric
    (kahlerManifold_ricci_posSemidef X) μ hμ o o' χ χ' hχ hχ' A hA B hb K hcK T hT ε hε

/-- In particular every original family is Cauchy in the localized
Hilbert space at each positive time, in arbitrary form degree. -/
theorem localized_cauchySeq (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B ^ 2)
    (K : Set (Pt X)) (hcK : IsCompact K) (t : ℝ) (ht : 0 < t) :
    CauchySeq (fun j => indicator X.metric μ K hcK.isClosed.measurableSet
      (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j))) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN, htail⟩ := localizedCauchy X μ hμ o o χ χ hχ hχ A hA B hb K hcK t ht ε hε
  refine ⟨N, fun j hj l hl => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  exact htail j l hj hl t ht le_rfl

/-- Completeness now supplies the actual localized Hilbert limit.  No
regularity or weak PDE assertion is used in this passage to the limit. -/
theorem exists_localized_limit (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B ^ 2)
    (K : Set (Pt X)) (hcK : IsCompact K) (t : ℝ) (ht : 0 < t) :
    ∃ u : L2FormHilbert X.metric μ k,
      Tendsto (fun j => indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j)))
        atTop (𝓝 u) :=
  cauchySeq_tendsto_of_complete (localized_cauchySeq X μ hμ o χ hχ A hA B hb K hcK t ht)

/-- The localized limit is independent of the admissible cutoff family
and its basepoint. -/
theorem exists_common_localized_limit (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o o' : Pt X) (χ χ' : ℕ → Pt X → ℝ)
    (hχ : MetricCutoffFamily X.metric.form o χ)
    (hχ' : MetricCutoffFamily X.metric.form o' χ')
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B ^ 2)
    (K : Set (Pt X)) (hcK : IsCompact K) (t : ℝ) (ht : 0 < t) :
    ∃ u : L2FormHilbert X.metric μ k,
      Tendsto (fun j => indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j)))
        atTop (𝓝 u) ∧
      Tendsto (fun j => indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o' χ' hχ' A hA j)))
        atTop (𝓝 u) := by
  obtain ⟨u, hu⟩ := exists_localized_limit X μ hμ o χ hχ A hA B hb K hcK t ht
  refine ⟨u, hu, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂, hmix⟩ := localizedCauchy X μ hμ o' o χ' χ hχ' hχ A hA B hb
    K hcK t ht (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  have hfirst := hN₁ j ((le_max_left N₁ N₂).trans hj)
  have hsecond := hmix j j ((le_max_right N₁ N₂).trans hj)
    ((le_max_right N₁ N₂).trans hj) t ht le_rfl
  have htri := dist_triangle
    (indicator X.metric μ K hcK.isClosed.measurableSet
      (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o' χ' hχ' A hA j)))
    (indicator X.metric μ K hcK.isClosed.measurableSet
      (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j))) u
  have hd : dist
      (indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o' χ' hχ' A hA j)))
      (indicator X.metric μ K hcK.isClosed.measurableSet
        (hodgeHeatHilbert X.metric μ hμ k t (cutoffDatum X.metric μ hμ o χ hχ A hA j))) < ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    exact hsecond
  linarith

end Yau.NodeProofs.P06Aux.CutoffTail
