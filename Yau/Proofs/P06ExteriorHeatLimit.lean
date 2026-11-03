import Yau.Proofs.P06ExteriorHeatDecay
import Yau.Proofs.P06ExteriorHeatCompactPairing

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexOrder Matrix

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03 Davies
variable {n k : ℕ} {M : ComplexManifold n}

/-- Every compact test lies in a fixed positive-radius metric ball. -/
theorem compact_form_support_in_ball (g : SmoothMetric M) (o : M.Carrier)
    (B : RealForm M k) (hcB : CompactlySupportedRealForm B) :
    ∃ r : ℝ, 0 < r ∧ closure {y | B y ≠ 0} ⊆ distBall g.form o r := by
  have hd : Continuous (fun y => inducedDistance g.form o y) :=
    (L12Aux.continuous_inducedDistance g).comp (continuous_const.prodMk continuous_id)
  obtain ⟨c,hc⟩ := hcB.bddAbove_image hd.continuousOn
  refine ⟨max c 0+1,by linarith [le_max_right c 0],?_⟩
  intro y hy
  apply (L12Aux.mem_distBall_iff g o y (show 0 < max c 0+1 by linarith [le_max_right c 0])).mpr
  have hh := hc ⟨y,hy,rfl⟩
  linarith [le_max_left c 0]

/-- Closed initial data leave only one annular exterior error, which vanishes
when the canonical cutoff heats are paired with any compact codifferential. -/
theorem cutoff_heat_exterior_pairing_tendsto_zero
    (g : SmoothMetric M) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (B0 : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B0^2)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (B : RealForm M (k+1)) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun j => inner ℝ
      (hodgeHeatHilbert g μ hμ k t (cutoffVector g μ hμ o χ hχ A hA (j+1) (by omega)))
      (realizeActualForm g μ (codifferentialRealForm g.form B) (codifferentialRealForm_l2 g μ hμ B hB hcB))) atTop (𝓝 0) := by
  obtain ⟨r,hr,hBr⟩ := compact_form_support_in_ball g o B hcB
  let b := realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)
  have hbs : indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) b = b := by
    apply indicator_realize_eq_self
    exact Eventually.of_forall fun y hy => by by_contra h; exact hy (hBr (subset_closure h))
  have htail := (cutoffExteriorVector_local_heat_tendsto_zero g hK hRic μ hμ o χ hχ A hA hclosed B0 hb r t hr ht).mul_const ‖b‖
  simp only [zero_mul] at htail
  have hdec : Tendsto (fun j => inner ℝ
      (hodgeHeatHilbert g μ hμ (k+1) t (cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega))) b) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_) htail
    let v := hodgeHeatHilbert g μ hμ (k+1) t (cutoffExteriorVector g μ hμ o χ hχ A hA (j+1) (by omega))
    have he : inner ℝ v b = inner ℝ
        (indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) v) b := by
      rw [CutoffTail.indicator_symmetric,hbs]
    rw [he]
    exact norm_inner_le_norm _ _
  apply hdec.congr'
  exact Eventually.of_forall fun j => (exteriorGraph_heat_core_pairing g μ hμ _
    (cutoff_multiply_smooth g o χ hχ A hA (j+1) (by omega))
    (cutoff_multiply_compact g o χ hχ A (j+1) (by omega)) B hB hcB t ht.le).symm

/-- Canonical Hilbert representatives and their constructed smooth local limit
are closed. These are internal construction data, not new P06 hypotheses. -/
theorem canonical_cutoff_localSmoothLimit_closed_general
    (g : SmoothMetric M) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (B0 : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B0^2)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hUsL2 : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm g.form μ (Us j t))
    (hrep : ∀ j (hj : 1 ≤ j) t (ht : 0 < t),
      realizeActualForm g μ (Us j t) (hUsL2 j hj t ht) =
        hodgeHeatHilbert g μ hμ 2 t (cutoffVector g μ hμ o χ hχ A hA j hj))
    (hU : ∀ t, 0 < t → SmoothRealForm (U t)) (hlimit : FormHeatLocalSmoothLimit Us U) :
    ∀ t, 0 < t → ClosedRealForm (U t) := by
  intro t ht
  apply closedRealForm_of_codifferential_pairings g μ hμ _ (hU t ht)
  intro B hB hcB
  let C := codifferentialRealForm g.form B
  have hC : SmoothRealForm C := codifferentialRealForm_smooth g μ hμ B hB
  have hcC : CompactlySupportedRealForm C := codifferentialRealForm_compactlySupported g μ hμ B hB hcB
  have hlim := localSmoothLimit_compact_pairing_tendsto g μ hμ Us U hUsL2 hU hlimit C hC hcC t ht
  have hlimshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hzero := cutoff_heat_exterior_pairing_tendsto_zero g hK hRic μ hμ A hA hclosed B0 hb o χ hχ B hB hcB t ht
  have hzero' : Tendsto (fun j => ∫ y, formInner g.form (Us (j+1) t) C y ∂μ) atTop (𝓝 0) := by
    apply hzero.congr'
    exact Eventually.of_forall fun j => by
      dsimp only
      rw [← hrep (j+1) (by omega) t ht,realizeActualForm_inner]
  exact tendsto_nhds_unique hlimshift hzero'

end Yau.NodeProofs.P06Aux.ExteriorHeat
