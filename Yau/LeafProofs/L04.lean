import Yau.LeafProofs.L04ContactGeometry
import Yau.LeafProofs.L04CompactLocalization

/-! Jensen's affine contact lemma and compact inf-convolution attainment. -/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal InnerProductSpace

namespace Yau.LeafProofs.L04Aux

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem lipschitzOn_image_volume_zero
    {P : E → E} {s : Set E} {K : ℝ≥0}
    (hP : LipschitzOnWith K P s) (hs : volume s = 0) :
    volume (P '' s) = 0 := by
  let ν : Measure E := hausdorffMeasure (Module.finrank ℝ E : ℝ)
  have hνv : ν ≪ (volume : Measure E) :=
    Measure.absolutelyContinuous_isAddHaarMeasure ν volume
  have hvν : (volume : Measure E) ≪ ν :=
    Measure.absolutelyContinuous_isAddHaarMeasure volume ν
  have hνs : ν s = 0 := hνv hs
  apply hvν
  have h := hP.hausdorffMeasure_image_le
    (show 0 ≤ (Module.finrank ℝ E : ℝ) by positivity)
  change ν (P '' s) ≤
    (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * ν s at h
  simpa only [hνs, mul_zero, nonpos_iff_eq_zero] using h

end Yau.LeafProofs.L04Aux

namespace Yau.LeafProofs

theorem jensen : Yau.LeafCandidates.Jensen := by
  intro m φ lam xh r O hr hO hxh hD hball hsemi hgap
  let D := closure O
  let U := Metric.ball xh (2 * r)
  have hDU : D ⊆ U :=
    hball.trans (Metric.ball_subset_ball (by linarith))
  have hg : ContinuousOn
      (fun x => -φ x + lam / 2 * ‖x‖ ^ 2) U :=
    hsemi.continuousOn Metric.isOpen_ball
  have hquad : ContinuousOn (fun x : Yau.LeafCandidates.RV m =>
      lam / 2 * ‖x‖ ^ 2) U := by fun_prop
  have hφU : ContinuousOn φ U := by
    convert hquad.sub hg using 1
    ext x
    change φ x = lam / 2 * ‖x‖ ^ 2 - (-φ x + lam / 2 * ‖x‖ ^ 2)
    ring
  have hφD : ContinuousOn φ D := hφU.mono hDU
  obtain ⟨δ₀, hδ₀, ρ, hρ, K, hK, hKO, hbuf, hcore⟩ :=
    L04Aux.boundaryGap_compact_core φ xh r O hr hO hxh hD hball hφD hgap
  let C : ℝ := max lam 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hlam : lam ≤ C := le_max_left _ _
  let L : ℝ := 2 * C + 2 * δ₀ / ρ
  have hL : 0 ≤ L := by positivity
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  let S : Set (Yau.LeafCandidates.RV m) :=
    {x | x ∈ O ∧ ∃ p, ‖p‖ ≤ δ ∧
      ∀ y ∈ D, φ x - ⟪p, x⟫_ℝ ≤ φ y - ⟪p, y⟫_ℝ}
  classical
  let P : Yau.LeafCandidates.RV m → Yau.LeafCandidates.RV m :=
    fun x => if hx : x ∈ S then Classical.choose hx.2 else 0
  have hPspec : ∀ x ∈ S, ‖P x‖ ≤ δ ∧
      L04Aux.AffineMinOn φ D x (P x) := by
    intro x hx
    simpa only [P, dite_eq_left hx, L04Aux.AffineMinOn] using Classical.choose_spec hx.2
  have hSK : S ⊆ K := by
    intro x hx
    exact hcore x (P x) (subset_closure hx.1) ((hPspec x hx).1.trans hδle)
      (hPspec x hx).2
  have hLip : LipschitzOnWith ⟨L, hL⟩ P S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change ‖P x - P y‖ ≤ L * ‖x - y‖
    rw [← norm_sub_rev y x]
    by_cases hxy : ‖y - x‖ ≤ ρ
    · have hnear := L04Aux.affineMin_slope_local_bound hsemi hDU hlam hC hρ
        ((hbuf x (hSK hx)).trans subset_closure)
        ((hbuf y (hSK hy)).trans subset_closure)
        (hPspec x hx).2 (hPspec y hy).2 hxy
      apply hnear.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [L]
      exact le_add_of_nonneg_right (by positivity)
    · have hfar : ρ ≤ ‖y - x‖ := le_of_lt (lt_of_not_ge hxy)
      have hnorm : ‖P x - P y‖ ≤ 2 * δ₀ := by
        have hxnorm := (hPspec x hx).1.trans hδle
        have hynorm := (hPspec y hy).1.trans hδle
        exact (norm_sub_le _ _).trans (by linarith)
      have hratio : 2 * δ₀ ≤ (2 * δ₀ / ρ) * ‖y - x‖ := by
        have hmul := mul_le_mul_of_nonneg_left hfar
          (show 0 ≤ 2 * δ₀ / ρ by positivity)
        have heq : (2 * δ₀ / ρ) * ρ = 2 * δ₀ := div_mul_cancel₀ _ hρ.ne'
        simpa only [heq] using hmul
      apply hnorm.trans (hratio.trans _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [L]
      linarith
  have hcover : Metric.closedBall (0 : Yau.LeafCandidates.RV m) δ ⊆ P '' S := by
    intro p hp
    have hpnorm : ‖p‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hp
    have hcost : ContinuousOn (fun x => φ x - ⟪p, x⟫_ℝ) D :=
      hφD.sub (continuous_const.inner continuous_id).continuousOn
    obtain ⟨x, hxD, hxMin⟩ := hD.exists_isMinOn
      ⟨xh, subset_closure hxh⟩ hcost
    have hxK : x ∈ K := hcore x p hxD (hpnorm.trans hδle) (fun z hz => hxMin hz)
    have hxS : x ∈ S := ⟨hKO hxK, p, hpnorm, fun z hz => hxMin hz⟩
    refine ⟨x, hxS, ?_⟩
    exact L04Aux.affineMin_slope_unique hsemi hDU hlam hC hρ
      ((hbuf x hxK).trans subset_closure) (hPspec x hxS).2 (fun z hz => hxMin hz)
  change 0 < volume S
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hnull : volume (P '' S) = 0 :=
    L04Aux.lipschitzOn_image_volume_zero hLip hzero
  have hballzero : volume (Metric.ball (0 : Yau.LeafCandidates.RV m) δ) = 0 :=
    measure_mono_null (Metric.ball_subset_closedBall.trans hcover) hnull
  exact (Metric.measure_ball_pos (volume : Measure (Yau.LeafCandidates.RV m)) 0 hδ).ne'
    hballzero

theorem L04 : Yau.LeafObligations.L04 :=
  ⟨jensen, infConvolutionAttainment⟩

end Yau.LeafProofs
