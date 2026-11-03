import Yau.LeafProofs.L22Integral
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section

open scoped Topology ContDiff Convolution
open MeasureTheory Set ContinuousLinearMap

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ}

/-- Local convolution preserves the actual complex-line submean inequality.
The extension is used only where it agrees with the original psh function;
the translated kernel support is explicitly required to stay there. -/
theorem normalized_convolution_psh
    {O V : Set (ComplexVector n)} {f F : ComplexVector n → ℝ}
    (hf : LeafCandidates.ComplexLinePshOn O f) (hFc : Continuous F)
    (hEq : EqOn F f O) (φ : ContDiffBump (0 : ComplexVector n))
    (hVO : ∀ z ∈ V, ∀ a ∈ Metric.closedBall (0 : ComplexVector n) φ.rOut,
      z - a ∈ O) :
    LeafCandidates.ComplexLinePshOn V
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] F) := by
  let B : Set (ComplexVector n) := Metric.closedBall 0 φ.rOut
  let κ : ComplexVector n → ℝ := φ.normed volume
  have hκc : Continuous κ := φ.continuous_normed
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hconv : ContDiff ℝ ∞ (κ ⋆[lsmul ℝ ℝ, volume] F) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hFc.locallyIntegrable
  have heq (z : ComplexVector n) :
      (∫ a in B, κ a * F (z - a)) = (κ ⋆[lsmul ℝ ℝ, volume] F) z := by
    rw [convolution_def]
    change (∫ a in B, κ a * F (z - a)) = ∫ a, κ a * F (z - a)
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    have hnot : a ∉ Function.support κ := by
      rw [φ.support_normed_eq]
      exact fun h => ha (Metric.ball_subset_closedBall h)
    have hzero : κ a = 0 := by simpa only [Function.mem_support, not_not] using hnot
    simp only [hzero, zero_mul]
  have hpsh : LeafCandidates.ComplexLinePshOn V
      (fun z => ∫ a in B, κ a * F (z - a)) := by
    apply complexLinePshOn_integral_ae (volume.restrict B)
      (fun a z => κ a * F (z - a))
    · filter_upwards [ae_restrict_mem hBc.measurableSet] with a ha
      have hs := complexLinePshOn_smul
        (complexLinePshOn_translate hf a (fun z hz => hVO z hz a ha))
        (φ.nonneg_normed (μ := volume) a)
      apply complexLinePshOn_congr hs
      intro z hz
      change κ a * f (z - a) = κ a * F (z - a)
      rw [hEq (hVO z hz a ha)]
    · have hfun : (fun z => ∫ a in B, κ a * F (z - a)) =
          (κ ⋆[lsmul ℝ ℝ, volume] F) := funext heq
      rw [hfun]
      exact hconv.continuous.continuousOn
    · intro z _
      exact (hκc.mul (hFc.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact hBc
    · intro z w _
      rw [Measure.prod_restrict]
      have hc : Continuous (fun p : ComplexVector n × ℝ =>
          κ p.1 * F (z + Complex.exp (p.2 * Complex.I) • w - p.1)) := by
        fun_prop
      exact (hc.continuousOn.integrableOn_compact (hBc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Subset.rfl Ioc_subset_Icc_self)
  exact complexLinePshOn_congr hpsh (fun z _ => heq z)

theorem sub_mem_cthickening {K : Set (ComplexVector n)} {r δ R : ℝ}
    (hsmall : r + δ ≤ R) {z a : ComplexVector n}
    (hz : z ∈ Metric.thickening r K) (ha : a ∈ Metric.closedBall 0 δ) :
    z - a ∈ Metric.cthickening R K := by
  obtain ⟨k, hk, hzk⟩ := Metric.mem_thickening_iff.mp hz
  have ha' : ‖a‖ ≤ δ := by simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  apply Metric.closedBall_subset_cthickening hk R
  change dist (z - a) k ≤ R
  apply le_of_lt
  calc
    dist (z - a) k ≤ dist (z - a) z + dist z k := dist_triangle _ _ _
    _ = ‖a‖ + dist z k := by simp [dist_eq_norm]
    _ ≤ δ + dist z k := add_le_add ha' le_rfl
    _ < R := by linarith

/-- A continuous classical psh function can be approximated near any compact
coordinate subset by a globally smooth function satisfying exactly the same
disc submean predicate. Tietze extension is used only on a compact thickening;
all convolution discs remain in that set. -/
theorem exists_smooth_psh_approx_near_compact
    {O : Set (ComplexVector n)} {f : ComplexVector n → ℝ}
    (hO : IsOpen O) (hf : LeafCandidates.ComplexLinePshOn O f)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ O)
    {a : ℝ} (ha : 0 < a) :
    ∃ (W : Set (ComplexVector n)) (g : ComplexVector n → ℝ),
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧ ContDiff ℝ ∞ g ∧
        LeafCandidates.ComplexLinePshOn W g ∧ ∀ z ∈ W, |g z - f z| < a := by
  obtain ⟨ρ, hρ, hρO⟩ := hK.exists_cthickening_subset_open hO hKO
  let D : Set (ComplexVector n) := Metric.cthickening ρ K
  have hD : IsCompact D := hK.cthickening
  let fc : C(D, ℝ) := ⟨fun z => f z, (hf.1.mono hρO).restrict⟩
  obtain ⟨F, hF⟩ := fc.exists_restrict_eq hD.isClosed
  have hEq : EqOn F f D := by
    intro z hz
    exact congrArg (fun q : C(D, ℝ) => q ⟨z, hz⟩) hF
  have hUF : UniformContinuousOn F D := hD.uniformContinuousOn_of_continuous F.continuous.continuousOn
  obtain ⟨d₀, hd₀, hdist⟩ := Metric.uniformContinuousOn_iff.mp hUF (a / 2) (half_pos ha)
  let d : ℝ := min (ρ / 4) (d₀ / 2)
  have hd : 0 < d := lt_min (by positivity) (half_pos hd₀)
  have hdρ : d ≤ ρ / 4 := min_le_left _ _
  have hdd₀ : d < d₀ := (min_le_right _ _).trans_lt (half_lt_self hd₀)
  let φ : ContDiffBump (0 : ComplexVector n) := ⟨d / 2, d, half_pos hd, half_lt_self hd⟩
  let W : Set (ComplexVector n) := Metric.thickening (ρ / 4) K
  have hWD : W ⊆ D :=
    (Metric.thickening_subset_cthickening _ _).trans
      (Metric.cthickening_mono (by linarith : ρ / 4 ≤ ρ) K)
  have htrans : ∀ z ∈ W, ∀ y ∈ Metric.closedBall (0 : ComplexVector n) φ.rOut,
      z - y ∈ D := by
    intro z hz y hy
    exact sub_mem_cthickening (by dsimp [φ]; linarith : ρ / 4 + φ.rOut ≤ ρ) hz hy
  let g : ComplexVector n → ℝ := φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun z => F z)
  have hgs : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      F.continuous.locallyIntegrable
  refine ⟨W, g, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) K,
    hWD.trans hρO, hgs, ?_, ?_⟩
  · exact normalized_convolution_psh (complexLinePshOn_mono hf hρO) F.continuous hEq φ htrans
  · intro z hz
    have hzD : z ∈ D := hWD hz
    have hbound : ∀ x ∈ Metric.ball z φ.rOut, dist (F x) (F z) ≤ a / 2 := by
      intro x hx
      have hy : z - x ∈ Metric.closedBall (0 : ComplexVector n) φ.rOut := by
        rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm]
        exact (Metric.mem_ball.mp hx).le
      have hxD : x ∈ D := by simpa only [sub_sub_cancel] using htrans z hz (z - x) hy
      exact (hdist x hxD z hzD ((Metric.mem_ball.mp hx).trans hdd₀)).le
    have hb := φ.dist_normed_convolution_le (μ := volume)
      F.continuous.aestronglyMeasurable hbound
    change |g z - f z| < a
    rw [← hEq hzD, ← Real.dist_eq]
    exact hb.trans_lt (half_lt_self ha)

end Yau.LeafProofs.L22Aux
