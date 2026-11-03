import Yau.Proofs.P06HodgeDaviesIMS
import Yau.Proofs.P06HodgeSpectral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Davies
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Davies' bound for every actual form degree and every smooth bounded
multiplier with a relative physical-gradient bound. The heat operator has
exactly the original generator `-□/2`. -/
theorem heat_multiplier_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (B : ℝ) (hB : 0 ≤ B)
    (hηb : ∀ x, |η x| ≤ B) (ell : ℝ)
    (hrel : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ ell ^ 2 * η x ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : L2FormHilbert g μ k) :
    let P := multiplyL2FormHilbert (k := k) g μ η
      (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable B hB hηb;
    ‖P (hodgeHeatHilbert g μ hμ k t f)‖ ≤ Real.exp (ell ^ 2 * t / 2) * ‖P f‖ := by
  let hm := (L18Aux.continuous_of_smoothFn hη).aestronglyMeasurable (μ := μ)
  let P := multiplyL2FormHilbert (k := k) g μ η hm B hB hηb
  let u := fun s => hodgeHeatHilbert g μ hμ k s f
  let F := fun s => ‖P (u s)‖ ^ 2
  let G := fun s => Real.exp (-ell ^ 2 * s) * F s
  have hF {s : ℝ} (hs : 0 < s) :
      ∃ z, HasDerivAt F z s ∧ z ≤ ell ^ 2 * F s := by
    obtain ⟨w, hw, hg⟩ := hodgeHeatHilbert_strongPath g μ hμ k f s hs
    have hd := (P.hasFDerivAt.comp_hasDerivAt s hw).norm_sq
    refine ⟨2 * inner ℝ (P (u s)) (P w), hd, ?_⟩
    have hl := graph_multiplier_lower g μ hμ η hη B hB hηb ell hrel
      (u s) ((-2 : ℝ) • w) hg
    change -(ell ^ 2) * F s ≤ inner ℝ ((-2 : ℝ) • w) (P (P (u s))) at hl
    have hi : inner ℝ w (P (P (u s))) = inner ℝ (P (u s)) (P w) := by
      rw [← multiplyL2FormHilbert_inner_symm g μ η hm B hB hηb]
      exact real_inner_comm _ _
    rw [inner_smul_left, hi] at hl
    simp only [conj_trivial] at hl
    linarith
  have hG {s : ℝ} (hs : 0 < s) : ∃ z, HasDerivAt G z s ∧ z ≤ 0 := by
    obtain ⟨z, hz, hb⟩ := hF hs
    have hd := (((hasDerivAt_id s).const_mul (-ell ^ 2)).exp).mul hz
    simp only [id_eq, mul_one] at hd
    refine ⟨Real.exp (-ell ^ 2 * s) * (-ell ^ 2 * F s + z), ?_, ?_⟩
    · convert hd using 1 <;> ring
    · exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hanti : AntitoneOn G (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · intro s hs
      obtain ⟨z, hz, _⟩ := hG hs
      exact hz.continuousAt.continuousWithinAt
    · intro s hs
      obtain ⟨z, hz, _⟩ := hG (interior_subset hs)
      exact hz.differentiableAt.differentiableWithinAt
    · intro s hs
      obtain ⟨z, hz, hb⟩ := hG (interior_subset hs)
      rwa [hz.deriv]
  have hzero : Tendsto G (𝓝[≥] (0 : ℝ)) (𝓝 (‖P f‖ ^ 2)) := by
    have hu := P.continuous.tendsto f |>.comp (hodgeHeatHilbert_tendsto_zero g μ hμ k f)
    have he : Tendsto (fun s : ℝ => Real.exp (-ell ^ 2 * s)) (𝓝[≥] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => Real.exp (-ell ^ 2 * s)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [G, F, u, Function.comp_def, one_mul] using he.mul (hu.norm.pow 2)
  rcases eq_or_lt_of_le ht with ht0 | htp
  · subst t
    simp only [hodgeHeatHilbert_zero, one_apply_eq_self, mul_zero, zero_div,
      Real.exp_zero, one_mul, le_refl]
  · have hz : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (‖P f‖ ^ 2)) :=
      hzero.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have hGt : G t ≤ ‖P f‖ ^ 2 := by
      apply ge_of_tendsto hz
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds htp).filter_mono nhdsWithin_le_nhds] with s hs hst
      exact hanti hs htp hst.le
    have hsq : ‖P (u t)‖ ^ 2 ≤ Real.exp (ell ^ 2 * t) * ‖P f‖ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hGt (Real.exp_pos (ell ^ 2 * t)).le
      have he : Real.exp (ell ^ 2 * t) * Real.exp (-ell ^ 2 * t) = 1 := by
        rw [← Real.exp_add]
        have hh : ell ^ 2 * t + -ell ^ 2 * t = 0 := by ring
        rw [hh, Real.exp_zero]
      dsimp only [G, F] at hm
      simpa only [← mul_assoc, he, one_mul] using hm
    have hexp : Real.exp (ell ^ 2 * t / 2) ^ 2 = Real.exp (ell ^ 2 * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    change ‖P (u t)‖ ≤ Real.exp (ell ^ 2 * t / 2) * ‖P f‖
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
    simpa only [mul_pow, hexp] using hsq

/-- The actual bounded exponential multiplier. Only an upper bound for
its smooth exponent is needed. -/
def expMultiplier (g : SmoothMetric M) (μ : Measure M.Carrier)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (b : ℝ) (hb : ∀ x, ψ x ≤ b) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  multiplyL2FormHilbert g μ (fun x => Real.exp (ψ x))
    (L18Aux.continuous_of_smoothFn
      (L18Aux.smoothFn_scalar_comp hψ Real.exp Real.contDiff_exp)).aestronglyMeasurable
    (Real.exp b) (Real.exp_pos _).le (fun x => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hb x))

/-- The sharp exponential weighted estimate for the original Hodge heat,
with no curvature, positivity, or additional source premise. -/
theorem heat_weighted_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (b : ℝ) (hb : ∀ x, ψ x ≤ b)
    (ell : ℝ) (hgrad : ∀ x, L18Aux.scalarGradientPair g.form ψ ψ x ≤ ell ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : L2FormHilbert g μ k) :
    ‖expMultiplier g μ ψ hψ b hb (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (ell ^ 2 * t / 2) * ‖expMultiplier g μ ψ hψ b hb f‖ := by
  apply heat_multiplier_norm_le g μ hμ _
    (L18Aux.smoothFn_scalar_comp hψ Real.exp Real.contDiff_exp)
    (Real.exp b) (Real.exp_pos _).le
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (hb x)) ell
    (fun x => ?_) t ht f
  rw [L18Aux.scalarGradientPair_scalar_comp_self g.form hψ Real.exp x
    (Real.hasDerivAt_exp (ψ x)).differentiableAt, Real.deriv_exp]
  nlinarith [mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg (Real.exp (ψ x)))]


/-- Explicit real-parameter version: a gradient bound `L²` for `ψ`
produces the uniform factor `exp(a² L² t / 2)`. -/
theorem heat_scaled_weighted_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (a b : ℝ)
    (hb : ∀ x, a * ψ x ≤ b) (L : ℝ)
    (hgrad : ∀ x, L18Aux.scalarGradientPair g.form ψ ψ x ≤ L ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : L2FormHilbert g μ k) :
    let hscaled : SmoothFn (fun x => a * ψ x) := fun x => contDiffOn_const.mul (hψ x);
    ‖expMultiplier g μ (fun x => a * ψ x) hscaled b hb
        (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (a ^ 2 * L ^ 2 * t / 2) *
        ‖expMultiplier g μ (fun x => a * ψ x) hscaled b hb f‖ := by
  let hscaled : SmoothFn (fun x => a * ψ x) := fun x => contDiffOn_const.mul (hψ x)
  have hscaledgrad (x : M.Carrier) :
      L18Aux.scalarGradientPair g.form (fun x => a * ψ x) (fun x => a * ψ x) x ≤
        (a * L) ^ 2 := by
    have hd : HasDerivAt (fun q : ℝ => a * q) a (ψ x) := by
      simpa using (hasDerivAt_id (ψ x)).const_mul a
    rw [L18Aux.scalarGradientPair_scalar_comp_self g.form hψ
      (fun q : ℝ => a * q) x hd.differentiableAt, hd.deriv]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg a)
  simpa only [mul_pow] using heat_weighted_L2 g μ hμ (fun x => a * ψ x)
    hscaled b hb (a * L) hscaledgrad t ht f


/-- Bounded multiplication by `exp(a ψ)` on actual form L². -/
def scaledExpMultiplier (g : SmoothMetric M) (μ : Measure M.Carrier)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (a B : ℝ)
    (hψb : ∀ x, |ψ x| ≤ B) : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  expMultiplier g μ (fun x => a * ψ x) (fun x => contDiffOn_const.mul (hψ x))
    (|a| * B) (fun x => (le_abs_self (a * ψ x)).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hψb x) (abs_nonneg a)))

/-- For every bounded smooth `ψ`, the original Hodge heat satisfies
`‖exp(aψ) S_t f‖ ≤ exp(a²L²t/2) ‖exp(aψ) f‖` in every degree. -/
theorem heat_bounded_scaled_weighted_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (ψ : M.Carrier → ℝ) (hψ : SmoothFn ψ) (a B : ℝ)
    (hψb : ∀ x, |ψ x| ≤ B) (L : ℝ)
    (hgrad : ∀ x, L18Aux.scalarGradientPair g.form ψ ψ x ≤ L ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : L2FormHilbert g μ k) :
    ‖scaledExpMultiplier g μ ψ hψ a B hψb (hodgeHeatHilbert g μ hμ k t f)‖ ≤
      Real.exp (a ^ 2 * L ^ 2 * t / 2) * ‖scaledExpMultiplier g μ ψ hψ a B hψb f‖ := by
  exact heat_scaled_weighted_L2 g μ hμ ψ hψ a (|a| * B)
    (fun x => (le_abs_self (a * ψ x)).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hψb x) (abs_nonneg a))) L hgrad t ht f

end Yau.NodeProofs.P06Aux.Davies
