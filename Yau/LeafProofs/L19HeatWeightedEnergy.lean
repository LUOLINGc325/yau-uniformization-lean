import Yau.LeafProofs.L19HeatWeightedEnergyForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The Davies weighted estimate for the constructed scalar heat family. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A genuine smooth multiplier with a relative physical gradient bound
obeys the weighted heat estimate. Every operator here is constructed from
actual scalar multiplication and the fixed spectral heat family. -/
theorem scalarHeatFamily_multiplier_norm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier → ℝ) (ha : SmoothFn a) (B C : ℝ)
    (hB : ∀ x, |a x| ≤ B) (hC : ∀ x, scalarGradientPair g.form a a x ≤ C ^ 2)
    (ell : ℝ) (hrel : ∀ x, scalarGradientPair g.form a a x ≤ ell ^ 2 * a x ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ‖scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
        (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (ell ^ 2 * t / 2) *
        ‖scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB f‖ := by
  let A := scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
  let T := scalarEnergyMultiplier g μ hμ a ha B C hB hC
  let u := fun s => scalarHeatFamily g μ hμ s f
  let W := fun s => scalarHeatEnergy g μ hμ s f
  let F := fun s => ‖A (u s)‖ ^ 2
  let G := fun s => Real.exp (-ell ^ 2 * s) * F s
  have htest {s : ℝ} (hs : 0 < s) :
      scalarEnergyL2 g μ hμ (T (T (W s))) = A (A (u s)) := by
    dsimp only [T, A, W, u]
    rw [scalarEnergyMultiplier_L2, scalarEnergyMultiplier_L2, scalarHeatEnergy_L2 g μ hμ hs]
  have hF {s : ℝ} (hs : 0 < s) :
      HasDerivAt F (-2 * scalarClosedEnergy g μ hμ (W s) (T (T (W s)))) s := by
    have hu := scalarHeatFamily_apply_hasDerivAt g μ hμ hs f
    have hd := (A.hasFDerivAt.comp_hasDerivAt s hu).norm_sq
    have hw := scalarHeatFamily_weak_equation g μ hμ hs f (T (T (W s)))
    rw [hu.deriv, htest hs] at hw
    have hi : ⟪A (u s), A (scalarHeatFamily g μ hμ s f - scalarHeatInverse g μ hμ s f)⟫_ℝ =
        ⟪scalarHeatFamily g μ hμ s f - scalarHeatInverse g μ hμ s f, A (A (u s))⟫_ℝ := by
      rw [real_inner_comm, scalarMultiplierL2_inner_square]
    change HasDerivAt F (2 * ⟪A (u s),
      A (scalarHeatFamily g μ hμ s f - scalarHeatInverse g μ hμ s f)⟫_ℝ) s at hd
    rw [hi] at hd
    convert hd using 1
    linarith only [hw]
  have hbound {s : ℝ} (hs : 0 < s) :
      -2 * scalarClosedEnergy g μ hμ (W s) (T (T (W s))) ≤ ell ^ 2 * F s := by
    have he := scalarClosedEnergy_multiplier_lower g μ hμ a ha B C hB hC ell hrel (W s)
    change -(ell ^ 2 / 2) * ‖A (scalarEnergyL2 g μ hμ (W s))‖ ^ 2 ≤
      scalarClosedEnergy g μ hμ (W s) (T (T (W s))) at he
    have hw : scalarEnergyL2 g μ hμ (W s) = u s := scalarHeatEnergy_L2 g μ hμ hs f
    rw [hw] at he
    change _ ≤ ell ^ 2 * ‖A (u s)‖ ^ 2
    linarith only [he]
  have hG {s : ℝ} (hs : 0 < s) : HasDerivAt G
      (Real.exp (-ell ^ 2 * s) *
        (-ell ^ 2 * F s - 2 * scalarClosedEnergy g μ hμ (W s) (T (T (W s))))) s := by
    have hd := (((hasDerivAt_id s).const_mul (-ell ^ 2)).exp).mul (hF hs)
    simp only [id_eq, mul_one] at hd
    change HasDerivAt G
      (Real.exp (-ell ^ 2 * s) * (-ell ^ 2) * F s +
        Real.exp (-ell ^ 2 * s) * (-2 * scalarClosedEnergy g μ hμ (W s) (T (T (W s))))) s at hd
    convert hd using 1
    ring
  have hanti : AntitoneOn G (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    · intro s hs
      exact (hG hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hG ((interior_subset hs) : 0 < s)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hsp : 0 < s := interior_subset hs
      rw [(hG hsp).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      linarith only [hbound hsp]
  have hzero : Tendsto G (𝓝[≥] (0 : ℝ)) (𝓝 (‖A f‖ ^ 2)) := by
    have hu := A.continuous.tendsto f |>.comp (scalarHeatFamily_tendsto_zero g μ hμ f)
    have he : Tendsto (fun s : ℝ => Real.exp (-ell ^ 2 * s)) (𝓝[≥] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => Real.exp (-ell ^ 2 * s)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [G, F, u, Function.comp_def, one_mul] using he.mul (hu.norm.pow 2)
  rcases eq_or_lt_of_le ht with ht0 | htp
  · subst t
    simp only [scalarHeatFamily_zero, one_apply_eq_self, mul_zero, zero_div, Real.exp_zero, one_mul, le_refl]
  · have hz : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (‖A f‖ ^ 2)) :=
      hzero.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have hGt : G t ≤ ‖A f‖ ^ 2 := by
      apply ge_of_tendsto hz
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds htp).filter_mono nhdsWithin_le_nhds]
        with s hs hst
      exact hanti hs htp hst.le
    have hsq : ‖A (u t)‖ ^ 2 ≤ Real.exp (ell ^ 2 * t) * ‖A f‖ ^ 2 := by
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
    change ‖A (u t)‖ ≤ Real.exp (ell ^ 2 * t / 2) * ‖A f‖
    have hh : (Real.exp (ell ^ 2 * t / 2) * ‖A f‖) ^ 2 =
        Real.exp (ell ^ 2 * t) * ‖A f‖ ^ 2 := by rw [mul_pow, hexp]
    nlinarith [norm_nonneg (A (u t)), norm_nonneg (A f),
      mul_nonneg (Real.exp_pos (ell ^ 2 * t / 2)).le (norm_nonneg (A f))]

end Yau.LeafProofs.L19Aux
