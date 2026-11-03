import Yau.LeafProofs.L19HeatRegularityLocalEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Dominated scalar L² convergence and differentiation for actual test paths. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A dominated convergence theorem in the actual scalar L² quotient,
with explicit measurable representative equalities. -/
theorem scalarL2_tendsto_of_dominated {l : Filter ι} [l.IsCountablyGenerated]
    (v : ι → Lp ℝ 2 μ) {g : ι → α → ℝ} {w b : α → ℝ}
    (hcoe : ∀ i, v i =ᵐ[μ] g i) (hw : MemLp w 2 μ) (hb : MemLp b 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖g i x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (w x))) :
    Tendsto v l (𝓝 (hw.toLp w)) := by
  let W := hw.toLp w
  let B := fun x => (‖b x‖ + ‖w x‖)^2
  have hB : Integrable B μ :=
    (memLp_two_iff_integrable_sq (hb.norm.add hw.norm).aestronglyMeasurable).mp (hb.norm.add hw.norm)
  have hmeas (i) : AEStronglyMeasurable (fun x => (g i x - w x)^2) μ :=
    (((Lp.memLp (v i)).ae_eq (hcoe i)).aestronglyMeasurable.sub hw.aestronglyMeasurable).pow 2
  have hdom : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖(g i x - w x)^2‖ ≤ B x := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    have hh := (norm_sub_le (g i x) (w x)).trans
      (add_le_add (hx.trans (le_abs_self _)) le_rfl)
    change ‖(g i x - w x)^2‖ ≤ (‖b x‖ + ‖w x‖)^2
    rw [norm_pow]
    change ‖g i x - w x‖ ≤ ‖b x‖ + ‖w x‖ at hh
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hh
  have hzero : ∀ᵐ x ∂μ, Tendsto (fun i => (g i x - w x)^2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa using (hx.sub_const (w x)).pow 2
  have hint := tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall hmeas)
    hdom hB hzero
  have hn (i) : ‖v i - W‖^2 = ∫ x, (g i x - w x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v i) W,hcoe i,hw.coeFn_toLp] with x hx hg hwx
    change W x = w x at hwx
    rw [hx]
    simp only [Pi.sub_apply, hg, hwx, RCLike.inner_apply, conj_trivial, pow_two]
  have hsq : Tendsto (fun i => ‖v i - W‖^2) l (𝓝 (0 : ℝ)) := by
    simpa only [hn,integral_zero] using hint
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm' : Tendsto (fun i => ‖v i - W‖) l (𝓝 (0 : ℝ)) := by
    change Tendsto (fun i => Real.sqrt (‖v i - W‖^2)) l (𝓝 (Real.sqrt 0)) at hnorm
    convert hnorm using 1
    · funext i
      exact (Real.sqrt_sq (norm_nonneg (v i - W))).symm
    · rw [Real.sqrt_zero]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

/-- A pointwise differentiable scalar path differentiates in the actual
L² norm whenever its local difference quotients have a true L² dominator. -/
theorem scalarL2_hasDerivAt_of_dominated {F : ℝ → α → ℝ} (hF : ∀ t, MemLp (F t) 2 μ)
    {F' b : α → ℝ} (hF' : MemLp F' 2 μ) (hb : MemLp b 2 μ) (t : ℝ)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => F s x) (F' x) t)
    (hbound : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ x ∂μ,
      ‖(s-t)⁻¹ * (F s x - F t x)‖ ≤ b x) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hF'.toLp F') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply scalarL2_tendsto_of_dominated
    (v := slope (fun s => (hF s).toLp (F s)) t)
    (g := fun s x => (s-t)⁻¹ * (F s x - F t x)) (w := F') (b := b)
    ?_ hF' hb hbound ?_
  · intro s
    unfold slope
    simp only [vsub_eq_sub]
    filter_upwards [Lp.coeFn_smul (s-t)⁻¹ ((hF s).toLp (F s) - (hF t).toLp (F t)),
      Lp.coeFn_sub ((hF s).toLp (F s)) ((hF t).toLp (F t)),
      (hF s).coeFn_toLp,(hF t).coeFn_toLp] with x hs hsub hFs hFt
    rw [hs]
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,hsub,hFs,hFt]
  · filter_upwards [hd] with x hx
    exact hx.tendsto_slope

end Yau.LeafProofs.L19Aux
