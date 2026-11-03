import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

open Set Filter Topology
open scoped Topology

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux

/-- Every punctured planar disc is preconnected, by its genuine polar
parametrization with a positive radial interval and all real angles. -/
theorem isPreconnected_punctured_ball (r : ℝ) :
    IsPreconnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  let P := fun q : ℝ × ℝ ↦ (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have himage : P '' (Ioo (0 : ℝ) r ×ˢ (univ : Set ℝ)) =
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
    ext z
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, _⟩, rfl⟩
      have hnorm : ‖P (t, θ)‖ = t := by
        dsimp [P]
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht.1]
      change 0 < ‖P (t, θ)‖ ∧ ‖P (t, θ)‖ < r
      rw [hnorm]
      exact ht
    · intro hz
      refine ⟨(‖z‖, Complex.arg z), ⟨hz, mem_univ _⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← himage]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image P hP.continuousOn

/-- A positive real radial parameter approaches the puncture through the
actual punctured complex neighborhood, for every fixed angle. -/
theorem tendsto_radial_punctured (θ : ℝ) :
    Tendsto (fun r : ℝ ↦ (r : ℂ) * Complex.exp (θ * Complex.I)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul_const (Complex.exp (θ * Complex.I))
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [mem_compl_iff, mem_singleton_iff, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
      Complex.exp_ne_zero, or_false]
    exact ne_of_gt hr

/-- Compact boundary trapping in a proper target metric. The map `F` is only
continuous and injective; no global properness or embedding premise is used.
The full radial limit and the ambient punctured limit refer to the SAME `p`. -/
theorem tendsto_of_injective_ambient_and_radial
    {Y E : Type*} [MetricSpace Y] [ProperSpace Y] [TopologicalSpace E] [T2Space E]
    {f : ℂ → Y} {F : Y → E} {p : Y} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R})
    (hF : Continuous F) (hinj : Function.Injective F)
    (hambient : Tendsto (F ∘ f) (𝓝[≠] 0) (𝓝 (F p)))
    (θ : ℝ) (hradial : Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (𝓝[>] 0) (𝓝 p)) :
    Tendsto f (𝓝[≠] 0) (𝓝 p) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcompact : IsCompact (F '' Metric.sphere p ε) :=
    (isCompact_sphere p ε).image hF
  have hpnot : F p ∉ F '' Metric.sphere p ε := by
    rintro ⟨x, hx, hxp⟩
    have heq := hinj hxp
    subst x
    exact hε.ne (by simpa only [Metric.mem_sphere, dist_self] using hx)
  have havoid : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (f z) ∉ F '' Metric.sphere p ε :=
    hambient (hcompact.isClosed.isOpen_compl.mem_nhds hpnot)
  obtain ⟨δ, hδ, hδavoid⟩ := Metric.mem_nhdsWithin_iff.mp havoid
  let t := min R δ
  have ht : 0 < t := lt_min hR hδ
  let D := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < t}
  have hD : D ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R} :=
    fun z hz ↦ ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  have hne : ∀ z ∈ D, dist (f z) p ≠ ε := by
    intro z hz heq
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz.1
    have hzδ : dist z (0 : ℂ) < δ := by
      simpa only [dist_zero_right] using hz.2.trans_le (min_le_right R δ)
    have hnot := hδavoid ⟨hzδ, hz0⟩
    exact hnot ⟨f z, heq, rfl⟩
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < t ∧
      dist (f ((s : ℂ) * Complex.exp (θ * Complex.I))) p < ε := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t from (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds),
      hradial (Metric.ball_mem_nhds p hε)] with s hs hst hsp
    exact ⟨hs, hst, hsp⟩
  obtain ⟨s, hs, hst, hsp⟩ := hsmall.exists
  have hnorm : ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ = s := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
  have hall : ∀ z ∈ D, dist (f z) p < ε := by
    apply (isPreconnected_punctured_ball t).gt_of_ne
      (continuous_dist.comp_continuousOn ((hf.mono hD).prodMk continuousOn_const)) hne
    refine ⟨_, ?_, hsp⟩
    change 0 < ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ ∧
      ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ < t
    rw [hnorm]
    exact ⟨hs, hst⟩
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨t, ht, ?_⟩
  intro z hz
  apply hall
  exact ⟨norm_pos_iff.mpr hz.2, by simpa only [Metric.mem_ball, dist_zero_right] using hz.1⟩

end Yau.NodeProofs.D02RemovableAux
