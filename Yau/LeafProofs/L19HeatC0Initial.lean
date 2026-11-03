import Yau.LeafProofs.L19HeatUniformBounds
import Yau.LeafProofs.L19SmoothDensity
import Yau.LeafProofs.L19GaussianWeightComparison
import Yau.LeafProofs.L19GaussianIntegrability

/-! Uniform approximation and initial trace for continuous decaying
data in the actual constructed scalar heat flow. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem continuous_uniform_bound_of_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : M.Carrier → ℝ} (hf : Continuous f)
    {K : ℝ} (hbound : ∀ᵐ x ∂μ, f x ≤ K) : ∀ x, f x ≤ K := by
  letI : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  have hzero : (fun x => max (f x - K) 0) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hbound] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have heq := MeasureTheory.Measure.eq_of_ae_eq hzero
    ((hf.sub continuous_const).max continuous_const) continuous_const
  intro x
  have hx := congrFun heq x
  have hh := le_max_left (f x - K) (0 : ℝ)
  rw [hx] at hh
  linarith only [hh]

/-- The original proper metric cutoffs and actual manifold smoothing
produce uniform compact scalar approximations for decaying data. -/
theorem exists_uniform_compact_core_of_radial_decay (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {f : M.Carrier → ℝ} (hf : Continuous f)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x,
      R ≤ inducedDistance g.form o x → |f x| < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ScalarEnergyDomain g μ hμ, ∀ x, |f x - k x| < ε := by
  letI := manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  obtain ⟨R, hR, hfar⟩ := hdecay (ε / 4) (by positivity)
  obtain ⟨η, hη, hcη, hηrange, hηone, _⟩ :=
    exists_smooth_compact_cutoff g o hR (show R < R + 1 by linarith)
  let F : M.Carrier → ℝ := fun x => η x * f x
  have hFc : Continuous F := (continuous_of_smoothFn hη).mul hf
  have hFcompact : HasCompactSupport F := hcη.mul_right
  obtain ⟨k, hkapprox, hksupport⟩ := hFc.exists_contMDiff_approx
    𝓘(ℝ, ComplexVector n) ⊤ (ε := fun _ => ε / 4) continuous_const (fun _ => by positivity)
  refine ⟨⟨k, smoothFn_of_contMDiff_real k.contMDiff, hFcompact.mono hksupport⟩, ?_⟩
  intro x
  have hdiff : |f x - F x| ≤ ε / 4 := by
    by_cases hx : inducedDistance g.form o x ≤ R
    · have he := hηone x hx
      simp only [F, he, one_mul, sub_self, abs_zero]
      positivity
    · have hsmall := hfar x (le_of_lt (lt_of_not_ge hx))
      have h1 : |1 - η x| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (hηrange x).2)]
        linarith [(hηrange x).1]
      have he : f x - F x = (1 - η x) * f x := by dsimp [F]; ring
      rw [he, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans hsmall.le
  have hkx : |F x - k x| < ε / 4 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hkapprox x
  have htri := abs_sub_le (f x) (F x) (k x)
  change |f x - k x| < ε
  linarith only [htri, hdiff, hkx, hε]

/-- Each true compact smooth scalar has a finite bound on its actual
computed Laplacian. -/
theorem scalarCompactLaplacian_bounded (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ScalarEnergyDomain g μ hμ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |laplacian g.form k x| ≤ K := by
  obtain ⟨C, hC⟩ := (continuous_of_smoothFn (smoothFn_laplacian g k.2.1)).bounded_above_of_compact_support
    (laplacian_hasCompactSupport g.form k.2.1 k.2.2)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x
  have hx : |laplacian g.form k x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_right _ _)

/-- Uniform compact approximation and the actual Markov/Duhamel theorems
give the genuine uniform initial trace for every continuous representative
of the fixed constructed heat family. -/
theorem scalarHeat_uniform_initial_of_compact_approximations
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (fL : Lp ℝ 2 μ)
    (hfL : fL =ᵐ[μ] f)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ScalarEnergyDomain g μ hμ, ∀ x, |f x - k x| < ε)
    {u : M.Carrier → ℝ → ℝ} (hu : ∀ t : ℝ, 0 < t → Continuous (fun x => u x t))
    (huL : ∀ t : ℝ, 0 < t → (fun x => u x t) =ᵐ[μ] scalarHeatFamily g μ hμ t fL) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ x : M.Carrier, |u x t - f x| < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := happrox (ε / 4) (by positivity)
  obtain ⟨K, hK0, hLap⟩ := scalarCompactLaplacian_bounded g μ hμ k
  let δ := ε / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hsub : ∀ᵐ x ∂μ, |(fL - scalarEnergyDomainL2 g μ hμ k) x| ≤ ε / 4 := by
    filter_upwards [hfL, scalarEnergyDomainL2_coe g μ hμ k,
      Lp.coeFn_sub fL (scalarEnergyDomainL2 g μ hμ k)] with x hfx hkx hs
    rw [hs, Pi.sub_apply, hfx, hkx]
    exact (hk x).le
  have hheat := scalarHeatFamily_linf g μ hμ ht.le (ε / 4) (by positivity)
    (fL - scalarEnergyDomainL2 g μ hμ k) hsub
  rw [map_sub] at hheat
  have hinit := scalarHeat_compact_initial_ae g hK μ hμ k hK0 ht hLap
  have hAE : ∀ᵐ x ∂μ, |u x t - k x| ≤ ε / 4 + t * K := by
    filter_upwards [huL t ht, hheat, hinit,
      Lp.coeFn_sub (scalarHeatFamily g μ hμ t fL)
        (scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k))] with x hux hh hi hs
    rw [hs, Pi.sub_apply] at hh
    have htri := abs_sub_le (u x t)
      (scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k) x) (k x)
    rw [hux] at htri
    rw [hux]
    linarith only [htri, hh, hi]
  have hpoint := continuous_uniform_bound_of_ae g μ hμ
    (((hu t ht).sub (continuous_of_smoothFn k.2.1)).abs) hAE
  have htK : t * K < ε / 2 := by
    have hm := mul_lt_mul_of_pos_right htδ (show 0 < K + 1 by linarith)
    have hc : δ * (K + 1) = ε / 2 := by dsimp [δ]; field_simp
    rw [hc] at hm
    nlinarith only [hm, ht]
  intro x
  have htri := abs_sub_le (u x t) (k x) (f x)
  have hkx : |k x - f x| < ε / 4 := by rw [abs_sub_comm]; exact hk x
  have hpx := hpoint x
  change |u x t - k x| ≤ ε / 4 + t * K at hpx
  linarith only [htri, hpx, hkx, htK]

theorem gaussianWeight_memLp_two (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a : ℝ} (ha : 0 < a) :
    MemLp (gaussianWeight g o a) 2 μ := by
  change MemLp (fun y => Real.exp (-(a * inducedDistance g.form o y ^ 2))) 2 μ
  simpa only [neg_mul] using memLp_exp_neg_distance_sq g hK hRic μ hμ o ha

/-- The actual Gaussian as a member of the given scalar L² space. -/
def scalarGaussianL2 (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (a : ℝ) (ha : 0 < a) : Lp ℝ 2 μ :=
  (gaussianWeight_memLp_two g hK hRic μ hμ o ha).toLp (gaussianWeight g o a)

theorem scalarHeat_gaussian_uniform_initial (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {a : ℝ} (ha : 0 < a)
    {u : M.Carrier → ℝ → ℝ} (hu : ∀ t : ℝ, 0 < t → Continuous (fun x => u x t))
    (huL : ∀ t : ℝ, 0 < t → (fun x => u x t) =ᵐ[μ]
      scalarHeatFamily g μ hμ t (scalarGaussianL2 g hK hRic μ hμ o a ha)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ x : M.Carrier, |u x t - gaussianWeight g o a x| < ε := by
  apply scalarHeat_uniform_initial_of_compact_approximations g hK μ hμ (gaussianWeight g o a)
    (scalarGaussianL2 g hK hRic μ hμ o a ha)
    (gaussianWeight_memLp_two g hK hRic μ hμ o ha).coeFn_toLp
  · intro ε hε
    apply exists_uniform_compact_core_of_radial_decay g μ hμ o (gaussianWeight_continuous g o a)
    · intro η hη
      obtain ⟨R, hR, hfar⟩ := gaussianWeight_small_far g o ha hη
      refine ⟨R, hR, ?_⟩
      intro x hx
      rw [abs_of_pos (gaussianWeight_pos g o a x)]
      exact hfar x hx
    · exact hε
  · exact hu
  · exact huL

end Yau.LeafProofs.L19Aux
