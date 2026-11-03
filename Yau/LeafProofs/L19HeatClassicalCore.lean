import Yau.LeafProofs.L19HeatClassical

/-! Actual classical compact test flows, including signed test functions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Positivity of the actual heat bounds the signed classical flow by
its internally constructed absolute-data flow. -/
theorem scalarClassicalHeat_abs_le (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    |scalarClassicalHeat hn g hK μ hμ f x t| ≤ scalarClassicalHeat hn g hK μ hμ |f| x t := by
  have hplus : ∀ᵐ z ∂μ, 0 ≤ (|f| + f : Lp ℝ 2 μ) z := by
    filter_upwards [Lp.coeFn_abs f, Lp.coeFn_add |f| f] with z ha hp
    rw [hp, Pi.add_apply, ha]
    linarith [neg_abs_le (f z)]
  have hminus : ∀ᵐ z ∂μ, 0 ≤ (|f| - f : Lp ℝ 2 μ) z := by
    filter_upwards [Lp.coeFn_abs f, Lp.coeFn_sub |f| f] with z ha hp
    rw [hp, Pi.sub_apply, ha]
    exact sub_nonneg.mpr (le_abs_self _)
  have hPp := scalarHeatFamily_nonneg g μ hμ ht.le (|f| + f) hplus
  have hPm := scalarHeatFamily_nonneg g μ hμ ht.le (|f| - f) hminus
  have hAE : ∀ᵐ z ∂μ, |scalarClassicalHeat hn g hK μ hμ f z t| -
      scalarClassicalHeat hn g hK μ hμ |f| z t ≤ 0 := by
    have hp : scalarHeatFamily g μ hμ t (|f| + f) =
        scalarHeatFamily g μ hμ t |f| + scalarHeatFamily g μ hμ t f := map_add _ _ _
    have hm : scalarHeatFamily g μ hμ t (|f| - f) =
        scalarHeatFamily g μ hμ t |f| - scalarHeatFamily g μ hμ t f := map_sub _ _ _
    rw [hp] at hPp
    rw [hm] at hPm
    filter_upwards [hPp, hPm, Lp.coeFn_add (scalarHeatFamily g μ hμ t |f|) (scalarHeatFamily g μ hμ t f),
      Lp.coeFn_sub (scalarHeatFamily g μ hμ t |f|) (scalarHeatFamily g μ hμ t f),
      scalarClassicalHeat_ae hn g hK μ hμ f ht, scalarClassicalHeat_ae hn g hK μ hμ |f| ht]
      with z hp hm hadd hsub hf ha
    rw [hadd, Pi.add_apply] at hp
    rw [hsub, Pi.sub_apply] at hm
    rw [hf, ha]
    exact sub_nonpos.mpr (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hc := ((continuous_of_smoothFn (smoothSpaceTime_slice
    (scalarClassicalHeat_smooth hn g hK μ hμ f) ht)).abs).sub
      (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ |f|) ht))
  exact sub_nonpos.mp (continuous_uniform_bound_of_ae g μ hμ hc hAE x)

/-- The actual classical heat of any signed smooth compact scalar has
Gaussian decay on each compact positive time slab. -/
theorem scalarClassicalCompactHeat_tail (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (o : M.Carrier) {l b : ℝ} (hl : 0 < l) (hlb : l ≤ b) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ x t, t ∈ Icc l b →
      |scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x t| ≤
        C * Real.exp (-β * inducedDistance g.form o x ^ 2) := by
  let f := scalarEnergyDomainL2 g μ hμ k
  obtain ⟨r, hr⟩ := k.2.2.bddAbove_image (continuous_distFrom g o).continuousOn
  let R := max r 0 + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hf : ∀ᵐ z ∂μ, 0 ≤ (|f| : Lp ℝ 2 μ) z := by
    filter_upwards [Lp.coeFn_abs f] with z hz
    rw [hz]
    exact abs_nonneg _
  have hfs : ∀ᵐ z ∂μ, z ∉ distBall g.form o R → (|f| : Lp ℝ 2 μ) z = 0 := by
    filter_upwards [Lp.coeFn_abs f, scalarEnergyDomainL2_coe g μ hμ k] with z hz hk hzR
    rw [hz, hk]
    have hzk : z ∉ tsupport (k : M.Carrier → ℝ) := by
      intro hzs
      have hzr : inducedDistance g.form o z ≤ r := hr ⟨z, hzs, rfl⟩
      have hzlt : inducedDistance g.form o z < R := by dsimp only [R]; linarith [le_max_left r 0]
      exact hzR ((mem_distBall_iff g o z hR).mpr hzlt)
    rw [image_eq_zero_of_notMem_tsupport hzk, abs_zero]
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarCompactHeatRepresentative_gaussian_tail g hcomplete hK hRic μ hμ
    o R hR |f| hf hfs (scalarClassicalHeat_smooth hn g hK μ hμ |f|)
    (fun x t ht => scalarClassicalHeat_pde hn g hK μ hμ |f| x ht)
    (fun t ht => (scalarClassicalHeat_ae hn g hK μ hμ |f| ht).symm) l b hl hlb
  refine ⟨C, β, hC, hβ, ?_⟩
  intro x t ht
  exact (scalarClassicalHeat_abs_le hn g hK μ hμ f x (hl.trans_le ht.1)).trans (htail x t ht)

/-- The true compact first-order initial bound holds pointwise for the
actual classical representative. -/
theorem scalarClassicalHeat_compact_initial_bound (hn : 0 < n) (g : SmoothMetric M)
    (hK : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {K t : ℝ} (hK0 : 0 ≤ K) (ht : 0 < t)
    (hLap : ∀ x, |laplacian g.form k x| ≤ K) (x : M.Carrier) :
    |scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x t - k x| ≤ t * K := by
  have hAE : ∀ᵐ z ∂μ,
      |scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) z t - k z| ≤ t * K := by
    filter_upwards [scalarHeat_compact_initial_ae g hK μ hμ k hK0 ht hLap,
      scalarClassicalHeat_ae hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) ht] with z hz he
    rwa [he]
  exact continuous_uniform_bound_of_ae g μ hμ
    (((continuous_of_smoothFn (smoothSpaceTime_slice
      (scalarClassicalHeat_smooth hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k)) ht)).sub
        (continuous_of_smoothFn k.2.1)).abs) hAE x

/-- The actual bounded-data estimate holds pointwise for the smooth heat. -/
theorem scalarClassicalHeat_linf (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ)
    {K : ℝ} (hK0 : 0 ≤ K) (hf : ∀ᵐ x ∂μ, |f x| ≤ K) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    |scalarClassicalHeat hn g hK μ hμ f x t| ≤ K := by
  have hAE : ∀ᵐ z ∂μ, |scalarClassicalHeat hn g hK μ hμ f z t| ≤ K := by
    filter_upwards [scalarHeatFamily_linf g μ hμ ht.le K hK0 f hf,
      scalarClassicalHeat_ae hn g hK μ hμ f ht] with z hz he
    rwa [he]
  exact continuous_uniform_bound_of_ae g μ hμ
    (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ f) ht)).abs hAE x

/-- Actual smooth compact heat tests attain their original values at time zero. -/
theorem scalarClassicalHeat_compact_tendsto_initial (hn : 0 < n) (g : SmoothMetric M)
    (hK : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (x : M.Carrier) :
    Tendsto (fun t : ℝ => scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x t)
      (𝓝[>] 0) (𝓝 (k x)) := by
  obtain ⟨K, hK0, hLap⟩ := scalarCompactLaplacian_bounded g μ hμ k
  have htK : Tendsto (fun t : ℝ => t * K) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).mul_const K
  have hz : Tendsto (fun t : ℝ => scalarClassicalHeat hn g hK μ hμ
      (scalarEnergyDomainL2 g μ hμ k) x t - k x) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ htK
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.norm_eq_abs]
    exact scalarClassicalHeat_compact_initial_bound hn g hK μ hμ k hK0 ht hLap x
  simpa only [zero_add, sub_add_cancel] using hz.add_const (k x)

end Yau.LeafProofs.L19Aux
