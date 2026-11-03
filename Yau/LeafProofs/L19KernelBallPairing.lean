import Yau.LeafProofs.L19KernelBallPairingApprox
import Yau.LeafProofs.L19GaussianExtraction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Actual kernel actions on the smooth core extend to ball indicators by
bounded smooth approximation and dominated convergence in each column. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- Identification on the genuine smooth compact scalar core. -/
def KernelCoreActionIdentity (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ k : ScalarEnergyDomain g μ hμ,
    (fun y => ∫ x, H t x y * k x ∂μ) =ᵐ[μ]
      (scalarHeatFamily g μ hμ t (scalarEnergyDomainL2 g μ hμ k) : M.Carrier → ℝ)

/-- The original columns are genuinely integrable and have subunit mass. -/
def KernelSubmass (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (μ : Measure M.Carrier) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ y,
    Integrable (fun x => H t x y) μ ∧ (∫ x, H t x y ∂μ) ≤ 1

/-- The action on an actual ball is the actual L² heat action, almost
everywhere. The domination uses integrability of each original column. -/
theorem kernelBall_action_ae (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (hcore : KernelCoreActionIdentity g μ hμ H)
    (hcol : ∀ t : ℝ, 0 < t → ∀ y, Integrable (fun x => H t x y) μ)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) (r : ℝ) (hr : 0 < r) :
    (fun y => ∫ z in distBall g.form x r, H t z y ∂μ) =ᵐ[μ]
      (scalarHeatFamily g μ hμ t (scalarBallL2 g μ hμ x r hr) : M.Carrier → ℝ) := by
  classical
  let f := scalarBallL2 g μ hμ x r hr
  let P := scalarHeatFamily g μ hμ t
  obtain ⟨k,hbound,hlim⟩ := kernelBall_exists_bounded_core_approx g μ hμ x r hr
  obtain ⟨ns,hns,hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hPlim : Tendsto (fun j => P (scalarEnergyDomainL2 g μ hμ (k (ns j))))
      atTop (𝓝 (P f)) := P.continuous.continuousAt.tendsto.comp (hlim.comp hns.tendsto_atTop)
  obtain ⟨ms,hms,hmsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hPlim).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ z ∂μ, ∀ j : ℕ,
      scalarEnergyDomainL2 g μ hμ (k j) z = k j z :=
    ae_all_iff.mpr (fun j => scalarEnergyDomainL2_coe g μ hμ (k j))
  have hkAE : ∀ᵐ z ∂μ, Tendsto (fun j => k (ns (ms j)) z) atTop
      (𝓝 ((distBall g.form x r).indicator (fun _ => (1 : ℝ)) z)) := by
    filter_upwards [hnsAE,hcoe,scalarBallL2_coe g μ hμ x r hr] with z hz hcz hfz
    have hh := hz.comp hms.tendsto_atTop
    simp only [hcz, hfz] at hh
    exact hh
  have hcoreAE : ∀ᵐ y ∂μ, ∀ j : ℕ,
      (∫ z, H t z y * k j z ∂μ) = P (scalarEnergyDomainL2 g μ hμ (k j)) y :=
    ae_all_iff.mpr (fun j => hcore t ht (k j))
  filter_upwards [hmsAE,hcoreAE] with y hy hcy
  have hDCT : Tendsto (fun j => ∫ z, H t z y * k (ns (ms j)) z ∂μ) atTop
      (𝓝 (∫ z, H t z y * (distBall g.form x r).indicator (fun _ => (1 : ℝ)) z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun z => H t z y)
    · intro j
      exact ((continuous_of_smoothFn (positiveHeatSolution_slice g.form (hH.1 y) ht)).mul
        (continuous_of_smoothFn (k (ns (ms j))).2.1)).aestronglyMeasurable
    · exact hcol t ht y
    · intro j
      apply ae_of_all
      intro z
      have hpos : 0 ≤ H t z y := ((hH.1 y).2 z t ht).1.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
      exact mul_le_of_le_one_right hpos (hbound _ z)
    · filter_upwards [hkAE] with z hz
      exact hz.const_mul (H t z y)
  have hDCT' : Tendsto (fun j => ∫ z, H t z y * k (ns (ms j)) z ∂μ) atTop
      (𝓝 (∫ z in distBall g.form x r, H t z y ∂μ)) := by
    convert hDCT using 2
    rw [← integral_indicator (measurableSet_distBall g x r)]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    by_cases hz : z ∈ distBall g.form x r <;> simp [Set.indicator, hz]
  have hright : Tendsto (fun j => ∫ z, H t z y * k (ns (ms j)) z ∂μ) atTop
      (𝓝 (P f y)) := by
    simpa only [hcy] using hy
  exact tendsto_nhds_unique hDCT' hright

/-- Genuine outer integrability and the exact two-ball heat pairing follow
from the smooth-core identification and actual column integrability. -/
theorem ballKernelPairingIdentity_of_coreAction (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (hcore : KernelCoreActionIdentity g μ hμ H)
    (hcol : ∀ t : ℝ, 0 < t → ∀ y, Integrable (fun x => H t x y) μ) :
    BallKernelPairingIdentity g μ hμ H := by
  intro t ht x y rx ry hrx hry
  have ha := kernelBall_action_ae g μ hμ hH hcore hcol ht x rx hrx
  have har : (fun w => ∫ z in distBall g.form x rx, H t z w ∂μ)
      =ᵐ[μ.restrict (distBall g.form y ry)]
      (scalarHeatFamily g μ hμ t (scalarBallL2 g μ hμ x rx hrx) : M.Carrier → ℝ) :=
    ae_restrict_of_ae ha
  have hfin := (riemannianVolume_distBall_lt_top g μ hμ y hry).ne
  have hi := integrableOn_Lp_of_measure_ne_top
    (scalarHeatFamily g μ hμ t (scalarBallL2 g μ hμ x rx hrx))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfin
  refine ⟨hi.congr_fun_ae har.symm, ?_⟩
  rw [integral_congr_ae har]
  exact (L2.inner_indicatorConstLp_one (measurableSet_distBall g y ry) hfin _).symm

/-- In particular the internally proved submass property suffices, with no
mass-one or minimal-kernel premise. -/
theorem ballKernelPairingIdentity_of_coreAction_submass (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (hcore : KernelCoreActionIdentity g μ hμ H)
    (hsub : KernelSubmass H μ) : BallKernelPairingIdentity g μ hμ H :=
  ballKernelPairingIdentity_of_coreAction g μ hμ hH hcore (fun t ht y => (hsub t ht y).1)

end Yau.LeafProofs.L19Aux
