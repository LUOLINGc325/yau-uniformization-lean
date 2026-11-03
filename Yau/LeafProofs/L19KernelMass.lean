import Yau.LeafProofs.L19KernelCoreIdentity
import Yau.LeafProofs.L19KernelFatou
import Yau.LeafProofs.L19KernelBallPairing

/-! Integrability of every original kernel column, proved by two genuine Fatou limits. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem scalarHeatKernel_nonnegative_core_subunit (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (k : ScalarEnergyDomain g μ hμ) (hk : ∀ x, k x ∈ Icc (0 : ℝ) 1)
    (y : M.Carrier) {T : ℝ} (hT : 0 < T) :
    Integrable (fun x => H T x y * k x) μ ∧ (∫ x, H T x y * k x ∂μ) ≤ 1 := by
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hε⟩
  let f := scalarEnergyDomainL2 g μ hμ k
  have hf0 : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ k] with x hx
    rw [hx]
    exact (hk x).1
  have hf1 : ∀ᵐ x ∂μ, |f x| ≤ 1 := by
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ k] with x hx
    rw [hx, abs_of_nonneg (hk x).1]
    exact (hk x).2
  apply integrable_nonnegative_fatou_bound μ (by norm_num : (0 : ℝ) ≤ 1)
    (F := fun j x => H T x y * scalarClassicalHeat hn g hK μ hμ f x (ε j))
  · intro j
    exact (scalarHeatKernel_regularized_core_identity hn g hcomplete hK hRic μ hμ hH k y hT (hε j)).1
  · intro j
    exact ae_of_all _ fun x => mul_nonneg ((hH.1 y).2 x T hT).1.le
      (scalarClassicalHeat_nonneg hn g hK μ hμ f hf0 x (hε j))
  · exact ((continuous_of_smoothFn (positiveHeatSolution_slice g.form (hH.1 y) hT)).mul
      (continuous_of_smoothFn k.2.1)).aestronglyMeasurable
  · exact ae_of_all _ fun x => mul_nonneg ((hH.1 y).2 x T hT).1.le (hk x).1
  · exact ae_of_all _ fun x =>
      ((scalarClassicalHeat_compact_tendsto_initial hn g hK μ hμ k x).comp hεlim).const_mul (H T x y)
  · intro j
    rw [(scalarHeatKernel_regularized_core_identity hn g hcomplete hK hRic μ hμ hH k y hT (hε j)).2]
    exact (le_abs_self _).trans (scalarClassicalHeat_linf hn g hK μ hμ f (by norm_num) hf1 y (add_pos hT (hε j)))

/-- The original arbitrary kernel is integrable in each column and has
mass at most one. No minimality or prior mass statement is assumed. -/
theorem scalarHeatKernel_submass (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H) :
    KernelSubmass H μ := by
  intro T hT y
  obtain ⟨A, _hA, hcuts⟩ := exists_uniform_heat_duality_cutoffs n
  obtain ⟨η, hη, hlim⟩ := hcuts M g y
  let k : ℕ → ScalarEnergyDomain g μ hμ := fun j => ⟨η j, (hη j).1, (hη j).2.1⟩
  apply integrable_nonnegative_fatou_bound μ (by norm_num : (0 : ℝ) ≤ 1)
    (F := fun j x => H T x y * η j x)
  · intro j
    exact (scalarHeatKernel_nonnegative_core_subunit hn g hcomplete hK hRic μ hμ hH (k j)
      (hη j).2.2.1 y hT).1
  · intro j
    exact ae_of_all _ fun x => mul_nonneg ((hH.1 y).2 x T hT).1.le ((hη j).2.2.1 x).1
  · exact (continuous_of_smoothFn (positiveHeatSolution_slice g.form (hH.1 y) hT)).aestronglyMeasurable
  · exact ae_of_all _ fun x => ((hH.1 y).2 x T hT).1.le
  · exact ae_of_all _ fun x => by simpa only [mul_one] using (hlim x).const_mul (H T x y)
  · intro j
    exact (scalarHeatKernel_nonnegative_core_subunit hn g hcomplete hK hRic μ hμ hH (k j)
      (hη j).2.2.1 y hT).2

end Yau.LeafProofs.L19Aux
