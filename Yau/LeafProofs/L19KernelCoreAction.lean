import Yau.LeafProofs.L19KernelMass

/-! Removing the regularization identifies the original kernel on the actual compact core. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

/-- Every original kernel acts on each genuine smooth compact scalar by
the actual classical heat. Column integrability is proved internally. -/
theorem scalarHeatKernel_core_action_pointwise (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (k : ScalarEnergyDomain g μ hμ) (y : M.Carrier) {T : ℝ} (hT : 0 < T) :
    Integrable (fun x => H T x y * k x) μ ∧
      (∫ x, H T x y * k x ∂μ) = scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) y T := by
  have hcol := (scalarHeatKernel_submass hn g hcomplete hK hRic μ hμ hH T hT y).1
  have hi : Integrable (fun x => H T x y * k x) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (positiveHeatSolution_slice g.form (hH.1 y) hT) k.2.1) k.2.2.mul_left
  refine ⟨hi, ?_⟩
  obtain ⟨C, hC⟩ := (continuous_of_smoothFn k.2.1).bounded_above_of_compact_support k.2.2
  let L := max C 0
  have hL : 0 ≤ L := le_max_right _ _
  have hkb (x : M.Carrier) : |k x| ≤ L := by
    have hh : |k x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
    exact hh.trans (le_max_left _ _)
  obtain ⟨K, hK0, hLap⟩ := scalarCompactLaplacian_bounded g μ hμ k
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hε1 (j : ℕ) : ε j ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεlimGT : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩
  let f := scalarEnergyDomainL2 g μ hμ k
  have hUb (j : ℕ) (x : M.Carrier) : |scalarClassicalHeat hn g hK μ hμ f x (ε j)| ≤ L + K := by
    have hd := scalarClassicalHeat_compact_initial_bound hn g hK μ hμ k hK0 (hε j) hLap x
    have hm : ε j * K ≤ K := mul_le_of_le_one_left hK0 (hε1 j)
    have ht := abs_sub_le (scalarClassicalHeat hn g hK μ hμ f x (ε j)) (k x) 0
    simp only [sub_zero] at ht
    linarith only [hd, hm, ht, hkb x]
  have hlim : Tendsto (fun j => ∫ x, H T x y * scalarClassicalHeat hn g hK μ hμ f x (ε j) ∂μ)
      atTop (𝓝 (∫ x, H T x y * k x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => (L + K) * H T x y)
    · intro j
      exact ((continuous_of_smoothFn (positiveHeatSolution_slice g.form (hH.1 y) hT)).mul
        (continuous_of_smoothFn (smoothSpaceTime_slice (scalarClassicalHeat_smooth hn g hK μ hμ f) (hε j)))).aestronglyMeasurable
    · exact hcol.const_mul (L + K)
    · intro j
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos ((hH.1 y).2 x T hT).1]
        exact (mul_le_mul_of_nonneg_left (hUb j x) ((hH.1 y).2 x T hT).1.le).trans_eq (by ring)
    · exact ae_of_all _ fun x =>
        ((scalarClassicalHeat_compact_tendsto_initial hn g hK μ hμ k x).comp hεlimGT).const_mul (H T x y)
  have hc := (smoothSpaceTime_time_contDiffAt (scalarClassicalHeat_smooth hn g hK μ hμ f) y
    (Ioi_mem_nhds hT)).continuousAt
  have htime : Tendsto (fun j => T + ε j) atTop (𝓝 T) := by simpa only [add_zero] using hεlim.const_add T
  have hact : Tendsto (fun j => ∫ x, H T x y * scalarClassicalHeat hn g hK μ hμ f x (ε j) ∂μ)
      atTop (𝓝 (scalarClassicalHeat hn g hK μ hμ f y T)) := by
    have hhc := hc.tendsto.comp htime
    apply hhc.congr'
    exact Eventually.of_forall fun j =>
      (scalarHeatKernel_regularized_core_identity hn g hcomplete hK hRic μ hμ hH k y hT (hε j)).2.symm
  exact tendsto_nhds_unique hlim hact

/-- The unchanged original kernel has the actual L² heat action on the
independently constructed smooth compact core. -/
theorem scalarHeatKernel_core_action (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H) :
    KernelCoreActionIdentity g μ hμ H := by
  intro T hT k
  filter_upwards [scalarClassicalHeat_ae hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) hT] with y hy
  rw [(scalarHeatKernel_core_action_pointwise hn g hcomplete hK hRic μ hμ hH k y hT).2]
  exact hy

/-- The actual double-ball pairing condition is now fully internal. -/
theorem scalarHeatKernel_ball_pairing (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H) :
    BallKernelPairingIdentity g μ hμ H :=
  ballKernelPairingIdentity_of_coreAction g μ hμ hH
    (scalarHeatKernel_core_action hn g hcomplete hK hRic μ hμ hH)
    (fun t ht y => (scalarHeatKernel_submass hn g hcomplete hK hRic μ hμ hH t ht y).1)

end Yau.LeafProofs.L19Aux
