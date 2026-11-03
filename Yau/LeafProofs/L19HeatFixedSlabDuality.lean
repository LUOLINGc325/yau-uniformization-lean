import Yau.LeafProofs.L19HeatDualCutoffError

/-! Genuine global heat duality on fixed positive slabs, before any trace or mass argument. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

/-- Original arbitrary positive heat solutions pair constantly with
backward Gaussian-decaying genuine heat tests on every fixed positive
slab.  Integrability and the vanishing boundary error are proved here;
there is no mass, uniqueness, initial trace or growth premise on u. -/
theorem positiveHeatSolution_gaussian_backward_duality
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (hI : IsOpen I) (hIpos : I ⊆ Ioi 0)
    (hv : SmoothSpaceTime v I)
    (hbackward : ∀ x t, t ∈ I → HasDerivAt (v x) (-laplacian g.form (fun y => v y t) x) t)
    (o : M.Carrier) {s T C β : ℝ} (hs : 0 < s) (hslab : Icc s T ⊆ I) (hsT : s ≤ T)
    (hC : 0 < C) (hβ : 0 < β)
    (hdecay : ∀ x t, t ∈ Icc s T → |v x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :
    Integrable (fun x => u x s * v x s) μ ∧ Integrable (fun x => u x T * v x T) μ ∧
      (∫ x, u x T * v x T ∂μ) = ∫ x, u x s * v x s ∂μ := by
  obtain ⟨_B, _hB, _hdom, hi⟩ := positiveHeatSolution_slab_gaussian_product_domination
    g hcomplete hK hRic μ hμ hu o hs hsT hC hβ
    (fun t ht => continuous_of_smoothFn (smoothSpaceTime_slice hv (hslab ht))) hdecay
  have his := hi s ⟨le_rfl, hsT⟩
  have hiT := hi T ⟨hsT, le_rfl⟩
  refine ⟨his, hiT, ?_⟩
  obtain ⟨A, hA, hcuts⟩ := exists_uniform_heat_duality_cutoffs n
  obtain ⟨η, hη, hηlim⟩ := hcuts M g o
  obtain ⟨K, hK0, herror⟩ := positiveHeatSolution_gaussian_test_cutoff_error g hcomplete hK hRic μ hμ
    hu hI hIpos hv hbackward o hs hslab hsT hC hβ hdecay A
  let R : ℕ → ℝ := fun j => (j : ℝ) + 1
  have hR (j : ℕ) : 1 ≤ R j := by dsimp only [R]; have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith
  have hηE (j : ℕ) (x : M.Carrier) : scalarGradientPair g.form (η j) (η j) x ≤ A ^ 2 := by
    apply (hη j).2.2.2.2.2 x |>.trans
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (hR j)) 2)).mpr
    have hsq : 1 ≤ R j ^ 2 := by nlinarith [sq_nonneg (R j - 1), hR j]
    change A ^ 2 ≤ A ^ 2 * R j ^ 2
    exact le_mul_of_one_le_right (sq_nonneg A) hsq
  have hbound (j : ℕ) :
      |(∫ x, η j x * u x T * v x T ∂μ) - (∫ x, η j x * u x s * v x s ∂μ)| ≤
        K * Real.exp (-(β / 16) * R j ^ 2) :=
    herror (R j) (hR j) (η j) (hη j).1 (hη j).2.1 (hη j).2.2.2.1 (hη j).2.2.2.2.1 (hηE j)
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have he : Tendsto (fun r : ℝ => Real.exp (-((β / 16) * r ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) (by positivity : 0 < β / 16))
  have hupper : Tendsto (fun j => K * Real.exp (-(β / 16) * R j ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_mul, Function.comp_def] using (he.comp hRtop).const_mul K
  have hzero : Tendsto (fun j =>
      (∫ x, η j x * u x T * v x T ∂μ) - (∫ x, η j x * u x s * v x s ∂μ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun j => abs_nonneg _) hbound hupper
  have hTlim : Tendsto (fun j => ∫ x, η j x * u x T * v x T ∂μ) atTop
      (𝓝 (∫ x, u x T * v x T ∂μ)) := by
    simpa only [mul_assoc] using integral_tendsto_smooth_cutoffs μ (fun j => (hη j).1)
      (fun j => (hη j).2.2.1) hηlim hiT
  have hslim : Tendsto (fun j => ∫ x, η j x * u x s * v x s ∂μ) atTop
      (𝓝 (∫ x, u x s * v x s ∂μ)) := by
    simpa only [mul_assoc] using integral_tendsto_smooth_cutoffs μ (fun j => (hη j).1)
      (fun j => (hη j).2.2.1) hηlim his
  exact sub_eq_zero.mp (tendsto_nhds_unique (hTlim.sub hslim) hzero)

end Yau.LeafProofs.L19Aux
