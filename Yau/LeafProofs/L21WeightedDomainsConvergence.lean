import Yau.LeafProofs.L21WeightedDomainsCutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedBallMeasure_eq_restrict (K : ℝ) : weightedBallMeasure n K =
    ((Yau.lebesgueC n).withDensity (weightedBallDensity K)).restrict (Metric.ball 0 1) := by
  rw [restrict_withDensity Metric.isOpen_ball.measurableSet]
  rfl

theorem weightedBoundaryCutoff_error_tendsto (K : ℝ) {u : X n → ℂ}
    (hu : MemLp u 2 (weightedBallMeasure n K)) :
    (∀ m, MemLp (fun x => (boundaryCutoff m x : ℂ)*u x-u x) 2 (weightedBallMeasure n K)) ∧
      Tendsto (fun m => ∫ x, ‖(boundaryCutoff m x : ℂ)*u x-u x‖^2 ∂weightedBallMeasure n K)
        atTop (𝓝 0) := by
  rw [weightedBallMeasure_eq_restrict] at hu ⊢
  simpa only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one,sub_mul,one_mul] using
    boundaryCutoff_L2_convergence ((Yau.lebesgueC n).withDensity (weightedBallDensity K)) hu

/-- A bounded principal coefficient times the rho-scaled cutoff
commutator tends to zero in the actual weighted L² norm. -/
theorem weightedBoundaryCutoff_principal_error_tendsto (K : ℝ) (hK : 0 ≤ K)
    {p u : X n → ℂ} (hp : ContinuousOn p (Metric.ball 0 1))
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ x ∈ Metric.ball (0 : X n) 1, ‖p x‖ ≤ C)
    (hu : MemLp u 2 (weightedBallMeasure n K)) (v : X n) :
    (∀ m, MemLp (fun x => p x*((rho x*fderiv ℝ (boundaryCutoff m) x v : ℝ) : ℂ)*u x)
        2 (weightedBallMeasure n K)) ∧
      Tendsto (fun m => ∫ x, ‖p x*((rho x*fderiv ℝ (boundaryCutoff m) x v : ℝ) : ℂ)*u x‖^2
        ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  obtain ⟨B,hB,hCutoff⟩ := exists_bound_scaled_fderiv_boundaryCutoff (E := X n)
  have hpMeas : AEStronglyMeasurable p (weightedBallMeasure n K) :=
    (hp.aestronglyMeasurable Metric.isOpen_ball.measurableSet).mono_measure
      (weightedBallMeasure_le_restrict K hK)
  have hBall : ∀ᵐ x ∂weightedBallMeasure n K, x ∈ Metric.ball (0 : X n) 1 :=
    (weightedBallMeasure_ae_iff K _).mpr (ae_restrict_mem Metric.isOpen_ball.measurableSet)
  apply tendsto_integral_norm_sq_of_dominated (C := C*B*‖v‖) _ hu
  · intro m
    have hd : Continuous (fun x : X n => rho x*fderiv ℝ (boundaryCutoff m) x v) :=
      contDiff_rho.continuous.mul
        (((contDiff_boundaryCutoff m).continuous_fderiv (by simp)).clm_apply continuous_const)
    exact (hpMeas.mul (Complex.ofRealCLM.continuous.comp hd).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · positivity
  · intro m
    filter_upwards [hBall] with x hx
    have hd : ‖rho x*fderiv ℝ (boundaryCutoff m) x v‖ ≤ B*‖v‖ := by
      change ‖(rho x • fderiv ℝ (boundaryCutoff m) x) v‖ ≤ _
      exact ((rho x • fderiv ℝ (boundaryCutoff m) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hCutoff m x hx) (norm_nonneg v))
    calc
      _ = ‖p x‖*‖rho x*fderiv ℝ (boundaryCutoff m) x v‖*‖u x‖ := by
        simp only [norm_mul,Complex.norm_real]
      _ ≤ C*(B*‖v‖)*‖u x‖ := by gcongr; exact hBound x hx
      _ = _ := by ring
  · filter_upwards [hBall] with x hx
    have he : (fun m => p x*((rho x*fderiv ℝ (boundaryCutoff m) x v : ℝ) : ℂ)*u x) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℂ)) := by
      filter_upwards [eventually_fderiv_boundaryCutoff_eq_zero hx] with m hm
      simp only [hm,_root_.zero_apply,mul_zero,Complex.ofReal_zero,zero_mul]
    exact tendsto_const_nhds.congr' he.symm

end Yau.LeafProofs.L21Aux
