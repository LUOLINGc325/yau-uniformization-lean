import Yau.Proofs.C07ShortLiftIntegral

/-! The actual lift speed and confinement estimates need only the original lower bound. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Set Filter MeasureTheory C07ShortLiftAux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ} {M : ComplexManifold n}

local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

theorem pullback_derivative_lower {r : ℝ} (k : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (c : ℝ)
    (hlo : ∀ z ∈ Metric.ball 0 r, HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Φ z))
    {z : ComplexVector n} (hz : z ∈ Metric.ball 0 r) (v : ComplexVector n) :
    c * ‖v‖ ^ 2 ≤ hermitianNormSq (k (Φ z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v) := by
  let q : Herm n → ℝ := fun A => (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re
  have hq {A B : Herm n} (hAB : HermLE A B) : q A ≤ q B := by
    have h := (Complex.nonneg_iff.mp (hAB.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
    simpa only [q, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using h
  have hq1 : q 1 = ‖v‖ ^ 2 := by
    have hh := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [EuclideanSpace.inner_eq_star_dotProduct, RCLike.re_eq_complex_re] at hh
    simpa only [q, Matrix.one_mulVec, dotProduct_comm] using hh
  have hscale : q ((c : ℂ) • (1 : Herm n)) = c * ‖v‖ ^ 2 := by
    simp only [q, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact congrArg (c * ·) (by simpa only [q, Matrix.one_mulVec] using hq1)
  have H := hq (hlo z hz)
  rw [hscale] at H
  rw [← C07Aux.pullback_quadratic]
  exact H

theorem lift_differentiable_speed {k : HermitianField M} {o x : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c a b : ℝ}
    (hc : 0 < c) (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball 0 r, HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Φ z))
    (γ : PiecewiseC1Curve o x) {η : ℝ → ComplexVector n}
    (hη : ContinuousOn η (Icc a b))
    (hηp : ∀ t ∈ Icc a b, η t ∈ Metric.ball 0 r ∧ Φ (η t) = γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) (hts : t ∉ γ.breakpoints) :
    DifferentiableAt ℝ η t ∧
      ‖deriv η t‖ ≤ (Real.sqrt (2 * c))⁻¹ * curveSpeed k γ t := by
  let z := η t
  let G : ComplexVector n → ComplexVector n := fun w => chartPt (Φ z) (Φ w)
  let H : ℝ → ComplexVector n := fun u => chartPt (Φ z) (γ u)
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hz : z ∈ Metric.ball 0 r := (hηp _ htcc).1
  have hpz : Φ z = γ t := (hηp _ htcc).2
  obtain ⟨hG, hGbij⟩ := C07Aux.coordinate_chart_invertible hΦ hz
  change ContDiffAt ℂ ∞ G z at hG
  change Function.Bijective (fderiv ℂ G z) at hGbij
  let D : ComplexVector n ≃L[ℂ] ComplexVector n :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ G z)
      (LinearMap.ker_eq_bot.mpr hGbij.1) (LinearMap.range_eq_top.mpr hGbij.2)
  have hGD : HasFDerivAt G (D : ComplexVector n →L[ℂ] ComplexVector n) z := by
    simpa only [D, ContinuousLinearEquiv.coe_ofBijective] using
      (hG.differentiableAt (by simp)).hasFDerivAt
  have hHD : DifferentiableAt ℝ H t := by
    dsimp [H]
    rw [hpz]
    exact (γ.piecewise_c1 t hts).differentiableAt (by simp)
  have hcomp : G ∘ η =ᶠ[𝓝 t] H := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    change chartPt (Φ z) (Φ (η u)) = chartPt (Φ z) (γ u)
    rw [(hηp u hu).2]
  have hηcont : ContinuousAt η t := hη.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hηD : DifferentiableAt ℝ η t :=
    (HasFDerivAt.of_comp_of_leftInverse (f'symm :=
        (D.symm.restrictScalars ℝ).toContinuousLinearMap)
      hηcont (hGD.restrictScalars ℝ) hHD.hasFDerivAt hcomp
      (fun v => D.symm_apply_apply v)).differentiableAt
  have hcoord : fderiv ℝ H t 1 = D (deriv η t) := by
    have h := ((hGD.restrictScalars ℝ).comp t hηD.hasFDerivAt).congr_of_eventuallyEq
      hcomp.symm
    have h' := congrArg (fun L : ℝ →L[ℝ] ComplexVector n => L 1) h.fderiv
    change fderiv ℝ H t 1 = D (fderiv ℝ η t 1) at h'
    simpa only [fderiv_apply_one_eq_deriv] using h'
  have hΦmd := hΦ.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
    |>.mdifferentiableAt (by simp)
  have hΦD (v : ComplexVector n) :
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v = D v := by
    unfold mfderiv
    rw [if_pos hΦmd]
    simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ,
      ContinuousLinearMap.comp_apply]
    change fderiv ℂ G z v = D v
    exact DFunLike.congr_fun hGD.fderiv v
  have hreal : realTangentDerivative γ t = D (deriv η t) := by
    have hid := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := Φ z)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
    unfold realTangentDerivative
    rw [← hpz]
    rw [hid]
    exact hcoord
  have hq := pullback_derivative_lower k Φ c hlo hz (deriv η t)
  rw [hΦD, hpz, ← hreal] at hq
  exact ⟨hηD, inverse_speed_bound hc hq⟩

/-- Every continuous partial lift satisfies the same prefix length bound;
no regularity assumption on the metric is needed beyond the integrability
already carried by the original curve. -/
theorem partial_lift_norm_bound {k : HermitianField M} {o x : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c b : ℝ}
    (hc : 0 < c) (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball 0 r, HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Φ z))
    (γ : IntegrableCurve k o x) (hb : b ∈ Icc (0 : ℝ) 1)
    {η : ℝ → ComplexVector n} (hη : ContinuousOn η (Icc 0 b)) (hη₀ : η 0 = 0)
    (hηp : ∀ t ∈ Icc 0 b, η t ∈ Metric.ball 0 r ∧ Φ (η t) = γ.1 t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) :
    ‖η t‖ ≤ (Real.sqrt (2 * c))⁻¹ * (∫ u in Icc 0 t, curveSpeed k γ.1 u) := by
  let B : ℝ → ℝ := fun u => (Real.sqrt (2 * c))⁻¹ * curveSpeed k γ.1 u
  have hBi : IntegrableOn B (Icc (0 : ℝ) 1) := γ.2.const_mul _
  have hBt : IntervalIntegrable B volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      (hBi.mono_set (Icc_subset_Icc_right (ht.2.trans hb.2)))
  have hηt : ContinuousOn η (Icc 0 t) := hη.mono (Icc_subset_Icc_right ht.2)
  have hs (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) t) (hus : u ∉ γ.1.breakpoints) :=
    lift_differentiable_speed hc hΦ hlo γ.1 hη hηp ⟨hu.1, hu.2.trans_le ht.2⟩ hus
  have h := norm_sub_le_integral_except_finset γ.1.breakpoints ht.1 hηt
    (fun u hu hus => (hs u hu hus).1) (fun u hu hus => (hs u hu hus).2) hBt
  rw [hη₀, sub_zero, intervalIntegral.integral_of_le ht.1,
    ← integral_Icc_eq_integral_Ioc, integral_const_mul] at h
  exact h


end Yau.Proofs.C03Aux.ShortLift
