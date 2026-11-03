import Yau.Proofs.C07PullbackBounds
import Yau.Proofs.C07InverseHolomorphic

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07ShortLiftAux

open Yau Yau.Blueprint Set Filter MeasureTheory

/-- The displacement estimate also holds across the finitely many corners
of a piecewise differentiable path. -/
theorem norm_sub_le_integral_except_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ℝ) {f : ℝ → E} {B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b, t ∉ s → DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Ioo a b, t ∉ s → ‖deriv f t‖ ≤ B t)
    (hB : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hcont
      · intro t ht
        exact (hdiff t ht (by simp)).differentiableWithinAt
      · exact .of_forall fun t ht => hbound t ht (by simp)
      · exact hB
  | @insert t s hts ih =>
      by_cases ht : t ∈ Ioo a b
      · have hat : a ≤ t := ht.1.le
        have htb : t ≤ b := ht.2.le
        have hsub₁ : Icc a t ⊆ Icc a b := Icc_subset_Icc_right htb
        have hsub₂ : Icc t b ⊆ Icc a b := Icc_subset_Icc_left hat
        have hB₁ : IntervalIntegrable B volume a t := by
          apply hB.mono_set
          simpa only [uIcc_of_le hat, uIcc_of_le hab] using hsub₁
        have hB₂ : IntervalIntegrable B volume t b := by
          apply hB.mono_set
          simpa only [uIcc_of_le htb, uIcc_of_le hab] using hsub₂
        have h₁ : ‖f t - f a‖ ≤ ∫ u in a..t, B u := by
          apply ih hat (hcont.mono hsub₁)
          · intro u hu hus
            exact hdiff u ⟨hu.1, hu.2.trans ht.2⟩ (by simp [hus, ne_of_lt hu.2])
          · intro u hu hus
            exact hbound u ⟨hu.1, hu.2.trans ht.2⟩ (by simp [hus, ne_of_lt hu.2])
          · exact hB₁
        have h₂ : ‖f b - f t‖ ≤ ∫ u in t..b, B u := by
          apply ih htb (hcont.mono hsub₂)
          · intro u hu hus
            exact hdiff u ⟨ht.1.trans hu.1, hu.2⟩ (by simp [hus, ne_of_gt hu.1])
          · intro u hu hus
            exact hbound u ⟨ht.1.trans hu.1, hu.2⟩ (by simp [hus, ne_of_gt hu.1])
          · exact hB₂
        calc
          ‖f b - f a‖ ≤ ‖f t - f a‖ + ‖f b - f t‖ := by
            simpa only [dist_eq_norm_sub] using dist_triangle (f b) (f t) (f a)
              |>.trans_eq (add_comm _ _)
          _ ≤ (∫ u in a..t, B u) + ∫ u in t..b, B u := add_le_add h₁ h₂
          _ = ∫ u in a..b, B u := intervalIntegral.integral_add_adjacent_intervals hB₁ hB₂
      · apply ih hab hcont
        · intro u hu hus
          apply hdiff u hu
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun hut => ht (hut ▸ hu), hus⟩
        · intro u hu hus
          apply hbound u hu
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun hut => ht (hut ▸ hu), hus⟩
        · exact hB

variable {n : ℕ} {M : ComplexManifold n}

/-- The factor two in the actual Riemannian speed yields the precise
inverse chart speed factor used in short path lifting. -/
theorem inverse_speed_bound {c q : ℝ} {v : ComplexVector n}
    (hc : 0 < c) (hq : c * ‖v‖ ^ 2 ≤ q) :
    ‖v‖ ≤ (Real.sqrt (2 * c))⁻¹ * Real.sqrt (2 * q) := by
  have hs : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
  have hq₀ : 0 ≤ q := (by positivity : 0 ≤ c * ‖v‖ ^ 2).trans hq
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * q)
  have hsc := Real.sq_sqrt (by positivity : 0 ≤ 2 * c)
  have hmul : Real.sqrt (2 * c) * ‖v‖ ≤ Real.sqrt (2 * q) := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg v)) (Real.sqrt_nonneg _)).1
    rw [mul_pow, hsc, hsq]
    linarith
  exact (le_inv_mul_iff₀ hs).2 hmul

/-- A continuous local lift is differentiable away from the actual curve's
corners, and its Euclidean speed is bounded by the genuine metric speed. -/
theorem lift_differentiable_speed {k : HermitianField M} {o x : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C a b : ℝ}
    (hc : 0 < c) (hΦ : UnitaryChart k o Φ r c C)
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
  obtain ⟨hG, hGbij⟩ := C07Aux.coordinate_chart_invertible hΦ.1 hz
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
  have hΦmd := hΦ.1.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
    |>.mdifferentiableAt (by simp)
  have hΦD (v : ComplexVector n) :
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v = D v := by
    unfold mfderiv
    rw [if_pos hΦmd]
    simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ,
      ContinuousLinearMap.comp_apply]
    change fderiv ℂ G z v = D v
    exact congrArg (fun L : ComplexVector n →L[ℂ] ComplexVector n => L v) hGD.fderiv
  have hreal : realTangentDerivative γ t = D (deriv η t) := by
    have hid := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := Φ z)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
    unfold realTangentDerivative
    rw [← hpz]
    rw [hid]
    exact hcoord
  have hq := (C07Aux.unitaryChart_derivative_bounds hΦ hz (deriv η t)).1
  rw [hΦD, hpz, ← hreal] at hq
  exact ⟨hηD, inverse_speed_bound hc hq⟩

/-- Every continuous partial lift satisfies the same prefix length bound;
no regularity assumption on the metric is needed beyond the integrability
already carried by the original curve. -/
theorem partial_lift_norm_bound {k : HermitianField M} {o x : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C b : ℝ}
    (hc : 0 < c) (hΦ : UnitaryChart k o Φ r c C)
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
    lift_differentiable_speed hc hΦ γ.1 hη hηp ⟨hu.1, hu.2.trans_le ht.2⟩ hus
  have h := norm_sub_le_integral_except_finset γ.1.breakpoints ht.1 hηt
    (fun u hu hus => (hs u hu hus).1) (fun u hu hus => (hs u hu hus).2) hBt
  rw [hη₀, sub_zero, intervalIntegral.integral_of_le ht.1,
    ← integral_Icc_eq_integral_Ioc, integral_const_mul] at h
  exact h

/-- Prefix integrals of the nonnegative curve speed do not exceed the
whole curve length. -/
theorem prefix_integral_le_length {k : HermitianField M} {o x : M.Carrier}
    (γ : IntegrableCurve k o x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u in Icc 0 t, curveSpeed k γ.1 u) ≤ curveLength k γ.1 := by
  apply setIntegral_mono_set γ.2
  · exact .of_forall fun u => Real.sqrt_nonneg _
  · exact .of_forall fun u hu => ⟨hu.1, hu.2.trans ht.2⟩

end Yau.Proofs.C07ShortLiftAux
