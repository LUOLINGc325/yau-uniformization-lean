import Yau.LeafProofs.L23LocalDistanceSupportTime

/-! The genuine short-path barrier gives time comparison for clipped distance. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem fieldPathELength_upper_of_tangentNorm_upper
    (h₀ h₁ : HermitianField M) (O : Set M.Carrier) (Qfac : ℝ) (hC : 0 ≤ Qfac)
    (hmetric : ∀ x ∈ O, ∀ v : TangentVector M x,
      2*hermitianNormSq (h₁ x) v ≤ Qfac^2*(2*hermitianNormSq (h₀ x) v))
    (γ : ℝ → M.Carrier) {a b : ℝ} (himage : ∀ s ∈ Set.Icc a b, γ s ∈ O) :
    fieldPathELength h₁ γ a b ≤ ENNReal.ofReal Qfac * fieldPathELength h₀ γ a b := by
  rw [fieldPathELength_eq_lintegral, fieldPathELength_eq_lintegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have H := Real.sqrt_le_sqrt (hmetric (γ s) (himage s hs)
    (realTangentEquiv (γ s) (realCurveVelocity γ s)))
  rw [Real.sqrt_mul (sq_nonneg Qfac), Real.sqrt_sq hC] at H
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal H

section Flow
variable (h : ℝ → HermitianField M) (p q : M.Carrier) (a K r τ σ rIn rOut : ℝ)
  (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
  (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
  (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ u ∈ Set.Icc a (a+2*τ),
    curvatureJetNorm (h u) 0 x ≤ K)
  (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
  (hq : q ∈ distBall (h a) p rIn)
include p r hK hr hτ hσ hflow hcurv hIn hInOut hOut hq

theorem local_flow_distance_comparison_when_short (y : M.Carrier) (s t : ℝ)
    (hs : s ∈ Set.Icc a (a+2*τ)) (ht : t ∈ Set.Icc a (a+2*τ))
    (hy : inducedDistance (h s) q y < Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) :
    inducedDistance (h t) q y ≤
      Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2)*inducedDistance (h s) q y := by
  let Qfac := Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2)
  have hC : 0 < Qfac := Real.exp_pos _
  have hC2 : Qfac^2 = Real.exp ((σ*(2*n : ℕ)*K)*|t-s|) := by
    dsimp [Qfac]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ,hγ,hbuffer⟩ := exists_nearMinimizingCurve_in_buffer h p q y a K r τ σ rIn rOut s
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq hs hy (div_pos hε hC)
  have himage : ∀ u ∈ Set.Icc (0 : ℝ) 1, γ.1 u ∈ distBall (h a) p (2*r) := by
    intro u hu
    apply (mem_distBall_iff (h a) p (γ.1 u) (by positivity)).mpr
    exact (hbuffer u hu).trans_lt (by linarith)
  have hmetric : ∀ x ∈ distBall (h a) p (2*r), ∀ v : TangentVector M x,
      2*hermitianNormSq ((h t) x) v ≤ Qfac^2*(2*hermitianNormSq ((h s) x) v) := by
    intro x hx v
    rw [hC2]
    exact (local_flow_metric_comparison_between h p a K r τ σ hK hr hτ hσ
      hflow hcurv x hx s t hs ht v).2
  have H : ENNReal.ofReal (inducedDistance (h t) q y) ≤
      ENNReal.ofReal (Qfac*curveLength (h s) γ.1) := by
    have hdist := inducedDistance_le_fieldPathELength_piecewise (h t)
      (metricFamilySmooth_slice h hflow.1 ht) γ.1 (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    rw [γ.1.finish_eq] at hdist
    calc
      _ ≤ fieldPathELength (h t) γ.1 0 1 := hdist
      _ ≤ ENNReal.ofReal Qfac * fieldPathELength (h s) γ.1 0 1 :=
        fieldPathELength_upper_of_tangentNorm_upper (h s) (h t) _ Qfac hC.le hmetric γ.1 himage
      _ = _ := by rw [fieldPathELength_of_integrableCurve (h s) γ, ENNReal.ofReal_mul hC.le]
  have Hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC.le (curveLength_nonneg (h s) γ.1))).mp H
  have Hγ := mul_lt_mul_of_pos_left hγ hC
  have heq : Qfac*(inducedDistance (h s) q y + ε/Qfac) = Qfac*inducedDistance (h s) q y + ε := by
    field_simp
    <;> ring
  exact Hreal.trans (by rw [← heq]; exact Hγ.le)

theorem local_flow_clippedDistance_comparison (y : M.Carrier) (s t : ℝ)
    (hs : s ∈ Set.Icc a (a+2*τ)) (ht : t ∈ Set.Icc a (a+2*τ)) :
    min (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) (inducedDistance (h t) q y) ≤
      Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2) *
        min (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) (inducedDistance (h s) q y) := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  let Qfac := Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2)
  have hR : 0 < R := div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hInOut)) (by norm_num)
  have hC1 : 1 ≤ Qfac := by
    have H : Real.exp 0 ≤ Qfac := Real.exp_le_exp.mpr (by positivity)
    simpa only [Real.exp_zero] using H
  change min R (inducedDistance (h t) q y) ≤ Qfac * min R (inducedDistance (h s) q y)
  by_cases hy : inducedDistance (h s) q y < R
  · rw [min_eq_right hy.le]
    exact (min_le_right _ _).trans
      (local_flow_distance_comparison_when_short h p q a K r τ σ rIn rOut
        hK hr hτ hσ hflow hcurv hIn hInOut hOut hq y s t hs ht hy)
  · rw [min_eq_left (le_of_not_gt hy)]
    exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_right hC1 hR.le])

theorem local_flow_clippedDistance_time_abs_bound (y : M.Carrier) (s t : ℝ)
    (hs : s ∈ Set.Icc a (a+2*τ)) (ht : t ∈ Set.Icc a (a+2*τ)) :
    |min (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) (inducedDistance (h t) q y) -
      min (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) (inducedDistance (h s) q y)| ≤
      (Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2)-1)*
        (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  let Qfac := Real.exp ((σ*(2*n : ℕ)*K)*|t-s|/2)
  have hC1 : 1 ≤ Qfac := by
    have H : Real.exp 0 ≤ Qfac := Real.exp_le_exp.mpr (by positivity)
    simpa only [Real.exp_zero] using H
  have Hst := local_flow_clippedDistance_comparison h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq y s t hs ht
  have Hts := local_flow_clippedDistance_comparison h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq y t s ht hs
  rw [abs_sub_comm s t] at Hts
  change min R (inducedDistance (h t) q y) ≤ Qfac*min R (inducedDistance (h s) q y) at Hst
  change min R (inducedDistance (h s) q y) ≤ Qfac*min R (inducedDistance (h t) q y) at Hts
  have Hs := mul_le_mul_of_nonneg_left (min_le_left R (inducedDistance (h s) q y))
    (sub_nonneg.mpr hC1)
  have Ht := mul_le_mul_of_nonneg_left (min_le_left R (inducedDistance (h t) q y))
    (sub_nonneg.mpr hC1)
  change |min R (inducedDistance (h t) q y)-min R (inducedDistance (h s) q y)| ≤ (Qfac-1)*R
  apply abs_le.mpr
  constructor <;> nlinarith only [Hst,Hts,Hs,Ht]

theorem local_flow_clippedDistance_continuousOn :
    ContinuousOn (fun z : M.Carrier × ℝ =>
      min (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) (inducedDistance (h z.2) q z.1))
      (Set.univ ×ˢ Set.Icc a (a+2*τ)) := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  let c := σ*(2*n : ℕ)*K
  intro z hz
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : M.Carrier × ℝ → ℝ := fun w =>
    (Real.exp (c*|w.2-z.2|/2)-1)*R +
      |min R (inducedDistance (h z.2) q w.1)-min R (inducedDistance (h z.2) q z.1)|
  have hB : Continuous B := by
    have htime : Continuous (fun w : M.Carrier × ℝ => (Real.exp (c*|w.2-z.2|/2)-1)*R) :=
      ((Real.continuous_exp.comp
        ((continuous_const.mul (continuous_snd.sub continuous_const).abs).div_const 2)).sub
          continuous_const).mul continuous_const
    have hspace : Continuous (fun w : M.Carrier × ℝ =>
        |min R (inducedDistance (h z.2) q w.1)-min R (inducedDistance (h z.2) q z.1)|) :=
      ((continuous_const.min ((continuous_distFrom (h z.2)
        (metricFamilySmooth_slice h hflow.1 hz.2) q).comp continuous_fst)).sub continuous_const).abs
    exact htime.add hspace
  have hBz : B z = 0 := by simp only [B,sub_self,abs_zero,mul_zero,zero_div,
    Real.exp_zero,zero_mul,zero_add]
  have hnear : ∀ᶠ w in 𝓝 z, B w < ε :=
    hB.continuousAt.eventually (Iio_mem_nhds (hBz ▸ hε))
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwI
  have H := local_flow_clippedDistance_time_abs_bound h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq w.1 z.2 w.2 hz.2 hwI.2
  rw [Real.dist_eq]
  calc
    _ = |(min R (inducedDistance (h w.2) q w.1)-min R (inducedDistance (h z.2) q w.1)) +
      (min R (inducedDistance (h z.2) q w.1)-min R (inducedDistance (h z.2) q z.1))| := by
        congr 1
        ring
    _ ≤ |min R (inducedDistance (h w.2) q w.1)-min R (inducedDistance (h z.2) q w.1)| +
      |min R (inducedDistance (h z.2) q w.1)-min R (inducedDistance (h z.2) q z.1)| := abs_add_le _ _
    _ ≤ B w := add_le_add H le_rfl
    _ < ε := hw

end Flow

theorem timeDistanceCutoff_eq_clipped_profile (h : ℝ → HermitianField M)
    (q y : M.Carrier) {R t : ℝ} (hR : 0 < R) (hh : MetricSmooth (h t)) :
    timeDistanceCutoff h q R y t = (1-(min R (inducedDistance (h t) q y))^2/R^2)^2 := by
  have hd := inducedDistance_nonneg (h t) hh q y
  have hR2 := sq_pos_of_pos hR
  by_cases hy : inducedDistance (h t) q y ≤ R
  · have hs := (sq_le_sq₀ hd hR.le).mpr hy
    have ha : 0 ≤ 1-inducedDistance (h t) q y ^ 2/R^2 :=
      sub_nonneg.mpr ((div_le_one hR2).mpr hs)
    simp only [timeDistanceCutoff,min_eq_right hy,max_eq_right ha]
  · have hRy := le_of_not_ge hy
    have hs := (sq_le_sq₀ hR.le hd).mpr hRy
    have ha : 1-inducedDistance (h t) q y ^ 2/R^2 ≤ 0 :=
      sub_nonpos.mpr ((one_le_div hR2).mpr hs)
    simp only [timeDistanceCutoff,min_eq_left hRy,max_eq_left ha,zero_pow,
      OfNat.ofNat_ne_zero,ne_eq,not_false_eq_true,div_self hR2.ne',sub_self]

theorem timeDistanceCutoff_pos_iff (h : ℝ → HermitianField M)
    (q y : M.Carrier) {R t : ℝ} (hR : 0 < R) (hh : MetricSmooth (h t)) :
    0 < timeDistanceCutoff h q R y t ↔ inducedDistance (h t) q y < R := by
  have hd := inducedDistance_nonneg (h t) hh q y
  have hR2 := sq_pos_of_pos hR
  constructor
  · intro hpos
    by_contra hy
    have hs := (sq_le_sq₀ hR.le hd).mpr (le_of_not_gt hy)
    have ha : 1-inducedDistance (h t) q y ^ 2/R^2 ≤ 0 :=
      sub_nonpos.mpr ((one_le_div hR2).mpr hs)
    simp only [timeDistanceCutoff,max_eq_left ha,zero_pow,OfNat.ofNat_ne_zero,
      ne_eq,not_false_eq_true] at hpos
    exact lt_irrefl _ hpos
  · intro hy
    have hs := (sq_lt_sq₀ hd hR.le).mpr hy
    have ha : 0 < 1-inducedDistance (h t) q y ^ 2/R^2 :=
      sub_pos.mpr ((div_lt_one hR2).mpr hs)
    simpa only [timeDistanceCutoff,max_eq_right ha.le] using sq_pos_of_pos ha

section Flow
variable (h : ℝ → HermitianField M) (p q : M.Carrier) (a K r τ σ rIn rOut : ℝ)
  (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
  (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
  (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ u ∈ Set.Icc a (a+2*τ),
    curvatureJetNorm (h u) 0 x ≤ K)
  (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
  (hq : q ∈ distBall (h a) p rIn)
include p r hK hr hτ hσ hflow hcurv hIn hInOut hOut hq

theorem local_flow_timeDistanceCutoff_continuousOn :
    ContinuousOn (fun z : M.Carrier × ℝ =>
      timeDistanceCutoff h q (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) z.1 z.2)
      (Set.univ ×ˢ Set.Icc a (a+2*τ)) := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  have hR : 0 < R := div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hInOut)) (by norm_num)
  have hc := local_flow_clippedDistance_continuousOn h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq
  have hp : ContinuousOn (fun z : M.Carrier × ℝ =>
      (1-(min R (inducedDistance (h z.2) q z.1))^2/R^2)^2)
      (Set.univ ×ˢ Set.Icc a (a+2*τ)) :=
    (continuousOn_const.sub ((hc.pow 2).div_const (R^2))).pow 2
  apply hp.congr
  intro z hz
  exact timeDistanceCutoff_eq_clipped_profile h q z.1 hR (metricFamilySmooth_slice h hflow.1 hz.2)

theorem local_flow_timeDistanceCutoff_nonzero_mem_buffer
    (y : M.Carrier) (t : ℝ) (ht : t ∈ Set.Icc a (a+2*τ))
    (hη : timeDistanceCutoff h q
      (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) y t ≠ 0) :
    y ∈ fieldDistanceBuffer (h a) p rIn rOut := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  have hR : 0 < R := div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hInOut)) (by norm_num)
  have hpos := lt_of_le_of_ne (timeDistanceCutoff_nonneg h q R y t) hη.symm
  have hy := (timeDistanceCutoff_pos_iff h q y hR (metricFamilySmooth_slice h hflow.1 ht)).mp hpos
  obtain ⟨γ,_,hbuffer⟩ := exists_nearMinimizingCurve_in_buffer h p q y a K r τ σ rIn rOut t
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq ht hy (show (0 : ℝ) < 1 by norm_num)
  have H := hbuffer 1 (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
  simpa only [γ.1.finish_eq] using H

theorem local_flow_timeDistanceCutoff_spatialSupport_subset :
    closure {y | ∃ t ∈ Set.Icc a (a+2*τ), timeDistanceCutoff h q
      (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) y t ≠ 0} ⊆
        fieldDistanceBuffer (h a) p rIn rOut := by
  have ha : a ∈ Set.Icc a (a+2*τ) := ⟨le_rfl,by linarith⟩
  apply closure_minimal _ (isClosed_le
    (continuous_distFrom (h a) (metricFamilySmooth_slice h hflow.1 ha) p) continuous_const)
  rintro y ⟨t,ht,hη⟩
  exact local_flow_timeDistanceCutoff_nonzero_mem_buffer h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq y t ht hη

theorem local_flow_timeDistanceCutoff_spatialSupport_compact_interior
    (hcO : IsCompact (closure (distBall (h a) p (2*r)))) :
    let S := closure {y | ∃ t ∈ Set.Icc a (a+2*τ), timeDistanceCutoff h q
      (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) y t ≠ 0}
    IsCompact S ∧ S ⊆ distBall (h a) p (2*r) := by
  dsimp only
  have hsub := local_flow_timeDistanceCutoff_spatialSupport_subset h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq
  have ha : a ∈ Set.Icc a (a+2*τ) := ⟨le_rfl,by linarith⟩
  have hbuffer := fieldDistanceBuffer_isCompact (h a) (metricFamilySmooth_slice h hflow.1 ha)
    p hIn hInOut hOut hcO
  refine ⟨hbuffer.of_isClosed_subset isClosed_closure hsub, ?_⟩
  intro y hy
  apply (mem_distBall_iff (h a) p y (by positivity)).mpr
  exact (hsub hy).trans_lt (by linarith)

theorem local_flow_timeDistanceCutoff_zero_outside
    (y : M.Carrier) (hy : y ∉ distBall (h a) p (2*r))
    (t : ℝ) (ht : t ∈ Set.Icc a (a+2*τ)) :
    timeDistanceCutoff h q (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) y t = 0 := by
  by_contra hη
  have H := local_flow_timeDistanceCutoff_nonzero_mem_buffer h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq y t ht hη
  apply hy
  apply (mem_distBall_iff (h a) p y (by positivity)).mpr
  exact H.trans_lt (by linarith)

end Flow
end Yau.LeafProofs.L23Aux
