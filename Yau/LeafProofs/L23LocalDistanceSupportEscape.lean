import Yau.LeafProofs.L23LocalDistanceSupportBuffer

/-! Extended path lengths permit restriction to the first escape segment
without any new integrability assumption on that segment. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_first_level_hit {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hstart : f a < L) (hend : L ≤ f b) :
    ∃ u ∈ Set.Ioc a b, f u = L ∧ ∀ s ∈ Set.Icc a u, f s ≤ L := by
  let T : Set (Set.Icc a b) := {u | f u = L}
  have hTc : IsCompact T := (isClosed_eq hf.restrict continuous_const).isCompact
  have himage : IsCompact (Subtype.val '' T) := hTc.image continuous_subtype_val
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hab hf ⟨hstart.le, hend⟩
  have hne : (Subtype.val '' T).Nonempty := ⟨v, ⟨⟨v,hv⟩,hfv,rfl⟩⟩
  obtain ⟨u, hu⟩ := himage.exists_isLeast hne
  obtain ⟨u', hu', rfl⟩ := hu.1
  have huI := u'.2
  have huval : f u' = L := hu'
  have hau : a < (u' : ℝ) := by
    by_contra h
    have heq : (u' : ℝ) = a := le_antisymm (le_of_not_gt h) huI.1
    rw [heq] at huval
    linarith
  refine ⟨u', ⟨hau, huI.2⟩, huval, ?_⟩
  intro s hs
  by_contra h
  have hfs : L < f s := lt_of_not_ge h
  have hsu : s < (u' : ℝ) := by
    apply lt_of_le_of_ne hs.2
    intro heq
    rw [heq, huval] at hfs
    exact lt_irrefl _ hfs
  have hsub : Set.Icc a s ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl (hs.2.trans huI.2)
  obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc hs.1 (hf.mono hsub) ⟨hstart.le, hfs.le⟩
  have humin : (u' : ℝ) ≤ w := hu.2 ⟨⟨w,hsub hw⟩,hfw,rfl⟩
  linarith [hw.2]

def fieldPathSpeed (h : HermitianField M) (γ : ℝ → M.Carrier) (s : ℝ) : ℝ :=
  Real.sqrt (2 * hermitianNormSq (h (γ s))
    (realTangentEquiv (γ s) (realCurveVelocity γ s)))

def fieldPathELength (h : HermitianField M) (γ : ℝ → M.Carrier) (a b : ℝ) : ℝ≥0∞ := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  exact Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ a b

theorem fieldPathELength_eq_lintegral (h : HermitianField M) (γ : ℝ → M.Carrier) (a b : ℝ) :
    fieldPathELength h γ a b = ∫⁻ s in Set.Icc a b, ENNReal.ofReal (fieldPathSpeed h γ s) := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  rw [fieldPathELength, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro s
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖realCurveVelocity γ s‖ = _
  rw [underlyingRealTangent_norm]
  rfl

theorem fieldPathELength_mono (h : HermitianField M) (γ : ℝ → M.Carrier)
    {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    fieldPathELength h γ a b ≤ fieldPathELength h γ a' b' := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  exact Manifold.pathELength_mono ha hb

theorem fieldPathELength_of_integrableCurve (h : HermitianField M) {x y : M.Carrier}
    (γ : IntegrableCurve h x y) :
    fieldPathELength h γ.1 0 1 = ENNReal.ofReal (curveLength h γ.1) :=
  (curveLength_eq_pathELength h γ).symm

theorem fieldPathELength_lower_of_tangentNorm_lower
    (h₀ h₁ : HermitianField M) (O : Set M.Carrier) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x ∈ O, ∀ v : TangentVector M x,
      ell^2*(2*hermitianNormSq (h₀ x) v) ≤ 2*hermitianNormSq (h₁ x) v)
    (γ : ℝ → M.Carrier) {a b : ℝ} (himage : ∀ s ∈ Set.Icc a b, γ s ∈ O) :
    ENNReal.ofReal ell * fieldPathELength h₀ γ a b ≤ fieldPathELength h₁ γ a b := by
  rw [fieldPathELength_eq_lintegral, fieldPathELength_eq_lintegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have H := Real.sqrt_le_sqrt (hmetric (γ s) (himage s hs)
    (realTangentEquiv (γ s) (realCurveVelocity γ s)))
  rw [Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hell] at H
  rw [← ENNReal.ofReal_mul hell]
  exact ENNReal.ofReal_le_ofReal H

theorem inducedDistance_le_fieldPathELength_piecewise
    (h : HermitianField M) (hh : MetricSmooth h)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (inducedDistance h x (γ u)) ≤ fieldPathELength h γ 0 u := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup h z
  change ENNReal.ofReal (inducedDistance h x (γ u)) ≤
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 u
  rw [inducedDistance_eq_riemannianEDist h hh]
  have H := riemannianEDist_le_pathELength_of_finite_exceptions h hh γ.breakpoints hu.1
    (γ.continuous_on.mono (Set.Icc_subset_Icc le_rfl hu.2)) (fun s hs hnot => ?_)
  · simpa only [γ.start_eq] using H
  · rw [contMDiffAt_iff]
    refine ⟨γ.continuous_on.continuousAt (Icc_mem_nhds hs.1 (hs.2.trans_le hu.2)), ?_⟩
    simp only [real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
    convert! γ.piecewise_c1 s hnot using 1

/-- Every genuinely short admissible curve is confined to the fixed compact
middle buffer. The argument only compares metrics before its first exit. -/
theorem shortCurve_stays_in_fieldDistanceBuffer
    (h₀ h₁ : HermitianField M) (hh₀ : MetricSmooth h₀)
    (p q y : M.Carrier) {rIn rOut rBound ell : ℝ}
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ rBound)
    (hell : 0 < ell) (hq : q ∈ distBall h₀ p rIn)
    (hmetric : ∀ x ∈ distBall h₀ p rBound, ∀ v : TangentVector M x,
      ell^2*(2*hermitianNormSq (h₀ x) v) ≤ 2*hermitianNormSq (h₁ x) v)
    (γ : IntegrableCurve h₁ q y)
    (hshort : curveLength h₁ γ.1 < ell*(rOut-rIn)/2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, γ.1 s ∈ fieldDistanceBuffer h₀ p rIn rOut := by
  let f : ℝ → ℝ := fun s => inducedDistance h₀ p (γ.1 s)
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (continuous_distFrom h₀ hh₀ p).comp_continuousOn γ.1.continuous_on
  have hstart : f 0 < (rIn+rOut)/2 := by
    have H := (mem_distBall_iff h₀ p q hIn).mp hq
    dsimp [f]
    rw [γ.1.start_eq]
    linarith
  intro s hs
  by_contra hout
  have hfs : (rIn+rOut)/2 < f s := lt_of_not_ge hout
  obtain ⟨u, hu, hfu, hbefore⟩ := exists_first_level_hit hs.1
    (hf.mono (Set.Icc_subset_Icc le_rfl hs.2)) hstart hfs.le
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.trans hs.2⟩
  have himage : ∀ z ∈ Set.Icc (0 : ℝ) u, γ.1 z ∈ distBall h₀ p rBound := by
    intro z hz
    apply (mem_distBall_iff h₀ p (γ.1 z) ((hIn.trans hInOut).trans_le hOut)).mpr
    exact (hbefore z hz).trans_lt (by linarith)
  have hdist : (rOut-rIn)/2 < inducedDistance h₀ q (γ.1 u) :=
    initial_buffer_boundary_distance h₀ hh₀ p q (γ.1 u) hIn hq hfu
  have H : ENNReal.ofReal (ell * inducedDistance h₀ q (γ.1 u)) ≤
      ENNReal.ofReal (curveLength h₁ γ.1) := by
    calc
      _ = ENNReal.ofReal ell * ENNReal.ofReal (inducedDistance h₀ q (γ.1 u)) :=
        ENNReal.ofReal_mul hell.le
      _ ≤ ENNReal.ofReal ell * fieldPathELength h₀ γ.1 0 u :=
        mul_le_mul' le_rfl (inducedDistance_le_fieldPathELength_piecewise h₀ hh₀ γ.1 hu01)
      _ ≤ fieldPathELength h₁ γ.1 0 u :=
        fieldPathELength_lower_of_tangentNorm_lower h₀ h₁ _ ell hell.le hmetric γ.1 himage
      _ ≤ fieldPathELength h₁ γ.1 0 1 := fieldPathELength_mono h₁ γ.1 le_rfl hu01.2
      _ = _ := fieldPathELength_of_integrableCurve h₁ γ
  have Hreal := (ENNReal.ofReal_le_ofReal_iff (curveLength_nonneg h₁ γ.1)).mp H
  have Hdist := mul_lt_mul_of_pos_left hdist hell
  nlinarith only [Hreal, Hdist, hshort]


theorem local_flow_shortCurve_stays_in_buffer
    (h : ℝ → HermitianField M) (p q y : M.Carrier) (a K r τ σ rIn rOut t : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ s ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h s) 0 x ≤ K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
    (hq : q ∈ distBall (h a) p rIn) (ht : t ∈ Set.Icc a (a+2*τ))
    (γ : IntegrableCurve (h t) q y)
    (hshort : curveLength (h t) γ.1 < Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, γ.1 s ∈ fieldDistanceBuffer (h a) p rIn rOut := by
  let ell := Real.exp (-σ*(2*n : ℕ)*K*τ)
  have hell : 0 < ell := Real.exp_pos _
  have hellSq : ell^2 = Real.exp (-2*σ*(2*n : ℕ)*K*τ) := by
    dsimp [ell]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have ha : a ∈ Set.Icc a (a+2*τ) := ⟨le_rfl, by linarith⟩
  apply shortCurve_stays_in_fieldDistanceBuffer (h a) (h t)
    (metricFamilySmooth_slice h hflow.1 ha) p q y hIn hInOut hOut hell hq _ γ hshort
  intro x hx v
  rw [hellSq]
  exact (local_flow_metric_comparison h p a K r τ σ hK hr hτ hσ hflow hcurv x hx t ht v).1

theorem exists_nearMinimizingCurve_in_buffer
    (h : ℝ → HermitianField M) (p q y : M.Carrier) (a K r τ σ rIn rOut t : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ s ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h s) 0 x ≤ K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
    (hq : q ∈ distBall (h a) p rIn) (ht : t ∈ Set.Icc a (a+2*τ))
    (hy : inducedDistance (h t) q y < Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : IntegrableCurve (h t) q y,
      curveLength (h t) γ.1 < inducedDistance (h t) q y + ε ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, γ.1 s ∈ fieldDistanceBuffer (h a) p rIn rOut := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  have hR : 0 < R := div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hInOut)) (by norm_num)
  obtain ⟨γ, hγ⟩ := exists_nearMinimizingCurve (h t) (metricFamilySmooth_slice h hflow.1 ht)
    q y (lt_min hε hR)
  refine ⟨γ, hγ.trans_le (add_le_add le_rfl (min_le_left ε R)), ?_⟩
  apply local_flow_shortCurve_stays_in_buffer h p q y a K r τ σ rIn rOut t
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq ht γ
  have H := hγ.trans_le (add_le_add le_rfl (min_le_right ε R))
  change inducedDistance (h t) q y < R at hy
  dsimp [R] at *
  linarith

end Yau.LeafProofs.L23Aux
