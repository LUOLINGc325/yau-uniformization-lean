import Yau.LeafProofs.L19GaussianWeightInterior
import Yau.LeafProofs.L19LocalizationCalculus

/-! Comparison of the actual Gaussian with smooth nonnegative heat flows. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem gaussian_secondFDeriv_const_mul_sub
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z)
    (c : ℝ) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y => c * f y - k y)) z v w =
      c * fderiv ℝ (fderiv ℝ f) z v w -
        fderiv ℝ (fderiv ℝ k) z v w := by
  have hcf : ContDiffAt ℝ 2 (fun y => c * f y) z := contDiffAt_const.mul hf
  have hneg : ContDiffAt ℝ 2 (fun y => -k y) z := hk.neg
  have hadd := secondFDeriv_add_local hcf hneg v w
  have hfun : (fun y => c * f y - k y) =
      (fun y => c * f y + -k y) := by funext y; ring
  rw [hfun, hadd]
  have hnegf : fderiv ℝ (fun y => -k y) = fun y => -fderiv ℝ k y := by
    funext y; exact fderiv_fun_neg
  have hscalef : fderiv ℝ (fun y => c * f y) = fun y => c • fderiv ℝ f y := by
    funext y
    change fderiv ℝ (c • f) y = _
    exact congrFun (fderiv_const_smul_field c) y
  have hscale2 : fderiv ℝ (fun y => c • fderiv ℝ f y) z =
      c • fderiv ℝ (fderiv ℝ f) z := by
    change fderiv ℝ (c • fderiv ℝ f) z = _
    exact congrFun (fderiv_const_smul_field
      (f := (fderiv ℝ f : ComplexVector n → ComplexVector n →L[ℝ] ℝ)) c) z
  rw [hnegf, hscalef]
  rw [hscale2]
  simp only [fderiv_fun_neg, smul_apply, smul_eq_mul, neg_apply]
  ring

private theorem gaussian_chartRealLaplacian_const_mul_sub
    (g : SmoothMetric M) (hK : IsKahler g) (q : M.Carrier)
    {f k : ComplexVector n → ℝ}
    (hf : ContDiffAt ℝ 2 f (chartPt q q))
    (hk : ContDiffAt ℝ 2 k (chartPt q q)) (c : ℝ) :
    chartRealLaplacian g.form q (fun z => c * f z - k z) (chartPt q q) =
      c * chartRealLaplacian g.form q f (chartPt q q) -
        chartRealLaplacian g.form q k (chartPt q q) := by
  have hz : chartPt q q ∈ chartTarget q := mem_extChartAt_target q
  rw [chartRealLaplacian_eq_principal g hK q hz,
    chartRealLaplacian_eq_principal g hK q hz,
    chartRealLaplacian_eq_principal g hK q hz]
  simp only [L18Aux.rDeriv_rDeriv_eq_hessian (contDiffAt_const.mul hf |>.sub hk),
    L18Aux.rDeriv_rDeriv_eq_hessian hf, L18Aux.rDeriv_rDeriv_eq_hessian hk]
  simp only [gaussian_secondFDeriv_const_mul_sub hf hk, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_left_comm, Finset.mul_sum]

/-- A positive-time maximum of the Gaussian comparison defect contradicts
the physical trace bound on a true C² lower support. -/
theorem gaussian_comparison_no_local_max
    (g : SmoothMetric M) (hK : IsKahler g)
    (o : M.Carrier) {a C ε t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (q : M.Carrier)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hheat : HasDerivAt (u q)
      (laplacian g.form (fun y => u y t) q) t)
    (hS : ∃ S : M.Carrier → ℝ,
      ∃ b : letI := underlyingRealTangentNormedAddCommGroup g.form q
        letI := underlyingRealTangentInnerProductSpace g.form q
        OrthonormalBasis (Fin (2 * n)) ℝ
          (TangentSpace 𝓘(ℝ, ComplexVector n) q),
        ContDiffAt ℝ 2 (S ∘ chartInv q) (chartPt q q) ∧
        S q = gaussianWeight g o a q ∧
        -2 * C * gaussianWeight g o a q ≤
          endpointFrameHessianTrace g q b (S ∘ chartInv q) (chartPt q q) ∧
        IsLocalMax (fun z => Real.exp (-(C * t)) * S (chartInv q z) -
          u (chartInv q z) t) (chartPt q q))
    (htmax : IsLocalMaxOn
      (fun r => Real.exp (-(C * r)) * gaussianWeight g o a q -
        u q r - ε * (1 + r)) (Set.Iic t) t) : False := by
  obtain ⟨S, b, hS2, hSq, hStrace, hspacemax⟩ := hS
  have hepos : 0 < Real.exp (-(C * t)) := Real.exp_pos _
  have huSlice : SmoothFn (fun y => u y t) := smoothSpaceTime_slice hu ht
  have hu2 : ContDiffAt ℝ 2 (inChart q (fun y => u y t)) (chartPt q q) :=
    (contDiffAt_inChart huSlice q (mem_extChartAt_target q)).of_le (by simp)
  have hspace : chartRealLaplacian g.form q
      (fun z => Real.exp (-(C * t)) * S (chartInv q z) - u (chartInv q z) t)
      (chartPt q q) ≤ 0 :=
    chartRealLaplacian_nonpos_at_local_max g q
      ((contDiffAt_const.mul hS2).sub hu2) hspacemax
  change chartRealLaplacian g.form q
    (fun z => Real.exp (-(C * t)) * (S ∘ chartInv q) z -
      inChart q (fun y => u y t) z) (chartPt q q) ≤ 0 at hspace
  rw [gaussian_chartRealLaplacian_const_mul_sub g hK q hS2 hu2] at hspace
  have htrace : -2 * C * gaussianWeight g o a q ≤
      chartRealLaplacian g.form q (S ∘ chartInv q) (chartPt q q) := by
    rw [chartRealLaplacian_eq_orthonormal_covHessian g.form q hS2 b]
    exact hStrace
  have huLap : chartRealLaplacian g.form q
      (inChart q (fun y => u y t)) (chartPt q q) =
      2 * laplacian g.form (fun y => u y t) q :=
    kahler_realLaplacian_center_eq g hK huSlice q
  have hspatial : -C * Real.exp (-(C * t)) * gaussianWeight g o a q ≤
      laplacian g.form (fun y => u y t) q := by
    rw [huLap] at hspace
    have hmul := mul_le_mul_of_nonneg_left htrace hepos.le
    nlinarith only [hspace, hmul]
  have he : HasDerivAt (fun r : ℝ => Real.exp (-(C * r)))
      (-C * Real.exp (-(C * t))) t := gaussianProfile_hasDerivAt C t
  have hd : HasDerivAt
      (fun r => Real.exp (-(C * r)) * gaussianWeight g o a q - u q r -
        ε * (1 + r))
      (-C * Real.exp (-(C * t)) * gaussianWeight g o a q -
        laplacian g.form (fun y => u y t) q - ε) t := by
    convert ((he.mul_const (gaussianWeight g o a q)).sub hheat).sub
      ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t) |>.const_mul ε) using 1
    all_goals try { funext r; dsimp }
    all_goals ring
  have htime := hasDerivAt_nonneg_at_left_max hd htmax
  linarith

/-- A positive Gaussian tends to zero along distance radii. -/
theorem gaussianWeight_small_far (g : SmoothMetric M) (o : M.Carrier)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : M.Carrier,
      R ≤ inducedDistance g.form o y → gaussianWeight g o a y < ε := by
  have hrad : Tendsto (fun r : ℝ => Real.exp (-(a * r ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) ha)
  obtain ⟨R₀, hR₀⟩ := (Filter.eventually_atTop.1 (hrad.eventually (Iio_mem_nhds hε)))
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact hR₀ _ ((le_max_left _ _).trans hy)

/-- The Gaussian lower-support bound yields a genuine global heat comparison
for any nonnegative classical heat flow with uniform Gaussian initial trace. -/
theorem gaussianWeight_heat_comparison_fraction
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 < a)
    {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hu_nonneg : ∀ y t, 0 < t → 0 ≤ u y t)
    (hu_heat : ∀ y t, 0 < t → HasDerivAt (u y)
      (laplacian g.form (fun z => u z t) y) t)
    (hu_initial : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → ∀ y : M.Carrier,
        |u y t - gaussianWeight g o a y| < η)
    (x : M.Carrier) {T : ℝ} (hT : 0 < T) :
    Real.exp (-(((2 * n : ℕ) : ℝ) * a / (1 - σ) * T)) *
        gaussianWeight g o a x ≤ u x T := by
  let C : ℝ := ((2 * n : ℕ) : ℝ) * a / (1 - σ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ha.le) (sub_nonneg.mpr hσ.2.le)
  have hW : ∀ y : M.Carrier, 0 ≤ gaussianWeight g o a y :=
    fun y => (gaussianWeight_pos g o a y).le
  have hexp_le (r : ℝ) (hr : 0 ≤ r) : Real.exp (-(C * r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hC hr))
  by_contra hgoal
  have hgap : 0 < Real.exp (-(C * T)) * gaussianWeight g o a x - u x T := by
    dsimp [C] at hgoal ⊢
    exact sub_pos.mpr (lt_of_not_ge hgoal)
  let ε : ℝ := (Real.exp (-(C * T)) * gaussianWeight g o a x - u x T) /
    (2 * (1 + T))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let W : M.Carrier → ℝ → ℝ := fun y r =>
    Real.exp (-(C * r)) * gaussianWeight g o a y - u y r - ε * (1 + r)
  have hxW : 0 < W x T := by
    dsimp [W, ε]
    have hden : 0 < 2 * (1 + T) := by positivity
    have hfrac : (Real.exp (-(C * T)) * gaussianWeight g o a x - u x T) /
        (2 * (1 + T)) * (1 + T) =
        (Real.exp (-(C * T)) * gaussianWeight g o a x - u x T) / 2 := by
      field_simp
    rw [hfrac]
    linarith
  obtain ⟨δ, hδ, hinit⟩ := hu_initial (ε / 2) (by positivity)
  let τ : ℝ := min T δ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτT : τ < T := by dsimp [τ]; have := min_le_left T δ; linarith
  have hτδ : τ < δ := by dsimp [τ]; have := min_le_right T δ; linarith
  have hstart (y : M.Carrier) : W y τ < 0 := by
    have h := hinit τ hτ hτδ y
    rw [abs_lt] at h
    have he := hexp_le τ hτ.le
    have hmul := mul_le_mul_of_nonneg_right he (hW y)
    dsimp [W]
    nlinarith only [h.1, h.2, hmul, hε, hτ]
  obtain ⟨R₀, hR₀, hfar⟩ := gaussianWeight_small_far g o ha hε
  let R : ℝ := max R₀ (inducedDistance g.form o x) + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left R₀ (inducedDistance g.form o x)]
  have hxR : inducedDistance g.form o x ≤ R := by
    dsimp [R]; linarith [le_max_right R₀ (inducedDistance g.form o x)]
  have hboundary (y : M.Carrier) (hy : R₀ ≤ inducedDistance g.form o y)
      (r : ℝ) (hr : 0 ≤ r) (hrt : 0 < r) : W y r < 0 := by
    have hh := hfar y hy
    have he := hexp_le r hr
    have hmu := mul_le_mul_of_nonneg_right he (hW y)
    have hposu := hu_nonneg y r hrt
    dsimp [W]
    nlinarith only [hh, hmu, hposu, hε, hr]
  let K : Set M.Carrier := {y | inducedDistance g.form o y ≤ R}
  let J : Set ℝ := Set.Icc τ T
  have hcompact : IsCompact (K ×ˢ J) :=
    (isCompact_inducedDistance_sublevel g o R).prod isCompact_Icc
  have hWcont : Continuous (fun p : M.Carrier × ℝ =>
      Real.exp (-(C * p.2)) * gaussianWeight g o a p.1) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_snd).neg)).mul
      ((gaussianWeight_continuous g o a).comp continuous_fst)
  have htimecont : Continuous (fun p : M.Carrier × ℝ => ε * (1 + p.2)) :=
    continuous_const.mul (continuous_const.add continuous_snd)
  have hWcontOn : ContinuousOn (fun p : M.Carrier × ℝ => W p.1 p.2)
      (K ×ˢ J) := by
    intro p hp
    have hpt : 0 < p.2 := hτ.trans_le hp.2.1
    exact ((hWcont.continuousAt.sub (smoothSpaceTime_continuousAt hu p.1 hpt)).sub
      htimecont.continuousAt).continuousWithinAt
  have hxmem : (x, T) ∈ K ×ˢ J := ⟨hxR, hτT.le, le_rfl⟩
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn (f := fun p => W p.1 p.2)
    ⟨(x, T), hxmem⟩ hWcontOn
  let q : M.Carrier := p.1
  let t : ℝ := p.2
  have hq : inducedDistance g.form o q ≤ R := hp.1
  have htI : t ∈ Set.Icc τ T := hp.2
  have ht : 0 < t := hτ.trans_le htI.1
  have hmaxall (y : M.Carrier) (r : ℝ)
      (hy : inducedDistance g.form o y ≤ R) (hr : r ∈ Set.Icc τ T) :
      W y r ≤ W q t := by
    exact hmax (show (y, r) ∈ K ×ˢ J from ⟨hy, hr⟩)
  have hmaxpos : 0 < W q t := (hxW.trans_le (hmaxall x T hxR ⟨hτT.le, le_rfl⟩))
  have hqinner : inducedDistance g.form o q < R := by
    by_contra hh
    have hqe : inducedDistance g.form o q = R := le_antisymm hq (le_of_not_gt hh)
    have hfarq : R₀ ≤ inducedDistance g.form o q := by
      dsimp [R] at hqe
      linarith [le_max_left R₀ (inducedDistance g.form o x)]
    exact (not_lt_of_ge hmaxpos.le) (hboundary q hfarq t ht.le ht)
  have htinner : τ < t := by
    by_contra hh
    have hteq : t = τ := le_antisymm (le_of_not_gt hh) htI.1
    rw [hteq] at hmaxpos
    exact (not_lt_of_ge hmaxpos.le) (hstart q)
  obtain ⟨S, b, hS2, hSq, hlower, htrace⟩ :=
    gaussianWeight_hasPhysicalLowerSupports_fraction g hK hRic o ha.le hσ q
  have htrace' : -2 * C * gaussianWeight g o a q ≤
      endpointFrameHessianTrace g q b (S ∘ chartInv q) (chartPt q q) := by
    convert htrace using 1
    dsimp [C]
    ring
  have hspacemax : IsLocalMax
      (fun z => Real.exp (-(C * t)) * S (chartInv q z) - u (chartInv q z) t)
      (chartPt q q) := by
    have hqmax : IsLocalMax (fun y => Real.exp (-(C * t)) * S y - u y t) q := by
      have hnear := (continuous_distFrom g o).continuousAt.eventually
        (Iio_mem_nhds hqinner)
      have hepos : 0 ≤ Real.exp (-(C * t)) := (Real.exp_pos _).le
      filter_upwards [hnear, hlower] with y hy hSy
      have hcomp := mul_le_mul_of_nonneg_left hSy hepos
      have hmax' := hmaxall y t hy.le htI
      dsimp [W] at hmax'
      rw [hSq]
      linarith
    have hqinv : chartInv q (chartPt q q) = q :=
      (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
    have hc : ContinuousAt (chartInv q) (chartPt q q) :=
      continuousAt_extChartAt_symm'' (I := ComplexModel n) (mem_extChartAt_target q)
    have htend : Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 q) := by
      simpa only [hqinv] using hc.tendsto
    change ∀ᶠ z in 𝓝 (chartPt q q), _ ≤ _
    simpa only [hqinv] using htend.eventually hqmax
  have htimemax : IsLocalMaxOn (W q) (Set.Iic t) t := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htinner),
      self_mem_nhdsWithin] with r hr hrle
    have hrt : r ∈ Set.Icc τ T := ⟨(show τ < r from hr).le,
      (show r ≤ t from hrle).trans htI.2⟩
    exact hmaxall q r hq hrt
  exact gaussian_comparison_no_local_max g hK o hε ht q hu
    (hu_heat q t ht) ⟨S, b, hS2, hSq, htrace', hspacemax⟩ htimemax

/-- Sending the interior anchor to the Gaussian center recovers the sharp
complex heat exponent `2na`. -/
theorem gaussianWeight_heat_comparison_sharp
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    (o : M.Carrier) {a : ℝ} (ha : 0 < a)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hu_nonneg : ∀ y t, 0 < t → 0 ≤ u y t)
    (hu_heat : ∀ y t, 0 < t → HasDerivAt (u y)
      (laplacian g.form (fun z => u z t) y) t)
    (hu_initial : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → ∀ y : M.Carrier,
        |u y t - gaussianWeight g o a y| < η)
    (x : M.Carrier) {T : ℝ} (hT : 0 < T) :
    Real.exp (-((2 * n : ℕ) * a * T)) * gaussianWeight g o a x ≤ u x T := by
  have hc : ContinuousAt (fun σ : ℝ =>
      Real.exp (-((2 * n : ℕ) * a / (1 - σ) * T)) *
        gaussianWeight g o a x) 0 := by
    have hden : ContinuousAt (fun σ : ℝ => 1 - σ) 0 :=
      continuousAt_const.sub continuousAt_id
    have hq : ContinuousAt (fun σ : ℝ => (2 * n : ℕ) * a / (1 - σ)) 0 :=
      continuousAt_const.div hden (by norm_num)
    exact (Real.continuous_exp.continuousAt.comp
      ((hq.mul continuousAt_const).neg)).mul continuousAt_const
  have hlim : Tendsto (fun σ : ℝ =>
      Real.exp (-((2 * n : ℕ) * a / (1 - σ) * T)) *
        gaussianWeight g o a x) (𝓝[>] 0)
      (𝓝 (Real.exp (-((2 * n : ℕ) * a * T)) * gaussianWeight g o a x)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with σ hσ0 hσ1
  exact gaussianWeight_heat_comparison_fraction g hK hRic o ha ⟨hσ0, hσ1⟩
    hu hu_nonneg hu_heat hu_initial x hT

end Yau.LeafProofs.L19Aux
