import Yau.Proofs.P08HeatBarrierMaximum

/-! Genuine finite-ball comparison with a Gaussian lower-support subsolution.
No smoothness of the metric sphere or Dirichlet solution is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem gaussian_finite_ball_supersolution (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ y, (ricci g.form y).PosSemidef) (o : M.Carrier)
    {a R σ : ℝ} (ha : 0 < a) (hR : 0 < R) (hσ : σ ∈ Set.Ioo 0 1)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hu_super : ∀ y s, 0 < s → laplacian g.form (fun z => u z s) y ≤ deriv (u y) s)
    (hu_initial : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, 0 < s → s < δ → ∀ y : M.Carrier,
        inducedDistance g.form o y ≤ R → 1 - η ≤ u y s)
    (hu_boundary : ∀ y : M.Carrier, inducedDistance g.form o y = R → ∀ s : ℝ, 0 < s →
      Real.exp (-(((2 * n : ℕ) : ℝ) * a / (1 - σ) * s)) * gaussianWeight g o a y ≤ u y s)
    (x : M.Carrier) (hxR : inducedDistance g.form o x ≤ R) {T : ℝ} (hT : 0 < T) :
    Real.exp (-(((2 * n : ℕ) : ℝ) * a / (1 - σ) * T)) * gaussianWeight g o a x ≤ u x T := by
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
  have hstart (y : M.Carrier) (hy : inducedDistance g.form o y ≤ R) : W y τ < 0 := by
    have h := hinit τ hτ hτδ y hy
    have he := hexp_le τ hτ.le
    have hmul := mul_le_mul_of_nonneg_right he (hW y)
    have hgauss : gaussianWeight g o a y ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))
    dsimp only [W]
    nlinarith
  have hboundaryW (y : M.Carrier) (hy : inducedDistance g.form o y = R)
      (r : ℝ) (hr : 0 < r) : W y r < 0 := by
    have h := hu_boundary y hy r hr
    change Real.exp (-(C * r)) * gaussianWeight g o a y ≤ u y r at h
    dsimp only [W]
    nlinarith
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
    exact (not_lt_of_ge hmaxpos.le) (hboundaryW q hqe t ht)
  have htinner : τ < t := by
    by_contra hh
    have hteq : t = τ := le_antisymm (le_of_not_gt hh) htI.1
    rw [hteq] at hmaxpos
    exact (not_lt_of_ge hmaxpos.le) (hstart q hq)
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
  have hd : HasDerivAt (u q) (deriv (u q) t) t :=
    ((smoothSpaceTime_time_contDiffAt hu q (Ioi_mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  exact gaussian_supersolution_no_local_max g hK o hε ht q hu hd
    (hu_super q t ht) ⟨S, b, hS2, hSq, htrace', hspacemax⟩ htimemax


end Yau.NodeProofs.P08Aux
