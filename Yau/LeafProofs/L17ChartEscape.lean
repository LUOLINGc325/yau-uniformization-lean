import Yau.LeafProofs.L17ChartDistance

/-! Quantitative escape from a uniform holomorphic chart, by path lengths. -/

noncomputable section

open Set Metric Filter MeasureTheory Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def realInverseCoordinateDifferential
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (q : M.Carrier) :
    TangentSpace 𝓘(ℝ, ComplexVector n) q →L[ℝ] ComplexVector n :=
  (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) (e.symm q)).toContinuousLinearMap ∘L
    mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) e.symm q

theorem BoundedChartFamily.inverseCoordinateDifferential_norm_le
    {g : HermitianField M} (A : BoundedChartFamily g) (p q : M.Carrier)
    (hq : q ∈ A.chart p '' ball 0 A.radius)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) q) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g q
    ‖realInverseCoordinateDifferential (A.chart p) q v‖ ≤
      (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ * ‖v‖ := by
  rcases hq with ⟨z, hz, rfl⟩
  convert! A.inverseFrame_norm_le p hz v using 1

theorem BoundedChartFamily.inverseCoordinateDifferential_enorm_le
    {g : HermitianField M} (A : BoundedChartFamily g) (p q : M.Carrier)
    (hq : q ∈ A.chart p '' ball 0 A.radius)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) q) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g q
    ‖realInverseCoordinateDifferential (A.chart p) q v‖ₑ ≤
      ENNReal.ofReal ((Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹) * ‖v‖ₑ := by
  let := L12Aux.underlyingRealTangentNormedAddCommGroup g q
  have hD : 0 ≤ (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (A.inverseCoordinateDifferential_norm_le p q hq v)

/-- A path shorter than the coordinate escape budget cannot leave the chart ball. -/
theorem BoundedChartFamily.closedChartBall_contains_distance_ball
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hq : inducedDistance g p q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    q ∈ A.chart p '' closedBall 0 ρ := by
  let := L12Aux.manifold_realSmooth M
  let : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentNormedAddCommGroup g x
  let : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentInnerProductSpace g x
  let e := A.chart p
  let D := (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹
  have hC := A.bound_pos 0
  have hD : 0 < D := by dsimp [D]; positivity
  have hbudget : inducedDistance g p q < ρ / D := by
    simpa only [D, div_inv_eq_mul, mul_comm] using hq
  have hED : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) p q <
      ENNReal.ofReal (ρ / D) := by
    rw [← L23Aux.inducedDistance_eq_riemannianEDist g hg]
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hρ hD)).mpr hbudget
  obtain ⟨γ, hγp, hγq, hγsmooth, hγlen, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hED zero_lt_one
  have hsource : closedBall (0 : ComplexVector n) ρ ⊆ e.source := by
    intro z hz
    apply A.closedBall_source p
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans hρr.le)
  let u := e '' closedBall (0 : ComplexVector n) ρ
  let v := e '' ball (0 : ComplexVector n) ρ
  have huclosed : IsClosed u :=
    ((isCompact_closedBall (0 : ComplexVector n) ρ).image_of_continuousOn
      (e.continuousOn.mono hsource)).isClosed
  have hvopen : IsOpen v := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hsource)
  have hvu : v ⊆ u := image_mono ball_subset_closedBall
  have hutarget : u ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hsource hz)
  have huBG : u ⊆ e '' ball 0 A.radius := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, (mem_closedBall.mp hz).trans_lt hρr, rfl⟩
  let B := γ ⁻¹' u
  have zero_mem : 0 ∈ B := by
    change γ 0 ∈ u
    rw [hγp]
    exact ⟨0, mem_closedBall_self hρ.le, A.center p⟩
  have hBclosed : IsClosed (B ∩ Icc 0 1) :=
    (huclosed.preimage hγsmooth.continuous).inter isClosed_Icc
  suffices Icc (0 : ℝ) 1 ⊆ B by
    have hone : γ 1 ∈ u := this (right_mem_Icc.mpr zero_le_one)
    simpa only [hγq] using hone
  apply hBclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset zero_mem
  rintro t₁ ⟨ht₁0, ht₁1⟩ hstay
  suffices γ t₁ ∈ v from
    hγsmooth.continuous.continuousWithinAt (mem_of_superset (hvopen.mem_nhds this) hvu)
  let γ' := e.symm ∘ γ
  have hcoord : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ' (Icc 0 t₁) :=
    ((inverse_chart_real_contMDiffOn e (A.inverse_differentiable p)).of_le (by simp)).comp
      hγsmooth.contMDiffOn (fun t ht => hutarget (hstay ht))
  have hnorm : ‖γ' t₁ - γ' 0‖ₑ < ENNReal.ofReal ρ := by
    rcases ht₁0.eq_or_lt with rfl | htpos
    · simpa using (ENNReal.ofReal_pos.mpr hρ)
    calc
      ‖γ' t₁ - γ' 0‖ₑ ≤ ∫⁻ t in Icc 0 t₁, ‖derivWithin γ' (Icc 0 t₁) t‖ₑ := by
        apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ ht₁0
        rwa [← contMDiffOn_iff_contDiffOn]
      _ ≤ ∫⁻ t in Icc 0 t₁,
          ENNReal.ofReal D * ‖mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
            γ (Icc 0 t₁) t 1‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        have heAt := ((inverse_chart_real_contMDiffOn e (A.inverse_differentiable p))
          (γ t) (hutarget (hstay ht))).contMDiffAt
            (e.open_target.mem_nhds (hutarget (hstay ht)))
        have hchain : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ' (Icc 0 t₁) t =
            (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) e.symm (γ t)).comp
              (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ (Icc 0 t₁) t) := by
          apply mfderiv_comp_mfderivWithin
          · exact heAt.mdifferentiableAt (by simp)
          · exact (hγsmooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc htpos t ht
        have heval := congrArg (fun L => L 1) hchain
        rw [mfderivWithin_eq_fderivWithin] at heval
        have hnative : derivWithin γ' (Icc 0 t₁) t =
            realInverseCoordinateDifferential e (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ (Icc 0 t₁) t 1) := by
          rw [← fderivWithin_derivWithin]
          convert! heval using 1
        rw [hnative]
        exact A.inverseCoordinateDifferential_enorm_le p (γ t) (huBG (hstay ht)) _
      _ = ENNReal.ofReal D * Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 t₁ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
      _ ≤ ENNReal.ofReal D * Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 := by gcongr
      _ < ENNReal.ofReal D * ENNReal.ofReal (ρ / D) := by
        gcongr
        · exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ρ := by
        rw [← ENNReal.ofReal_mul hD.le]
        congr 1
        field_simp
  have hcoord0 : γ' 0 = 0 := by
    change e.symm (γ 0) = 0
    rw [hγp, ← A.center p]
    exact e.left_inv (hsource (mem_closedBall_self hρ.le))
  have hnormreal : ‖e.symm (γ t₁)‖ < ρ := by
    apply (ENNReal.ofReal_lt_ofReal_iff hρ).mp
    simpa only [hcoord0, sub_zero, ofReal_norm, γ', Function.comp_apply] using hnorm
  exact ⟨e.symm (γ t₁), by simpa using hnormreal,
    e.right_inv (hutarget (hstay (right_mem_Icc.mpr ht₁0)))⟩

theorem BoundedChartFamily.chartBall_contains_distance_ball
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hq : inducedDistance g p q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    q ∈ A.chart p '' ball 0 ρ := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ inducedDistance g p q / c :=
    div_nonneg (L23Aux.inducedDistance_nonneg g hg p q) hc.le
  have hlt : inducedDistance g p q / c < ρ :=
    (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hq)
  let σ := (ρ + inducedDistance g p q / c) / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσρ : σ < ρ := by dsimp [σ]; linarith
  have hbudget : inducedDistance g p q < c * σ := by
    have hdiv : inducedDistance g p q / c < σ := by dsimp [σ]; linarith
    exact ((div_lt_iff₀ hc).mp hdiv).trans_eq (mul_comm σ c)
  obtain ⟨z, hz, hqz⟩ := A.closedChartBall_contains_distance_ball hg p q hσ
    (hσρ.trans hρr) hbudget
  exact ⟨z, (mem_closedBall.mp hz).trans_lt hσρ, hqz⟩

/-- Small intrinsic balls have the original quantitative coordinate bound. -/
theorem BoundedChartFamily.coordinate_norm_le_distance
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < A.radius)
    (hq : inducedDistance g p q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    ‖(A.chart p).symm q‖ ≤
      (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹ * inducedDistance g p q := by
  let c := Real.sqrt (2 * (A.bound 0)⁻¹)
  have hC := A.bound_pos 0
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ inducedDistance g p q / c :=
    div_nonneg (L23Aux.inducedDistance_nonneg g hg p q) hc.le
  have hqcoord : ‖(A.chart p).symm q‖ < ρ := by
    obtain ⟨z, hz, hqz⟩ := A.chartBall_contains_distance_ball hg p q hρ hρr hq
    have hs : z ∈ (A.chart p).source := A.closedBall_source p
      (mem_closedBall.mpr ((mem_ball.mp hz).le.trans hρr.le))
    have hinv : (A.chart p).symm q = z := by rw [← hqz]; exact (A.chart p).left_inv hs
    rw [hinv]
    simpa using hz
  suffices ‖(A.chart p).symm q‖ ≤ inducedDistance g p q / c by
    simpa only [div_eq_inv_mul, c] using this
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  by_cases hbρ : b < ρ
  · have hbp : 0 < b := hd.trans_lt hb
    have hbudget : inducedDistance g p q < c * b :=
      (div_lt_iff₀ hc).mp hb |>.trans_eq (mul_comm b c)
    obtain ⟨z, hz, hqz⟩ := A.closedChartBall_contains_distance_ball hg p q hbp
      (hbρ.trans hρr) hbudget
    have hs : z ∈ (A.chart p).source := A.closedBall_source p
      (mem_closedBall.mpr ((mem_closedBall.mp hz).trans (hbρ.trans hρr).le))
    have hinv : (A.chart p).symm q = z := by rw [← hqz]; exact (A.chart p).left_inv hs
    rw [hinv]
    simpa using hz
  · exact hqcoord.le.trans (le_of_not_gt hbρ)

end Yau.LeafProofs.L17Aux
