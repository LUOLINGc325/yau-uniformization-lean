import Yau.LeafProofs.L17ChartEscape

/-! Interior chart escape from an arbitrary actual coordinate starting point. -/

noncomputable section

open Set Metric Filter MeasureTheory Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem BoundedChartFamily.closedChartBall_contains_distance_ball_from
    {g : HermitianField M} (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (p q : M.Carrier) (z₀ : ComplexVector n) {ρ : ℝ} (hρ : 0 < ρ)
    (hBG : closedBall z₀ ρ ⊆ ball 0 A.radius)
    (hq : inducedDistance g (A.chart p z₀) q < Real.sqrt (2 * (A.bound 0)⁻¹) * ρ) :
    q ∈ A.chart p '' closedBall z₀ ρ := by
  let := L12Aux.manifold_realSmooth M
  let : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentNormedAddCommGroup g x
  let : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => L12Aux.underlyingRealTangentInnerProductSpace g x
  let e := A.chart p
  let D := (Real.sqrt (2 * (A.bound 0)⁻¹))⁻¹
  have hC := A.bound_pos 0
  have hD : 0 < D := by dsimp [D]; positivity
  have hbudget : inducedDistance g (A.chart p z₀) q < ρ / D := by
    simpa only [D, div_inv_eq_mul, mul_comm] using hq
  have hED : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) (e z₀) q <
      ENNReal.ofReal (ρ / D) := by
    rw [← L23Aux.inducedDistance_eq_riemannianEDist g hg]
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hρ hD)).mpr hbudget
  obtain ⟨γ, hγp, hγq, hγsmooth, hγlen, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hED zero_lt_one
  have hsource : closedBall z₀ ρ ⊆ e.source := by
    intro z hz
    exact A.closedBall_source p (ball_subset_closedBall (hBG hz))
  let u := e '' closedBall z₀ ρ
  let v := e '' ball z₀ ρ
  have huclosed : IsClosed u :=
    ((isCompact_closedBall z₀ ρ).image_of_continuousOn
      (e.continuousOn.mono hsource)).isClosed
  have hvopen : IsOpen v := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hsource)
  have hvu : v ⊆ u := image_mono ball_subset_closedBall
  have hutarget : u ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hsource hz)
  have huBG : u ⊆ e '' ball 0 A.radius := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hBG hz, rfl⟩
  let B := γ ⁻¹' u
  have zero_mem : 0 ∈ B := by
    change γ 0 ∈ u
    rw [hγp]
    exact ⟨z₀, mem_closedBall_self hρ.le, rfl⟩
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
  have hcoord0 : γ' 0 = z₀ := by
    change e.symm (γ 0) = z₀
    rw [hγp]
    exact e.left_inv (hsource (mem_closedBall_self hρ.le))
  have hnormreal : ‖e.symm (γ t₁) - z₀‖ < ρ := by
    apply (ENNReal.ofReal_lt_ofReal_iff hρ).mp
    simpa only [hcoord0, ofReal_norm, γ', Function.comp_apply] using hnorm
  exact ⟨e.symm (γ t₁), by simpa only [mem_ball, dist_eq_norm] using hnormreal,
    e.right_inv (hutarget (hstay (right_mem_Icc.mpr ht₁0)))⟩

end Yau.LeafProofs.L17Aux
