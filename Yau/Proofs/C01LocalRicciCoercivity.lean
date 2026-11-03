import Yau.Proofs.C01CompactQuadraticCoercivity

/-! A compact coordinate ball gives a genuine neighborhood on which
the original Ricci matrix at time one uniformly dominates the original
metric.  Both forms are transported by the same actual chart frame. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem quadratic_coercivity_of_congruence {n : ℕ} (H A J : Herm n)
    (hJ : IsUnit J.det) (c : ℝ)
    (hbound : ∀ v : ComplexVector n,
      c * matrixQuadraticReal (Jᴴ * H * J) v ≤ matrixQuadraticReal (Jᴴ * A * J) v) :
    ∀ u : ComplexVector n, c * matrixQuadraticReal H u ≤ matrixQuadraticReal A u := by
  intro u
  let v : ComplexVector n := WithLp.toLp 2 (J⁻¹ *ᵥ WithLp.ofLp u)
  have hcancel : J *ᵥ WithLp.ofLp v = WithLp.ofLp u := by
    simp only [v, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv J hJ, Matrix.one_mulVec]
  have hv := hbound v
  dsimp only [matrixQuadraticReal] at hv
  rw [← Yau.Blueprint.Alignment.Y03Proof.conjugate_quadratic H J (WithLp.ofLp v),
    ← Yau.Blueprint.Alignment.Y03Proof.conjugate_quadratic A J (WithLp.ofLp v), hcancel] at hv
  exact hv

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_local_ricci_coercivity_one
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X) :
    ∃ c : ℝ, 0 < c ∧ ∃ O : Set (Pt X), IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ O, ∀ v : ComplexVector n,
        c * matrixQuadraticReal (gMat (h 1) y) v ≤ matrixQuadraticReal (ricci (h 1) y) v := by
  let z₀ := chartPt x x
  have hz₀ : z₀ ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz₀)
  let S : Set (ComplexVector n) := Metric.closedBall z₀ (r / 2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsub : S ⊆ chartTarget x := by
    intro z hz
    apply hball
    exact ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  obtain ⟨c, hc, hlocal⟩ := compact_matrix_quadratic_coercivity
    (original_manifold_dimension_pos X.manifold)
    (fun z => hMat (h 1) x z) (fun z => fixedChartRicciMatrix h x z 1) S hS
    (fun i j => (localizedFlow_hMat_fixedTime_contDiffOn hflow 1 zero_le_one x i j).continuousOn.mono hsub)
    (fun i j => (localizedFlow_fixedChartRicci_contDiffOn hflow x 1 zero_lt_one i j).continuousOn.mono hsub)
    (fun z hz => localizedFlow_fixedChartRicci_posDef hflow hjoint x z (hsub hz) 1 zero_lt_one)
  let O : Set (Pt X) := (extChartAt (ComplexModel n) x).source ∩
    (chartPt x) ⁻¹' Metric.ball z₀ (r / 2)
  have hO : IsOpen O :=
    (continuousOn_extChartAt (I := ComplexModel n) x).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := ComplexModel n) x) Metric.isOpen_ball
  have hxO : x ∈ O := ⟨mem_extChartAt_source x, Metric.mem_ball_self (half_pos hr)⟩
  refine ⟨c, hc, O, hO, hxO, ?_⟩
  intro y hy
  let z := chartPt x y
  have hzS : z ∈ S := (Metric.mem_ball.mp hy.2).le
  have hzy : chartInv x z = y := (extChartAt (ComplexModel n) x).left_inv hy.1
  let J : Herm n := centerFrameMatrix x y
  have hJdet : IsUnit J.det := isUnit_iff_ne_zero.mpr (by
    simpa only [hzy] using centerFrameMatrix_det_ne_zero x z (hsub hzS) (h 1))
  have hH : hMat (h 1) x z = Jᴴ * gMat (h 1) y * J := by
    simpa only [hzy] using hMat_center_congruence (h 1) x z
  have hA : fixedChartRicciMatrix h x z 1 = Jᴴ * ricci (h 1) y * J := by
    simpa only [hzy] using fixedChartRicciMatrix_center_congruence hflow x z 1 zero_lt_one
  apply quadratic_coercivity_of_congruence (gMat (h 1) y) (ricci (h 1) y) J hJdet c
  intro v
  have hv := hlocal z hzS v
  rw [hH, hA] at hv
  exact hv

end Yau.NodeProofs.C01Aux
