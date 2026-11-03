import Yau.Proofs.C01UniformMatrixComparison
import Yau.Proofs.C01LocalRicciCoercivity

/-! A fixed genuine chart and its compact coordinate ball give uniform
relative continuity of the actual flow metric near every spatial point,
including one-sided time continuity at zero. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Filter

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_local_uniform_metric_comparison
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (a : ℝ) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ O : Set (Pt X), IsOpen O ∧ x ∈ O ∧
      ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ y ∈ O, ∀ v : ComplexVector n,
        |matrixQuadraticReal (gMat (h s) y) v - matrixQuadraticReal (gMat (h a) y) v| ≤
          ε * matrixQuadraticReal (gMat (h a) y) v := by
  let z₀ := chartPt x x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target (I := ComplexModel n) x))
  let S : Set (ComplexVector n) := Metric.closedBall z₀ (r / 2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsub : S ⊆ chartTarget x := by
    intro z hz
    exact hball ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : Set.Ici (0 : ℝ) → S → Herm n := fun t z => hMat (h t.val) x z.val
  have hA (i j : Fin n) : Continuous (fun p : Set.Ici (0 : ℝ) × S => A p.1 p.2 i j) := by
    have hc := (Yau.Blueprint.Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).continuousOn
    exact hc.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨hsub p.2.property, p.1.property⟩)
  have hpositive (z : S) (_hz : z ∈ (Set.univ : Set S)) : (A ⟨a, ha⟩ z).PosDef :=
    Yau.Blueprint.Alignment.Y03Proof.hMat_posDef (h a) x z.val (hsub z.property)
  have huniform := compact_uniform_matrix_comparison A ⟨a, ha⟩ Set.univ isCompact_univ
    hA hpositive ε hε
  have hreal : ∀ᶠ s in 𝓝[Set.Ici 0] a, ∀ z : S, ∀ v : ComplexVector n,
      |matrixQuadraticReal (hMat (h s) x z.val) v -
        matrixQuadraticReal (hMat (h a) x z.val) v| ≤
          ε * matrixQuadraticReal (hMat (h a) x z.val) v := by
    rw [nhdsWithin_eq_map_subtype_coe (s := Set.Ici (0 : ℝ)) (show a ∈ Set.Ici (0 : ℝ) from ha)]
    exact huniform.mono (fun s hs z v => hs z (Set.mem_univ z) v)
  let O : Set (Pt X) := (extChartAt (ComplexModel n) x).source ∩
    (chartPt x) ⁻¹' Metric.ball z₀ (r / 2)
  have hO : IsOpen O :=
    (continuousOn_extChartAt (I := ComplexModel n) x).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := ComplexModel n) x) Metric.isOpen_ball
  have hxO : x ∈ O := ⟨mem_extChartAt_source x, Metric.mem_ball_self (half_pos hr)⟩
  refine ⟨O, hO, hxO, ?_⟩
  filter_upwards [hreal] with s hs
  intro y hy u
  let z := chartPt x y
  have hzS : z ∈ S := (Metric.mem_ball.mp hy.2).le
  have hzy : chartInv x z = y := (extChartAt (ComplexModel n) x).left_inv hy.1
  let J : Herm n := centerFrameMatrix x y
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (by
    simpa only [hzy] using centerFrameMatrix_det_ne_zero x z (hsub hzS) (h a))
  let v : ComplexVector n := WithLp.toLp 2 (J⁻¹ *ᵥ WithLp.ofLp u)
  have hcancel : J *ᵥ WithLp.ofLp v = WithLp.ofLp u := by
    simp only [v, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv J hJ, Matrix.one_mulVec]
  have hH (t : ℝ) : hMat (h t) x z = Jᴴ * gMat (h t) y * J := by
    simpa only [hzy] using hMat_center_congruence (h t) x z
  have hb := hs ⟨z, hzS⟩ v
  change |matrixQuadraticReal (hMat (h s) x z) v -
      matrixQuadraticReal (hMat (h a) x z) v| ≤
        ε * matrixQuadraticReal (hMat (h a) x z) v at hb
  rw [hH s, hH a] at hb
  dsimp only [matrixQuadraticReal] at hb ⊢
  rw [← Yau.Blueprint.Alignment.Y03Proof.conjugate_quadratic (gMat (h s) y) J (WithLp.ofLp v),
    ← Yau.Blueprint.Alignment.Y03Proof.conjugate_quadratic (gMat (h a) y) J (WithLp.ofLp v),
    hcancel] at hb
  exact hb

end Yau.NodeProofs.C01Aux
