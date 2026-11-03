import Yau.Proofs.C01LocalRicciCoercivity

/-! On a compact original spatial set, the actual time-a metric has a
strictly positive lower bound relative to the original metric. This is
local compactness of genuine positive matrices, with no completeness
assertion about the time-a metric. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_local_metric_coercivity
    (hflow : LocalizedFlow X o h U P ρ) (a : ℝ) (ha : 0 ≤ a) (x : Pt X) :
    ∃ c : ℝ, 0 < c ∧ ∃ O : Set (Pt X), IsOpen O ∧ x ∈ O ∧
      ∀ y ∈ O, ∀ v : ComplexVector n,
        c * matrixQuadraticReal (gMat X.metric.form y) v ≤
          matrixQuadraticReal (gMat (h a) y) v := by
  let z₀ := chartPt x x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target (I := ComplexModel n) x))
  let S : Set (ComplexVector n) := Metric.closedBall z₀ (r / 2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsub : S ⊆ chartTarget x := by
    intro z hz
    exact hball ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  obtain ⟨c, hc, hlocal⟩ := compact_matrix_quadratic_coercivity
    (original_manifold_dimension_pos X.manifold)
    (fun z => hMat X.metric.form x z) (fun z => hMat (h a) x z) S hS
    (fun i j => (Yau.LeafProofs.L12Aux.hMat_contDiffOn X.metric x i j).continuousOn.mono hsub)
    (fun i j => (localizedFlow_hMat_fixedTime_contDiffOn hflow a ha x i j).continuousOn.mono hsub)
    (fun z hz => Yau.Blueprint.Alignment.Y03Proof.hMat_posDef (h a) x z (hsub hz))
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
  have hJ : IsUnit J.det := isUnit_iff_ne_zero.mpr (by
    simpa only [hzy] using centerFrameMatrix_det_ne_zero x z (hsub hzS) (h a))
  have hH (k : HermitianField X.manifold) : hMat k x z = Jᴴ * gMat k y * J := by
    simpa only [hzy] using hMat_center_congruence k x z
  apply quadratic_coercivity_of_congruence (gMat X.metric.form y) (gMat (h a) y) J hJ c
  intro v
  have hv := hlocal z hzS v
  rw [hH X.metric.form, hH (h a)] at hv
  exact hv

theorem localizedFlow_compact_metric_coercivity
    (hflow : LocalizedFlow X o h U P ρ) (a : ℝ) (ha : 0 ≤ a)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : ComplexVector n,
      c * matrixQuadraticReal (gMat X.metric.form x) v ≤
        matrixQuadraticReal (gMat (h a) x) v := by
  classical
  by_cases hKne : K.Nonempty
  · choose c hc O hO hxO hb using
      (fun x : Pt X => localizedFlow_local_metric_coercivity hflow a ha x)
    have hcover : K ⊆ ⋃ x, O x := fun x _ => Set.mem_iUnion.mpr ⟨x, hxO x⟩
    obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hO hcover
    have hFne : F.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
      obtain ⟨hyF, _⟩ := Set.mem_iUnion.mp hy
      exact ⟨y, hyF⟩
    let cK := (F.image c).min' (hFne.image c)
    have hcK : 0 < cK := by
      obtain ⟨x, _, hxeq⟩ := Finset.mem_image.mp ((F.image c).min'_mem (hFne.image c))
      have hp := hc x
      rw [hxeq] at hp
      exact hp
    have hcle (y : Pt X) (hy : y ∈ F) : cK ≤ c y :=
      Finset.min'_le (F.image c) (c y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    refine ⟨cK, hcK, ?_⟩
    intro x hx v
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
    obtain ⟨hyF, hyO⟩ := Set.mem_iUnion.mp hy
    have hqH : 0 ≤ matrixQuadraticReal (gMat X.metric.form x) v := by
      have hp := (Complex.nonneg_iff.mp
        ((Yau.Blueprint.Alignment.Y03Proof.hMat_posDef X.metric.form x (chartPt x x)
          (mem_extChartAt_target (I := ComplexModel n) x)).posSemidef.dotProduct_mulVec_nonneg
            (WithLp.ofLp v))).1
      simpa only [matrixQuadraticReal, gMat] using hp
    exact (mul_le_mul_of_nonneg_right (hcle y hyF) hqH).trans (hb y x hyO v)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hKne ⟨x, hx⟩).elim

end Yau.NodeProofs.C01Aux
