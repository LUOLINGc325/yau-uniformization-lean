import Yau.Proofs.V02WallTaylorChartFactor
import Yau.Proofs.V02WallTaylorWallAlgebra
import Yau.Proofs.V02WallTaylorOuterPhase

/-! One parameter radius preserves both original geometric walls for the
literal outer-candidate native spray family. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n q b : ℕ} {X : KahlerManifold n}

theorem wallPower_mem_Icc {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (y : CotangentPoint X.manifold) : wallPower d j a y ∈ Set.Icc 0 1 := by
  have hp := setup_wallProfiles hd
  have hb : 0 ≤ deltaBase d j y.1 := (hp.2.2.1 _).1
  have hf : 0 ≤ deltaFiber d j y := (hp.2.2.2 _).1
  have hprod : 0 ≤ wallProduct d j y := mul_nonneg hb hf
  have hprod1 : wallProduct d j y ≤ 1 :=
    (mul_le_mul (deltaBase_le_one hp j y.1) (deltaFiber_le_one hp j y) hf (by norm_num)).trans_eq (one_mul 1)
  exact ⟨pow_nonneg hprod _, pow_le_one₀ hprod hprod1⟩

theorem wallPower_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun u => wallPower d j a (cotangentChartInv x u)) (cotangentTarget x) :=
  ((deltaBase_chart_contDiffOn hd j x).mul (deltaFiber_chart_contDiffOn hd j x)).pow a

theorem exists_uniform_chart_boundary_region {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 1 ≤ a)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Pt X)
    {A : CotangentCoord n} {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : Metric.ball A (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball A (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall A δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧
      ∀ z : ℂ, z ∈ Metric.ball 0 r → ∀ u ∈ Metric.closedBall A δ,
      ∀ β ∈ Metric.closedBall (0 : ℂ) 1, ∀ c ∈ Metric.closedBall (0 : Fin b → ℂ) C,
      cotangentChartInv x u ∈ boundaryRegion d j →
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u),
        wallPower d j a (cotangentChartInv x u) • (z • (β • c)))).val ∈ boundaryRegion d j := by
  let m : CotangentCoord n → ℝ := fun u => wallPower d j a (cotangentChartInv x u)
  have hm : ContDiffOn ℝ ∞ m (Metric.ball A (2 * δ)) :=
    (wallPower_chart_contDiffOn hd j a x).mono hvalid
  have hmb : ∀ u ∈ Metric.closedBall A δ, m u ∈ Set.Icc 0 1 :=
    fun u _ => wallPower_mem_Icc hd j a _
  obtain ⟨rb, hrb, hrbR, hb⟩ := exists_uniform_chartSprayFactor hzero x hδ hR hC hvalid hΨ hsource
    (B := fun y => deltaBase d j y.1) (deltaBase_chart_contDiffOn hd j x) hm hmb
  obtain ⟨rf, hrf, _, hf⟩ := exists_uniform_chartSprayFactor hzero x hδ hR hC hvalid hΨ hsource
    (B := deltaFiber d j) (deltaFiber_chart_contDiffOn hd j x) hm hmb
  refine ⟨min rb rf, lt_min hrb hrf, (min_le_left rb rf).trans_lt hrbR, ?_⟩
  intro z hz u hu β hβ c hc hy
  have hzb := Metric.ball_subset_ball (min_le_left rb rf) hz
  have hzf := Metric.ball_subset_ball (min_le_right rb rf) hz
  have hB := hb z hzb u hu β hβ c hc
  have hF := hf z hzf u hu β hβ c hc
  apply boundaryRegion_persists_of_wall_factors hd j a ha hy hB.1.le hF.1.le
  · linarith [hB.2]
  · linarith [hF.2]

/-- Finite minima with an explicit positive fallback cover the empty chart family. -/
theorem exists_pos_common_radius {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {S : ℝ} (hS : 0 < S) :
    ∃ t : ℝ, 0 < t ∧ t < S ∧ ∀ i, t ≤ r i := by
  classical
  have hh : ∀ s : Finset ι, ∃ t : ℝ, 0 < t ∧ t < S ∧ ∀ i ∈ s, t ≤ r i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨S / 2, half_pos hS, half_lt_self hS, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨t, ht, htS, htr⟩ := ih
      refine ⟨min t (r i), lt_min ht (hr i), (min_le_left _ _).trans_lt htS, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (htr k hk)
  obtain ⟨t, ht, htS, htr⟩ := hh Finset.univ
  exact ⟨t, ht, htS, fun i => htr i (Finset.mem_univ _)⟩

def wallSprayFamily (d : VariationData X q) (j a : ℕ)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (F : VariationDisc X) (c : ℂ → Fin b → ℂ) (z ζ : ℂ) : CotangentPoint X.manifold :=
  (Ψ (NativeCotangentPoint.mk (F.f ζ),
    fun k => z * outerCandidate (logTrace d j F.f) a ζ * c ζ k)).val

theorem exists_uniform_spray_boundary_region {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 1 ≤ a) {N : ℕ}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : Fin N → Pt X) (A : Fin N → CotangentCoord n)
    {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : ∀ k, Metric.closedBall (A k) (8 * δ) ⊆ cotangentTarget (x k))
    (hΨ : ∀ k, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x k))
      (Metric.ball (A k) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ k, ∀ u ∈ Metric.closedBall (A k) δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x k) u), τ)).val ∈ cotangentSource (x k))
    (K : Set (CotangentPoint X.manifold))
    (hcover : K ⊆ ⋃ k, cotangentChartInv (x k) '' Metric.ball (A k) δ) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧
      ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F.f ζ ∈ K) →
      ∀ c : ℂ → Fin b → ℂ, (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C) →
      ∀ z ∈ Metric.ball 0 r, ∀ θ : ℝ, wallSprayFamily d j a Ψ F c z (circlePoint θ) ∈ boundaryRegion d j := by
  classical
  have hval (k : Fin N) : Metric.ball (A k) (2 * δ) ⊆ cotangentTarget (x k) := by
    intro u hu
    exact hvalid k (Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hu))
  choose r hr hrR hb using fun k =>
    exists_uniform_chart_boundary_region hd j a ha hzero (x k) hδ hR hC (hval k) (hΨ k) (hsource k)
  obtain ⟨t, ht, htR, htr⟩ := exists_pos_common_radius r hr
    (show 0 < R / (2 * (C + 1)) by positivity)
  refine ⟨t, ht, htR, fun F hF hFK c hc z hz θ => ?_⟩
  have hyK := hFK _ (circlePoint_mem_closedBall θ)
  obtain ⟨k, u, hu, huy⟩ := Set.mem_iUnion.mp (hcover hyK)
  have hβ : outerWallPhase d j a F.f θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, outerWallPhase_norm, le_refl]
  have hcθ : c (circlePoint θ) ∈ Metric.closedBall (0 : Fin b → ℂ) C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc _ (circlePoint_mem_closedBall θ)
  have hy := hF.2.2.2.2.2.2.2.1 θ
  rw [← huy] at hy
  have hh := hb k z (Metric.ball_subset_ball (htr k) hz) u
    (Metric.ball_subset_closedBall hu) _ hβ _ hcθ hy
  have hτ : (wallPower d j a (cotangentChartInv (x k) u) •
      (z • (outerWallPhase d j a F.f θ • c (circlePoint θ))) : Fin b → ℂ) =
      (fun i => z * outerCandidate (logTrace d j F.f) a (circlePoint θ) * c (circlePoint θ) i) := by
    rw [outerCandidate_eq_wallPower_mul_phase hd hF a θ, ← huy]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [hτ, huy] at hh
  exact hh

end Yau.Blueprint.V02WallTaylorProof
