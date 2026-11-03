import Yau.Proofs.F01AActualLocalChart
import Yau.Proofs.F01AOriginalJointJets
import Yau.Proofs.F01AOriginalSpatialSchauder
import Yau.Proofs.F01ACenteredOriginalChart

/-! The continued approximation family supplies the whole quantitative
closed-chart compactness inlet. One common domain threshold precedes all
orders; the jet constants come from actual spatial estimates and the
native mixed-clock recursion. -/
noncomputable section
open Set Filter Metric
open scoped Topology Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem actual_centered_chart_closed_joint_budgets
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    (L : ℕ → ℝ) (ho : ∀ m : ℕ, u o < L m)
    (h : ∀ m : ℕ, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (U : ∀ m : ℕ, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m : ℕ, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (U m))
    (e : OpenPartialHomeomorph (ComplexVector n) X.manifold.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r T : ℝ} (hr : 0 < r) (hr1 : 64 * r ≤ 1)
    (hball : closedBall 0 (64 * r) ⊆ e.source) (hT : 1 ≤ T) :
    ∃ N : ℕ,
      (∀ m : ℕ, N ≤ m → ContDiffOn ℝ ∞
        (fun p : Point n => ambientApproximationPotential X o u hu (L m) (ho m) (U m) (e p.1) p.2)
        (closedBall 0 r ×ˢ Icc 0 T)) ∧
      ∀ k, ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, N ≤ m → ∀ p ∈ closedBall 0 r ×ˢ Icc 0 T,
        ‖iteratedFDerivWithin ℝ k
          (fun q : Point n => ambientApproximationPotential X o u hu (L m) (ho m) (U m) (e q.1) q.2)
          (closedBall 0 r ×ˢ Icc 0 T) p‖ ≤ B := by
  classical
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hg : MetricSmooth X.metric.form := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  obtain ⟨L0, Mclock, ell, upper, hL0, hM, hell, hUpper, hData⟩ :=
    actual_original_chart_uniform_solution_data X o u hu Ξ hΞ hRic hc hgrowth e he hei hball hTp
  let ρ : ℝ := 16 * r
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρr : 4 * ρ ≤ 64 * r := by dsimp only [ρ]; linarith
  have hρ1 : 4 * ρ ≤ 1 := by dsimp only [ρ]; linarith
  have hρT : (4 * ρ) ^ 2 ≤ T := by
    dsimp only [ρ]
    nlinarith [mul_nonneg (show 0 ≤ 64 * r by positivity) (sub_nonneg.mpr hr1)]
  obtain ⟨C, hC, hSpatial⟩ := fixed_original_chart_closed_spatial_jets
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos X.manifold)
    X.metric.form hg e he hei hball (α := 1 / 2) (β := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hell hUpper hM hTp hρ hρr hρ1 hρT
  have hEvent : ∀ᶠ m : ℕ in atTop, L0 ≤ L m ∧ T < (m : ℝ) + 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt T
    filter_upwards [hL.eventually (eventually_ge_atTop L0), eventually_ge_atTop N] with m hm hmN
    have hcast : (N : ℝ) ≤ m := by exact_mod_cast hmN
    exact ⟨hm, by linarith⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEvent
  let F : {m : ℕ // N ≤ m} → Point n → ℝ := fun i p =>
    ambientApproximationPotential X o u hu (L i.val) (ho i.val) (U i.val) (e p.1) p.2
  have hLocal (i : {m : ℕ // N ≤ m}) :=
    hData (L i.val) (hN i.val i.property).1 (ho i.val) ((i.val : ℝ) + 2)
      (h i.val) (U i.val) (hN i.val i.property).2 (hsol i.val)
  have hSmall : ball (0 : Space n) (2 * r) ⊆ ball 0 (64 * r) :=
    ball_subset_ball (by linarith)
  have hClosedSmall : closedBall (0 : Space n) r ⊆ ball 0 (2 * r) :=
    closedBall_subset_ball (by linarith)
  have hSpatial' (i : {m : ℕ // N ≤ m}) (k : ℕ) (z : Space n)
      (hz : z ∈ ball 0 (2 * r)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖iteratedFDeriv ℝ k (fun w => F i (w,t)) z‖ ≤ C k := by
    have hScale : ρ / 8 = 2 * r := by dsimp only [ρ]; ring
    exact hSpatial (F i) (hLocal i).1 (hLocal i).2.1 (hLocal i).2.2.1
      (hLocal i).2.2.2.1 (hLocal i).2.2.2.2 k z (by rwa [hScale]) t ht
  have hBudgets := original_chart_closed_joint_budgets_of_spatial_bounds
    X.metric.form hg e he hei hr
    ((closedBall_subset_closedBall (by linarith : 2 * r ≤ 64 * r)).trans hball)
    hTp hell F C hC
    (fun i => ((hLocal i).1).mono (prod_mono hSmall Subset.rfl))
    (fun i z hz t ht => (hLocal i).2.2.1 z (hSmall hz) t ht)
    (fun i p hp => ((hLocal i).2.2.2.2 p ⟨hSmall hp.1,hp.2⟩).1) hSpatial'
  refine ⟨N, ?_, ?_⟩
  · intro m hm
    exact ((hLocal ⟨m,hm⟩).1).mono
      (prod_mono (hClosedSmall.trans hSmall) Subset.rfl)
  · intro k
    obtain ⟨B, hB, hBound⟩ := hBudgets k
    exact ⟨B, hB, fun m hm p hp => hBound ⟨m,hm⟩ p hp⟩

theorem actual_original_chart_closed_joint_budgets
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    (L : ℕ → ℝ) (ho : ∀ m : ℕ, u o < L m)
    (h : ∀ m : ℕ, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (U : ∀ m : ℕ, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m : ℕ, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (U m))
    (a : Pt X) {r T : ℝ} (hr : 0 < r) (hr1 : 64 * r ≤ 1)
    (hball : closedBall (chartPt a a) (64 * r) ⊆ chartTarget a) (hT : 1 ≤ T) :
    (∀ᶠ m : ℕ in atTop, ContDiffOn ℝ ∞
      (fun p : Point n => ambientApproximationPotential X o u hu (L m) (ho m) (U m) (chartInv a p.1) p.2)
      (closedBall (chartPt a a) r ×ˢ Icc 0 T)) ∧
    ∀ k, ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, N ≤ m →
      ∀ p ∈ closedBall (chartPt a a) r ×ˢ Icc 0 T,
        ‖iteratedFDerivWithin ℝ k
          (fun q : Point n => ambientApproximationPotential X o u hu (L m) (ho m) (U m) (chartInv a q.1) q.2)
          (closedBall (chartPt a a) r ×ˢ Icc 0 T) p‖ ≤ B := by
  have hsmall : closedBall (chartPt a a) r ⊆ chartTarget a :=
    (closedBall_subset_closedBall (by linarith : r ≤ 64 * r)).trans hball
  have he := (centeredOriginalChart_contMDiffOn a).mdifferentiableOn (by simp)
  have hei := (centeredOriginalChart_inverse_contMDiffOn a).mdifferentiableOn (by simp)
  obtain ⟨N, hSmooth, hBounds⟩ := actual_centered_chart_closed_joint_budgets
    X o u hu Ξ hΞ hRic hc hgrowth L ho h U hL hsol
    (centeredOriginalChart a) he hei hr hr1 (centeredOriginalChart_closedBall_source a hball) hT
  refine ⟨?_, ?_⟩
  · have hh := actual_approximation_sequence_eventual_chart_smoothness
      X o u hu L ho h U hL hsol (ordinaryChart a)
      ((ordinaryChart_contMDiffOn a).mdifferentiableOn (by simp))
      (isCompact_closedBall _ _) (by rw [ordinaryChart_source]; exact hsmall) T
    simpa only [ordinaryChart_apply] using hh
  · intro k
    obtain ⟨B, hB, hBound⟩ := hBounds k
    refine ⟨N, B, hB.le, ?_⟩
    intro m hm p hp
    have hz : p.1 - chartPt a a ∈ closedBall (0 : Space n) r := by
      simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hp.1
    have hh := hBound m hm (p.1 - chartPt a a,p.2) ⟨hz,hp.2⟩
    rw [centeredOriginalChart_iteratedFDerivWithin_joint] at hh
    have heq : chartPt a a + (p.1 - chartPt a a) = p.1 := by abel
    simpa only [heq] using hh

end Yau.NodeProofs.F01Aux
