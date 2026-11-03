import Yau.Proofs.V02SprayTest
import Yau.Proofs.V02NativeFamily
import Yau.Proofs.V02AreaTaylorJetAt

/-! The actual lower test has uniform third parameter jets on the compact
set of allowed centers and bounded initial spray coefficients. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02AreaTaylorProof

variable {n b q : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spray_test_C3
    {d : VariationData X q} (hd : VariationSetup d)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcC : Kc ⊆ interior (centerCylinder d))
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hU : IsOpen U)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    (hInitial : ∀ p ∈ Kc,
      NativeCotangentPoint.mk (cotangentChartInv d.chart p.1) ∈ U)
    (hTube : ∀ p ∈ Kc, ∀ τ ∈ closedBall (0 : Fin b → ℂ) R,
      InCotangentTimeChart d.chart
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), τ)).val p.2
        (interior (centerCylinder d))) :
    ∃ r M : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧ 0 ≤ M ∧
      ∀ (F : VariationDisc X) (h : ℂ → ℂ) (c : ℂ → Fin b → ℂ),
        InCotangentTimeChart d.chart (F.f 0) F.s Kc → ‖h 0‖ ≤ 1 → ‖c 0‖ ≤ C →
        ContDiffOn ℝ 3 (fun z => d.test (nativeSprayFamily Ψ F.f h c z 0) F.s)
          (ball (0 : ℂ) r) ∧
        ∀ z ∈ ball (0 : ℂ) r,
          ‖iteratedFDeriv ℝ 3
            (fun w => d.test (nativeSprayFamily Ψ F.f h c w 0) F.s) z‖ ≤ M := by
  let r := R / (4 * (C + 1))
  have hr : 0 < r := div_pos hR (by positivity)
  have hrR : r < R / (2 * (C + 1)) := by
    dsimp [r]
    exact div_lt_div_of_pos_left hR (by positivity) (by nlinarith)
  let A : Set (SprayCenterData n b) :=
    Kc ×ˢ (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : Fin b → ℂ) C)
  let K : Set (ℂ × SprayCenterData n b) := closedBall (0 : ℂ) r ×ˢ A
  have hK : IsCompact K := (isCompact_closedBall _ _).prod
    (hKc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  obtain ⟨V, hV, hCV, _, htest⟩ := hd.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  have hcf : ∀ p ∈ K, ContDiffAt ℝ ∞ (nativeSprayTest d Ψ) p := by
    intro p hp
    have hz : ‖p.1‖ ≤ r := by simpa using hp.1
    have hβ : ‖p.2.2.1‖ ≤ 1 := by simpa using hp.2.2.1
    have hc : ‖p.2.2.2‖ ≤ C := by simpa using hp.2.2.2
    have htime : (sprayTestParameter p).2 ∈ ball (0 : Fin b → ℂ) R := by
      have hn : ‖(sprayTestParameter p).2‖ ≤ ‖p.1‖ * C := by
        apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) hC)).mpr
        intro k
        change ‖p.1 * p.2.2.1 * p.2.2.2 k‖ ≤ _
        rw [norm_mul, norm_mul]
        exact (mul_le_mul
          (mul_le_mul_of_nonneg_left hβ (norm_nonneg _))
          ((norm_le_pi_norm p.2.2.2 k).trans hc) (norm_nonneg _)
          (by positivity)).trans_eq (by ring)
      have hsmall : ‖p.1‖ * C < R := by
        have hzr : ‖p.1‖ * (4 * (C + 1)) ≤ R := (le_div_iff₀ (by positivity)).mp hz
        nlinarith [norm_nonneg p.1]
      exact mem_ball.mpr (by simpa only [dist_zero_right] using hn.trans_lt hsmall)
    have ht := hTube p.2.1 hp.2.1 (sprayTestParameter p).2 (ball_subset_closedBall htime)
    apply nativeSprayTest_contDiffAt hU hΨ hV htest
      ((hd.2.2.2.2.2.2.2.1.2.2.1 (interior_subset (hKcC hp.2.1))).1)
      (hInitial _ hp.2.1) htime ht.1
    exact hCV (interior_subset ht.2)
  obtain ⟨M, hM, hbound⟩ := compact_slice_jet_bound_at hK hcf 3
  refine ⟨r, M, hr, hrR, hM, fun F h c hcenter hh hc => ?_⟩
  let a : SprayCenterData n b := ((cotangentChart d.chart (F.f 0), F.s), (h 0, c 0))
  have ha : a ∈ A := ⟨hcenter.2, by simpa using hh, by simpa using hc⟩
  have heq : (fun z => d.test (nativeSprayFamily Ψ F.f h c z 0) F.s) =
      (fun z => nativeSprayTest d Ψ (z, a)) := by
    funext z
    simp only [nativeSprayTest, sprayTestParameter, a, nativeSprayFamily,
      cotangentChart_left_inv d.chart hcenter.1]
  rw [heq]
  constructor
  · intro z hz
    have hs : ContDiffAt ℝ ∞ (fun w => nativeSprayTest d Ψ (w, a)) z :=
      (hcf (z, a) ⟨ball_subset_closedBall hz, ha⟩).comp z
        (contDiffAt_id.prodMk contDiffAt_const)
    exact hs.contDiffWithinAt.of_le (by simp : (3 : ℕ∞ω) ≤ ∞)
  · intro z hz
    exact hbound (z, a) ⟨ball_subset_closedBall hz, ha⟩

end Yau.Blueprint.V02Proof
