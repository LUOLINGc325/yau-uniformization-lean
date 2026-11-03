import Yau.Proofs.F01NormalizedAllSpatialSchauder
import Yau.Proofs.F01AllOrderMatrixJetBudget

/-! Full spatial matrix jets on the initial patch. The zero extension is
used only for its parabolic C² and spatial estimates. This theorem makes
no claim of joint smoothness across the initial time. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_initial_matrix_jet_budgets
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C α β : ℝ} (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ A.radius → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) → ∀ a : M.Carrier,
      HolderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 2)) (1 / 2))
        (fun p => iteratedFDeriv ℝ k
          (fun z => pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • z)) p.1) (K k) := by
  classical
  let δ := min α β
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  obtain ⟨Ci, hCi, hInitial⟩ := normalized_initial_schauder g hg A hC hα hα1 hβ hβ1
  obtain ⟨Cs, hCs, hBackground⟩ := normalized_background_spatial_tensor_holder_budgets A hδ1.le
  obtain ⟨Cu, hCu, hWords⟩ := normalized_native_all_spatial_schauder g hg A hC hα hα1 hβ hβ1
  choose K hK hBudget using all_order_matrix_jet_budgets (n := n) Cs Cu hCs hCu hCi.le
  refine ⟨K, hK, ?_⟩
  intro k h U T ρ hρ hρr2 hρ12 hρT2 hU hh0 hU0 hpot hpde hflow a
  have hρr : ρ ≤ A.radius := by linarith [hρ.le]
  have hρ1 : ρ ≤ 1 := by linarith [hρ.le]
  have hρT : ρ ^ 2 ≤ T := by nlinarith [sq_nonneg ρ]
  let V := forwardZeroSpaceTime (parabolicRescalePotential ρ
    (fun p : Point n => U (A.chart a p.1) p.2))
  let S := normalizedComplexBackground A a ρ
  let Q := cylinder (ball (0 : Space n) (1 / 2)) (-(1 / 2)) (1 / 2)
  have hCore : Q ⊆ cylinder (ball 0 1) (-1) 1 := fun p hp =>
    ⟨ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.1,
      by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hData := normalized_rescale_initial_jet_data A h U hρ hρr hρT hU hh0 hU0 hpde a
  have hVs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ContDiffOn ℝ ∞ (fun z => V (z,t)) (ball 0 1) :=
    forwardZeroSpaceTime_smooth_slices (fun s hs => contDiffOn_space_slice hData.1 hs) ht.2
  have hInit := hInitial h U T ρ hρ hρr2 hρ12 hρT2 hU hh0 hU0 hpot hpde hflow a
  have hDD : HolderBound δ Q (spatialDD V) Ci := holderBound_restrict hInit.2.2.2.1 hCore
  have hSj (j : ℕ) : HolderBound δ Q
      (fun p => iteratedFDeriv ℝ j (fun z => S (z,p.2)) p.1) (Cs j) :=
    holderBound_restrict (hBackground j ρ hρ hρr hρ1 a) hCore
  have hW (i : RIdx n) (ws : List (Space n)) (hws : NativeFrameWord ws) :
      SchauderBound δ Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] V)) (Cu ws.length) :=
    hWords ws.length h U T ρ hρ hρr2 hρ12 hρT2 hU hh0 hU0 hpot hpde hflow a i ws hws rfl
  have hm := hBudget k Q (ball 0 1) δ S V isOpen_ball
    (fun p hp => ⟨(hCore hp).1, mem_univ _⟩)
    (fun p _ => normalizedComplexBackground_smooth_spatial_slice A hρ hρr a p.2)
    (fun p hp => hVs p.2 (hCore hp).2) hSj hDD hW
  apply holderBound_congr_on_native hm
  intro p hp
  have he : (fun z => chartPotentialMatrix S V (z,p.2)) =ᶠ[𝓝 p.1]
      (fun z => pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • z)) := by
    filter_upwards [isOpen_ball.mem_nhds (hCore hp).1] with z hz
    exact normalized_complex_flow_matrix hg A h U hρ hρr hρT hU hh0 hpot a
      (show (z,p.2) ∈ ball 0 1 ×ˢ Icc (-1) 1 from ⟨hz, (hCore hp).2⟩)
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end Yau.NodeProofs.F01Aux
