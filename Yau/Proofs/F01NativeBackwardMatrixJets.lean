import Yau.Proofs.F01NativeBackwardAllSpatialSchauder
import Yau.Proofs.F01AllOrderMatrixJetBudget

/-! Full spatial operator-tensor jets of the genuine native flow
matrix have uniform parabolic Holder bounds up to each terminal time.
The bounds precede all realized flows and clock/chart centers. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_backward_matrix_jet_budgets
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      SmoothSpaceTime U (Icc 0 T) → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) → ∀ a : M.Carrier,
      let σ := ρ * (1 / 4)
      HolderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
        (fun p => iteratedFDeriv ℝ k
          (fun z => pullbackMatrix (h (τ + σ ^ 2 * p.2)) (A.chart a) (σ • z)) p.1) (K k) := by
  classical
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  obtain ⟨Ci, hCi, hInitial⟩ := backward_native_schauder g hg A hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  obtain ⟨Cs, hCs, hBackground⟩ := shifted_background_spatial_tensor_holder_budgets A hTcap hδ1.le
  obtain ⟨Cu, hCu, hWords⟩ := native_backward_all_spatial_schauder g hg A
    hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  have each := all_order_matrix_jet_budgets (n := n) Cs Cu hCs hCu (by positivity : 0 ≤ 16 * Ci)
  choose K hK hBudget using each
  refine ⟨K, hK, ?_⟩
  intro k h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a
  dsimp only
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσρ : σ ≤ ρ := by dsimp only [σ]; linarith [hρ.le]
  have hσr : σ ≤ A.radius := hσρ.trans hρr
  have hσ1 : σ ≤ 1 := hσρ.trans hρ1
  have hσLower : σ ^ 2 ≤ τ := by
    have hh : σ ^ 2 ≤ ρ ^ 2 := by dsimp only [σ]; nlinarith [sq_nonneg ρ]
    exact hh.trans hLower
  have hτ : |τ| ≤ Tcap := by
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ρ] : 0 ≤ τ)]
    exact hUpper.trans hCap
  let V := shiftedNativePotential A U a σ τ
  let S := shiftedComplexBackground A a σ τ
  let Q := cylinder (ball (0 : Space n) (1 / 2)) (-(1 / 2)) 0
  have hCore : Q ⊆ cylinder (ball 0 1) (-1) 0 := by
    intro p hp
    exact ⟨ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.1, by linarith [hp.2.1], hp.2.2⟩
  have hFull : Q ⊆ cylinder (ball 0 1) (-1) 1 :=
    fun p hp => ⟨(hCore hp).1, (hCore hp).2.1, (hCore hp).2.2.trans zero_le_one⟩
  have hV := shifted_backward_native_potential_smooth A U hσ hσr hσLower hUpper hU a
  have hInit := shifted_native_quarter_schauder A U a ρ τ hδ.le
    (hInitial h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a)
  have hDD : HolderBound δ Q (spatialDD V) (16 * Ci) := holderBound_restrict hInit.2.2.2.1 hCore
  have hSj (j : ℕ) : HolderBound δ Q
      (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) (Cs j) :=
    holderBound_restrict (hBackground j σ τ hσ hσr hσ1 hτ a) hFull
  have hW (i : RIdx n) (ws : List (Space n)) (hws : NativeFrameWord ws) :
      SchauderBound δ Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] V)) (Cu ws.length) :=
    hWords ws.length h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a i ws hws rfl
  have hM := hBudget k Q (ball 0 1) δ S V isOpen_ball
    (fun p hp => ⟨(hCore hp).1, mem_univ p.2⟩)
    (fun p hp => shiftedComplexBackground_smooth_spatial_slice A hσ hσr τ a p.2)
    (fun p hp => contDiffOn_space_slice hV (hCore hp).2) hSj hDD hW
  apply holderBound_congr_on_native hM
  intro p hp
  have he : (fun z => chartPotentialMatrix S V (z, p.2)) =ᶠ[𝓝 p.1]
      (fun z => pullbackMatrix (h (τ + σ ^ 2 * p.2)) (A.chart a) (σ • z)) := by
    filter_upwards [isOpen_ball.mem_nhds (hCore hp).1] with z hz
    have ht := shifted_backward_clock_maps hσLower hUpper (hCore hp).2
    simpa only [affineParabolicPoint, add_zero] using
      shifted_native_flow_matrix_at hg A h U hσ.ne' hU hpot a (z, p.2)
        (spatialDilation_mem_ball hσ hσr hz) ht
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end Yau.NodeProofs.F01Aux
