import Yau.Proofs.F01NativeBackwardMatrixJets
import Yau.Proofs.F01InverseTensorDilation
import Yau.Proofs.F01FrobeniusEntryJetBounds
import Yau.Proofs.F01ChartGramSmooth

/-! Recover all genuine coefficient jets in the original holomorphic
charts. The fixed inverse spatial scale and finite entry-evaluation
constant are selected before every flow and terminal/chart center. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem physical_native_chart_jet_budgets
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      SmoothSpaceTime U (Icc 0 T) → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) → MetricSmooth (h τ) →
      ∀ (a : M.Carrier) (z : Space n), z ∈ ball 0 (ρ / 8) → ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ k (fun w => pullbackMatrix (h τ) (A.chart a) w i j) z‖ ≤ B k := by
  classical
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσr : σ ≤ A.radius := (show σ ≤ ρ by dsimp only [σ]; linarith [hρ.le]).trans hρr
  obtain ⟨K, hK, hNative⟩ := native_backward_matrix_jet_budgets g hg A
    hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  have each := fun k : ℕ => inverse_spatial_jet_budget (E := Space n)
    (F := Matrix (Fin n) (Fin n) ℂ) k hσ.ne'
  choose I hI hInverse using each
  obtain ⟨E, hE, hEntry⟩ := frobenius_entry_common_budget n
  refine ⟨fun k => E * (I k * K k), fun k => mul_pos hE (mul_pos (hI k) (hK k)), ?_⟩
  intro k h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow hτ a z hz i j
  let f := fun w => pullbackMatrix (h τ) (A.chart a) w
  have hf : ContDiffOn ℝ ∞ f (ball 0 A.radius) :=
    matrix_contDiffOn_of_entries (fun i j =>
      (pullbackMatrix_entry_contDiffOn (h τ) hτ (A.chart a) (A.differentiable a) i j).mono
        (ball_subset_closedBall.trans (A.closedBall_source a)))
  let x := σ⁻¹ • z
  have hzNorm : ‖z‖ < σ / 2 := by
    have hh : ‖z‖ < ρ / 8 := by simpa only [mem_ball, dist_zero_right] using hz
    dsimp only [σ]
    linarith
  have hx : x ∈ ball (0 : Space n) (1 / 2) := by
    rw [mem_ball, dist_zero_right]
    change ‖σ⁻¹ • z‖ < 1 / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    calc
      _ < σ⁻¹ * (σ / 2) := mul_lt_mul_of_pos_left hzNorm (inv_pos.mpr hσ)
      _ = 1 / 2 := by field_simp [hσ.ne']
  have hσx : σ • x = z := by dsimp only [x]; rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  have hxOld : σ • x ∈ ball 0 A.radius :=
    spatialDilation_mem_ball hσ hσr (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hx)
  have hzOld : z ∈ ball 0 A.radius := by simpa only [hσx] using hxOld
  have hN := hNative k h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a
  have hp : (x, (0 : ℝ)) ∈ cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0 := ⟨hx, by norm_num, le_rfl⟩
  have hScaled : ‖iteratedFDeriv ℝ k (fun w => f (σ • w)) x‖ ≤ K k := by
    simpa only [mul_zero, add_zero] using hN.2.1 (x, 0) hp
  have hPhysical := hInverse k (ball 0 A.radius) f x (K k) isOpen_ball hf hxOld hScaled
  rw [hσx] at hPhysical
  exact (frobenius_entry_iteratedFDeriv_norm_le isOpen_ball hf hzOld k i j).trans
    (mul_le_mul (hEntry i j) hPhysical (norm_nonneg _) hE.le)

end Yau.NodeProofs.F01Aux
