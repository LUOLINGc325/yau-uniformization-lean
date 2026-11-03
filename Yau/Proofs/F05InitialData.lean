import Yau.Proofs.F05Scalar

/-! Compatible initial and lateral data for the nonlinear compact-domain problem. -/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.F05Aux

theorem exists_time_cutoff : ∃ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ ∧
    (∀ t, 0 ≤ ζ t ∧ ζ t ≤ 1) ∧ ζ =ᶠ[𝓝 0] (fun _ => 1) ∧ ∀ t, 1 ≤ t → ζ t = 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, fun t => ⟨b.nonneg, b.le_one⟩, b.eventuallyEq_one, ?_⟩
  intro t ht
  apply b.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ t)] using ht

def cornerBoundary (ρ : ℝ → ℝ) (α R δ : ℝ) (ζ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ρ t + α - Real.exp (-α) * R * t * ζ (t / δ)

theorem cornerBoundary_initial (ρ : ℝ → ℝ) (α R δ : ℝ) (ζ : ℝ → ℝ)
    (hρ : ρ 0 = 0) : cornerBoundary ρ α R δ ζ 0 = α := by
  simp [cornerBoundary, hρ]

theorem cornerBoundary_hasDerivWithinAt (ρ : ℝ → ℝ) (α R δ : ℝ) (ζ : ℝ → ℝ)
    (hρ : HasDerivWithinAt ρ R (Set.Ici 0) 0)
    (hζ : ζ =ᶠ[𝓝 0] (fun _ => 1)) :
    HasDerivWithinAt (cornerBoundary ρ α R δ ζ)
      ((1 - Real.exp (-α)) * R) (Set.Ici 0) 0 := by
  have hz : (fun t : ℝ => ζ (t / δ)) =ᶠ[𝓝 0] (fun _ => 1) :=
    hζ.comp_tendsto (by
      simpa using ((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).div_const δ).tendsto)
  have heq : cornerBoundary ρ α R δ ζ =ᶠ[𝓝 0]
      (fun t => ρ t + α - (Real.exp (-α) * R) * t) := by
    filter_upwards [hz] with t ht
    simp only [cornerBoundary, ht, mul_one]
  have h := (hρ.add_const α).sub ((hasDerivAt_id (0 : ℝ)).const_mul (Real.exp (-α) * R)).hasDerivWithinAt
  convert h.congr_of_eventuallyEq_of_mem (heq.filter_mono nhdsWithin_le_nhds)
    (by simp : (0 : ℝ) ∈ Set.Ici 0) using 1
  ring

theorem time_cutoff_product_bounds (ζ : ℝ → ℝ) (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t)
    (hζ : ∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) (hsupp : ∀ s, 1 ≤ s → ζ s = 0) :
    0 ≤ t * ζ (t / δ) ∧ t * ζ (t / δ) ≤ δ := by
  refine ⟨mul_nonneg ht (hζ _).1, ?_⟩
  by_cases htd : t ≤ δ
  · exact (mul_le_of_le_one_right ht (hζ _).2).trans htd
  · rw [hsupp _ ((le_div_iff₀ hδ).mpr (by linarith)), mul_zero]
    exact hδ.le

theorem cornerBoundary_bounds (ρ : ℝ → ℝ) (α R δ t : ℝ) (ζ : ℝ → ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hδ : 0 < δ) (ht : 0 ≤ t)
    (hζ : ∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) (hsupp : ∀ s, 1 ≤ s → ζ s = 0)
    (hsmall : δ * R ≤ α / 2) :
    ρ t + α / 2 ≤ cornerBoundary ρ α R δ ζ t ∧
      cornerBoundary ρ α R δ ζ t ≤ ρ t + α := by
  have hb := time_cutoff_product_bounds ζ δ t hδ ht hζ hsupp
  have hexp : Real.exp (-α) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcorr0 : 0 ≤ Real.exp (-α) * R * (t * ζ (t / δ)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hR) hb.1
  have hcorr : Real.exp (-α) * R * (t * ζ (t / δ)) ≤ α / 2 := by
    calc
      _ ≤ (1 : ℝ) * R * δ := mul_le_mul
        (mul_le_mul_of_nonneg_right hexp hR) hb.2 hb.1 (by positivity)
      _ ≤ α / 2 := by simpa only [one_mul, mul_comm R δ] using hsmall
  unfold cornerBoundary
  constructor <;> nlinarith

/-- A single scale works for every boundary curvature below a fixed bound. -/
theorem exists_uniform_corner_scale (α M : ℝ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, R ≤ M → δ * R ≤ α / 2 := by
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨α / (2 * B), div_pos hα (by positivity), ?_⟩
  intro R hR
  have hRB : R ≤ B := hR.trans ((le_max_left M 0).trans (by dsimp [B]; linarith))
  have heq : α / (2 * B) * B = α / 2 := by field_simp
  exact (mul_le_mul_of_nonneg_left hRB (div_pos hα (by positivity)).le).trans_eq heq

end Yau.Proofs.F05Aux
