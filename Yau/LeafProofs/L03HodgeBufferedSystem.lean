import Yau.LeafProofs.L03HodgeLocalWeak
import Yau.LeafProofs.L03HodgeCoercivity

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

theorem divergenceSystemWeakEquation_coeff_congr {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [Fintype α] [Fintype ι]
    (ν : Measure E) (v : ι → E)
    (a a' : β → α → ι → ι → E → ℝ)
    (B B' : β → α → ι → E → ℝ) (C C' : β → α → E → ℝ)
    (u : E → α → ℝ) (F0 : E → β → ℝ) (F : E → β → ι → ℝ)
    (hweak : divergenceSystemWeakEquation ν v a B C u F0 F)
    (ha : ∀ x c, u x c ≠ 0 → ∀ r i j, a' r c i j =ᶠ[𝓝 x] a r c i j)
    (hB : ∀ x c, u x c ≠ 0 → ∀ r i, B' r c i x = B r c i x)
    (hC : ∀ x c, u x c ≠ 0 → ∀ r, C' r c x = C r c x) :
    divergenceSystemWeakEquation ν v a' B' C' u F0 F := by
  intro r φ hφ hcφ
  have hp (c : α) (i j : ι) : (∫ x,
      (a' r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
        fderiv ℝ (a' r c i j) x (v j) * fderiv ℝ φ x (v i)) * u x c ∂ν) =
      ∫ x, (a r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
        fderiv ℝ (a r c i j) x (v j) * fderiv ℝ φ x (v i)) * u x c ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : u x c = 0
      · simp only [hx, mul_zero]
      · rw [(ha x c hx r i j).eq_of_nhds, (ha x c hx r i j).fderiv_eq]
  have hb (c : α) (i : ι) : (∫ x, (B' r c i x * fderiv ℝ φ x (v i)) * u x c ∂ν) =
      ∫ x, (B r c i x * fderiv ℝ φ x (v i)) * u x c ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : u x c = 0
      · simp only [hx, mul_zero]
      · rw [hB x c hx r i]
  have hc (c : α) : (∫ x, φ x * (C' r c x * u x c) ∂ν) =
      ∫ x, φ x * (C r c x * u x c) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : u x c = 0
      · simp only [hx, mul_zero]
      · rw [hC x c hx r]
  simpa only [hp, hb, hc] using hweak r φ hφ hcφ

namespace HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

/-- A genuine compact chart buffer and bounded smooth coefficient
extensions for the actual localized rough Hodge equation. Coercivity is
asserted only on that buffer, where the extensions equal the actual fields. -/
theorem exists_buffered_localized_divergence_system {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ Ω : Set (ComplexVector n), IsOpen Ω ∧ tsupport χ ⊆ Ω ∧ IsCompact (closure Ω) ∧
      closure Ω ⊆ chartTarget x ∧ ∃ θ : ComplexVector n → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ chartTarget x ∧
      (∀ z ∈ closure Ω, θ z = 1) ∧
      (∀ r c i j, ContDiff ℝ ∞ (fun z => θ z * a g.form x b r c i j z)) ∧
      (∀ r c i, ContDiff ℝ ∞ (fun z => θ z * B g.form x b r c i z)) ∧
      (∀ r c, ContDiff ℝ ∞ (fun z => θ z * C g.form x b r c z)) ∧
      divergenceSystemWeakEquation (lebesgueC n) (realModelBasis n)
        (fun r c i j z => θ z * a g.form x b r c i j z)
        (fun r c i z => θ z * B g.form x b r c i z)
        (fun r c z => θ z * C g.form x b r c z)
        (localizedInput x b χ A) (localizedValue g.form x b χ A) (localizedFlux g.form x b χ A) ∧
      ∃ ell : ℝ, 0 < ell ∧ ∀ z ∈ closure Ω, ∀ ξ : RIdx n × α → ℝ,
        ell * (∑ p, (ξ p) ^ 2) ≤
          ∑ r, ∑ c, ∑ i, ∑ j, (θ z * a g.form x b r c i j z) * ξ (j, c) * ξ (i, r) := by
  classical
  obtain ⟨Ω, hΩ, hKΩ, hΩO, hcΩ⟩ := exists_open_between_and_isCompact_closure hcχ
    (isOpen_extChartAt_target (I := ComplexModel n) x) hχO
  obtain ⟨θ, hθ, hcθ, hθO, _, hθone⟩ := exists_model_chart_cutoff
    (isOpen_extChartAt_target (I := ComplexModel n) x) hcΩ hΩO
  have hθK (z : ComplexVector n) (hz : z ∈ closure Ω) : θ z = 1 := (hθone z hz).1
  refine ⟨Ω, hΩ, hKΩ, hcΩ, hΩO, θ, hθ, hcθ, hθO, hθK, ?_, ?_, ?_, ?_, ?_⟩
  · intro r c i j
    exact (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      θ hθ hcθ hθO _ (a_contDiffOn g x b r c i j)).1
  · intro r c i
    exact (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      θ hθ hcθ hθO _ (B_contDiffOn g x b r c i)).1
  · intro r c
    exact (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      θ hθ hcθ hθO _ (C_contDiffOn g x b r c)).1
  · apply divergenceSystemWeakEquation_coeff_congr (lebesgueC n) (realModelBasis n)
      (a g.form x b) _ (B g.form x b) _ (C g.form x b) _
      (localizedInput x b χ A) (localizedValue g.form x b χ A) (localizedFlux g.form x b χ A)
      (maximalGraph_localized_divergenceWeak g μ hμ A hmax x b χ hχ hcχ hχO)
    · intro z c hz r i j
      have hzχ : z ∈ tsupport χ := by
        by_contra hn
        exact hz (by simp only [localizedInput, image_eq_zero_of_notMem_tsupport hn, zero_mul])
      filter_upwards [hΩ.mem_nhds (hKΩ hzχ)] with y hy
      rw [hθK y (subset_closure hy), one_mul]
    · intro z c hz r i
      have hzχ : z ∈ tsupport χ := by
        by_contra hn
        exact hz (by simp only [localizedInput, image_eq_zero_of_notMem_tsupport hn, zero_mul])
      rw [hθK z (subset_closure (hKΩ hzχ)), one_mul]
    · intro z c hz r
      have hzχ : z ∈ tsupport χ := by
        by_contra hn
        exact hz (by simp only [localizedInput, image_eq_zero_of_notMem_tsupport hn, zero_mul])
      rw [hθK z (subset_closure (hKΩ hzχ)), one_mul]
  · obtain ⟨ell, hell, hb⟩ := a_uniform_coercivity g x b hcΩ hΩO
    refine ⟨ell, hell, ?_⟩
    intro z hz ξ
    simpa only [hθK z hz, one_mul] using hb z hz ξ

end HodgeDivergenceWeak

end Yau.LeafProofs.L03
