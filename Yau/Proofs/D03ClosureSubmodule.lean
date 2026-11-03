import Yau.Proofs.D03ClosureSubmoduleIntegral
import Yau.Proofs.D03ClosureSubmoduleAnalytic

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Metric Bundle

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Membership records an actual original local section with one positive exponent. -/
def extraImageGermCarrier (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (g : Fin q → AnalyticGerm) : Prop :=
  ∃ ρ ε : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < ε ∧ ∃ b : Section E,
    HolomorphicSectionOn (r := r) E b (discSectionDomain c ρ) ∧
    weightedSectionIntegral E c k b ρ ε < ⊤ ∧
    ∃ F : ℂ → ComplexVector q, ∃ hF0 : AnalyticAt ℂ F 0,
      DifferentiableOn ℂ F (ball 0 ρ) ∧ vectorGerm F hF0 = g ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → F z = A (c.symm z) (b (c.symm z))

theorem extraImageGermCarrier_zero (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) : extraImageGermCarrier (r := r) E c k A 0 := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, fun _ => 0,
    holomorphicSectionOn_zero E _, ?_, fun _ => 0, analyticAt_const,
    differentiableOn_const _, vectorGerm_zero q, ?_⟩
  · rw [closure_weighted_zero E]
    exact ENNReal.zero_lt_top
  · intro z _ _
    exact (map_zero (A (c.symm z))).symm

theorem extraImageGermCarrier_add (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) {g h : Fin q → AnalyticGerm}
    (hg : extraImageGermCarrier (r := r) E c k A g)
    (hh : extraImageGermCarrier (r := r) E c k A h) :
    extraImageGermCarrier (r := r) E c k A (g + h) := by
  rcases hg with ⟨ρ, ε, hρ, hρ1, hε, b, hb, hbI, F, hF0, hF, hFg, hFb⟩
  rcases hh with ⟨τ, η, hτ, hτ1, hη, d, hd, hdI, G, hG0, hG, hGh, hGd⟩
  have hb' := holomorphicSectionOn_mono E hb (discSectionDomain_mono c (min_le_left ρ τ))
  have hd' := holomorphicSectionOn_mono E hd (discSectionDomain_mono c (min_le_right ρ τ))
  have hbI' : weightedSectionIntegral E c k b (min ρ τ) (min ε η) < ⊤ :=
    lt_of_le_of_lt ((closure_weighted_exponent_mono E c hc k b _ (min_le_left ε η)).trans
      (closure_weighted_radius_mono E c k b (min_le_left ρ τ) ε)) hbI
  have hdI' : weightedSectionIntegral E c k d (min ρ τ) (min ε η) < ⊤ :=
    lt_of_le_of_lt ((closure_weighted_exponent_mono E c hc k d _ (min_le_right ε η)).trans
      (closure_weighted_radius_mono E c k d (min_le_right ρ τ) η)) hdI
  refine ⟨min ρ τ, min ε η, lt_min hρ hτ, (min_le_left ρ τ).trans_lt hρ1,
    lt_min hε hη, fun x => b x + d x, holomorphicSectionOn_add E hb' hd', ?_,
    F + G, hF0.add hG0, (hF.mono (ball_subset_ball (min_le_left ρ τ))).add
      (hG.mono (ball_subset_ball (min_le_right ρ τ))), ?_, ?_⟩
  · apply lt_of_le_of_lt (closure_weighted_add_le E c hc k hk b d _ _ hb')
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hbI', ENNReal.mul_lt_top (by norm_num) hdI'⟩
  · rw [vectorGerm_add F G hF0 hG0, hFg, hGh]
  · intro z hz hzρ
    change F z + G z = A (c.symm z) (b (c.symm z) + d (c.symm z))
    rw [hFb z hz (hzρ.trans_le (min_le_left ρ τ)),
      hGd z hz (hzρ.trans_le (min_le_right ρ τ)), map_add]

theorem extraImageGermCarrier_smul (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (A : MapToTrivial E q) (a : AnalyticGerm)
    {g : Fin q → AnalyticGerm} (hg : extraImageGermCarrier (r := r) E c k A g) :
    extraImageGermCarrier (r := r) E c k A (a • g) := by
  rcases hg with ⟨ρ, ε, hρ, hρ1, hε, b, hb, hbI, F, hF0, hF, hFg, hFb⟩
  obtain ⟨f, hf0, R, B, hR, hB, hf, hfB, hfa⟩ := closure_analyticGerm_bounded a
  let δ := min ρ R / 2
  have hδ : 0 < δ := half_pos (lt_min hρ hR)
  have hδρ : δ ≤ ρ := (half_le_self (le_of_lt (lt_min hρ hR))).trans (min_le_left ρ R)
  have hδR : δ ≤ R := (half_le_self (le_of_lt (lt_min hρ hR))).trans (min_le_right ρ R)
  have hδ1 : δ < 1 := hδρ.trans_lt hρ1
  have hb' := holomorphicSectionOn_mono E hb (discSectionDomain_mono c hδρ)
  refine ⟨δ, ε, hδ, hδ1, hε, fun x => f (c x) • b x,
    closure_holomorphicSectionOn_scalar E c hc f R hf δ hδR b hb', ?_,
    (fun z => f z • F z), hf0.smul hF0,
    (hf.mono (ball_subset_ball hδR)).smul (hF.mono (ball_subset_ball hδρ)), ?_, ?_⟩
  · apply lt_of_le_of_lt (closure_weighted_smul_le E c hc k b δ ε B hB (fun x => f (c x)) ?_)
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((closure_weighted_radius_mono E c k b hδρ ε).trans_lt hbI)
    · intro x hx
      exact hfB (c x) (by rw [mem_ball_zero_iff]; exact hx.2.trans_le hδR)
  · rw [vectorGerm_smul f F hf0 hF0, hfa, hFg]
  · intro z hz hzδ
    change f z • F z = A (c.symm z) (f (c (c.symm z)) • b (c.symm z))
    rw [hFb z hz (hzδ.trans_le hδρ), map_smul,
      B01Aux.disc_right_inv c hc (show z ∈ puncturedUnitDisc from ⟨hz, hzδ.trans hδ1⟩)]

/-- The actual extra-integrable image germs form a module over the analytic local ring. -/
def extraImageGerms (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) : Submodule AnalyticGerm (Fin q → AnalyticGerm) where
  carrier := extraImageGermCarrier (r := r) E c k A
  zero_mem' := extraImageGermCarrier_zero E c k A
  add_mem' := extraImageGermCarrier_add E c hc k hk A
  smul_mem' := extraImageGermCarrier_smul E c hc k A

@[simp] theorem mem_extraImageGerms (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) (g : Fin q → AnalyticGerm) :
    g ∈ extraImageGerms E c hc k hk A ↔ extraImageGermCarrier (r := r) E c k A g := Iff.rfl

end Yau.Proofs.D03Aux
