import Yau.Proofs.F01CompactJets
import Yau.Proofs.F01ShiftedAffineTensorHolder
import Yau.Proofs.F01ChartLogDet
import Yau.Proofs.F01ComplexLeviFrobenius
import Yau.Proofs.F01MatrixSmooth

/-! Fixed original-coordinate coefficient budgets. The only compact set is
inside one original holomorphic chart. No approximating bounded-geometry
chart family enters these constants. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem compact_smooth_uniform_jet_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} {r : ℝ} {f : E → F}
    (hΩ : IsOpen Ω) (hball : closedBall 0 r ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (k : ℕ) :
    UniformJetBounds k (fun _ : Unit => f) (fun _ => ball 0 r) := by
  classical
  obtain ⟨C, hC, hb⟩ := compact_all_derivative_budgets hΩ (isCompact_closedBall _ _) hball hf
  let B : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), C j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  refine ⟨B, by dsimp only [B]; linarith, ?_⟩
  intro i x hx j hj
  have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hle : C j ≤ ∑ j ∈ Finset.range (k + 1), C j :=
    Finset.single_le_sum (fun l _ => (hC l).le) hmem
  exact (hb j x (ball_subset_closedBall hx)).trans (by dsimp only [B]; linarith)

theorem fixed_compact_initial_coefficient_budgets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Space n)} {r β : ℝ} {f g : Space n → F}
    (hΩ : IsOpen Ω) (hball : closedBall 0 r ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) (hβ : β ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ k ρ,
      0 < ρ → ρ ≤ r → ρ ≤ 1 → ∀ κ : ℝ, |κ| ≤ 1 →
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k
          (fun z => f (ρ • z) + max p.2 0 • (κ • g (ρ • z))) p.1) (K k) := by
  have hsub : ball (0 : Space n) r ⊆ Ω := ball_subset_closedBall.trans hball
  have hex (k : ℕ) := dilated_affine_spatial_tensor_holder_budget k
    (compact_smooth_uniform_jet_bounds hΩ hball hf (k + 1))
    (compact_smooth_uniform_jet_bounds hΩ hball hg (k + 1))
    (fun _ : Unit => hf.mono hsub) (fun _ : Unit => hg.mono hsub) hβ
  choose K hK hb using hex
  exact ⟨K, hK, fun k ρ hρ hρr hρ1 κ hκ => hb k ρ hρ hρr hρ1 κ hκ ()⟩

theorem fixed_compact_backward_coefficient_budgets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Space n)} {r β T : ℝ} {f g : Space n → F}
    (hΩ : IsOpen Ω) (hball : closedBall 0 r ⊆ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (hT : 0 ≤ T) (hβ : β ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ k ρ τ κ,
      0 < ρ → ρ ≤ r → ρ ≤ 1 → |τ| ≤ T → |κ| ≤ 1 →
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k
          (fun z => f (ρ • z) + (τ + κ * p.2) • g (ρ • z)) p.1) (K k) := by
  have hsub : ball (0 : Space n) r ⊆ Ω := ball_subset_closedBall.trans hball
  have hex (k : ℕ) := shifted_affine_spatial_tensor_holder_budget k hT
    (compact_smooth_uniform_jet_bounds hΩ hball hf (k + 1))
    (compact_smooth_uniform_jet_bounds hΩ hball hg (k + 1))
    (fun _ : Unit => hf.mono hsub) (fun _ : Unit => hg.mono hsub) hβ
  choose K hK hb using hex
  exact ⟨K, hK, fun k ρ τ κ hρ hρr hρ1 hτ hκ => hb k ρ τ κ hρ hρr hρ1 hτ hκ ()⟩

theorem original_chart_background_smooth (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    ContDiffOn ℝ ∞ (fun z => pullbackMatrix g e z) e.source ∧
    ContDiffOn ℝ ∞ (backgroundRicci (pullbackMatrix g e)) e.source ∧
    ContDiffOn ℝ ∞ (fun z => Real.log (pullbackMatrix g e z).det.re) e.source := by
  have hq := pullback_logdet_contDiffOn g hg e he hei
  refine ⟨matrix_contDiffOn_of_entries (fun i j =>
    pullbackMatrix_entry_contDiffOn g hg e he i j), ?_, hq⟩
  have hqq := (hq.fderiv_of_isOpen e.open_source (m := ∞) (by simp)).fderiv_of_isOpen
    e.open_source (m := ∞) (by simp)
  apply ((-leviSecondMatrixCLM).contDiff.comp_contDiffOn hqq).congr
  intro z hz
  change -leviC (fun w => Real.log (pullbackMatrix g e w).det.re) z =
    -leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ (fun w => Real.log (pullbackMatrix g e w).det.re)) z)
  exact congrArg Neg.neg (leviSecondMatrixCLM_eq_native
    ((hq.contDiffAt (e.open_source.mem_nhds hz)).of_le (by simp))).symm

end Yau.NodeProofs.F01Aux
