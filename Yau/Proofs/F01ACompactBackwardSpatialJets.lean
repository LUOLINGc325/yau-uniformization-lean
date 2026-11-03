import Yau.Proofs.F01AllBackwardSpatialSchauder
import Yau.Proofs.F01AllPotentialSpatialJetHolder

/-! Fixed original-coordinate backward Schauder data give uniform full
spatial tensor budgets. The closed terminal face is retained throughout. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem compact_coordinate_backward_spatial_jet_budgets
    (hn : 0 < n) {β D Ci : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hD : 1 ≤ D) (hCi : 0 < Ci) (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (d : Space n → ℝ),
      SchauderBound β (cylinder (ball 0 1) (-1) 0) u Ci →
      (∀ t ∈ Icc (-1 : ℝ) 0, ContDiffOn ℝ ∞ (fun z => S (z,t)) (ball 0 1)) →
      (∀ t ∈ Icc (-1 : ℝ) 0, ContDiffOn ℝ ∞ (fun z => u (z,t)) (ball 0 1)) →
      ContDiffOn ℝ ∞ d (ball 0 1) →
      (∀ j, HolderBound β (cylinder (ball 0 1) (-1) 0)
        (fun p => iteratedFDeriv ℝ j (fun z => S (z,p.2)) p.1) (B j)) →
      (∀ j, HolderBound β (cylinder (ball 0 1) (-1) 0)
        (fun p => iteratedFDeriv ℝ j d p.1) (B j)) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 0, (chartPotentialMatrix S u p).PosDef) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 0,
        (chartPotentialMatrix S u p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - chartPotentialMatrix S u p).PosSemidef) →
      (∀ i : RIdx n, PotentialWordEquationsOn (cylinder (ball 0 1) (-1) 0) S u d (realVec i)) →
      ∀ k p, p ∈ cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0 →
        ‖iteratedFDeriv ℝ k (fun z => u (z,p.2)) p.1‖ ≤ K k := by
  classical
  choose Cu hCu hWords using backward_spatial_word_schauder_budgets hn hβ hβ1 hD hCi.le B hB
  obtain ⟨K, hK, hBudget⟩ := all_potential_spatial_jet_holder_budgets hCi hβ1.le Cu hCu
  refine ⟨K, hK, ?_⟩
  intro S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq
  have hInitialHalf : SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0) u Ci :=
    schauderBound_closed_cylinder_restrict (by norm_num)
      (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hInitial
  have hW (i : RIdx n) (ws : List (Space n)) (hws : NativeFrameWord ws) :
      SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
        (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) (Cu ws.length) := by
    have hw := hWords ws.length S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq i ws hws rfl
    have hR := bootstrapRadius_bounds (ws.length + 1)
    exact schauderBound_closed_cylinder_restrict (by norm_num : (-(1 / 2) : ℝ) < 0)
      (ball_subset_ball hR.1.le) (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hw
  have hb := hBudget u
    (fun t ht => (hus t ⟨by linarith [ht.1], ht.2⟩).mono
      (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))) hInitialHalf hW
  exact fun k p hp => (hb k).2.1 p hp

end Yau.NodeProofs.F01Aux
