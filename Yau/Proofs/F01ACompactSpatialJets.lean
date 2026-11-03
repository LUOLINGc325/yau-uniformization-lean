import Yau.Proofs.F01AllSpatialWordSchauder
import Yau.Proofs.F01SpatialWordsTensorJets
import Yau.Proofs.F01SchauderClosedRestriction

/-! The scalar-coordinate Schauder engine controls the full spatial
operator tensors on one fixed compact cylinder. Numerical coefficient
budgets are supplied by the fixed original chart, before every solution. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem compact_coordinate_spatial_jet_budgets
    (hn : 0 < n) {β D Ci : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hD : 1 ≤ D) (hCi : 0 < Ci) (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ k
      (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (d : Space n → ℝ),
      SchauderBound β (cylinder (ball 0 1) (-1) 1) u Ci →
      (∀ t ∈ Icc (-1 : ℝ) 1, ContDiffOn ℝ ∞ (fun z => S (z,t)) (ball 0 1)) →
      (∀ t ∈ Icc (-1 : ℝ) 1, ContDiffOn ℝ ∞ (fun z => u (z,t)) (ball 0 1)) →
      ContDiffOn ℝ ∞ d (ball 0 1) →
      (∀ j, HolderBound β (cylinder (ball 0 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ j (fun z => S (z,p.2)) p.1) (B j)) →
      (∀ j, HolderBound β (cylinder (ball 0 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ j d p.1) (B j)) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 1, (chartPotentialMatrix S u p).PosDef) →
      (∀ p ∈ cylinder (ball 0 1) (-1) 1,
        (chartPotentialMatrix S u p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - chartPotentialMatrix S u p).PosSemidef) →
      (∀ i : RIdx n, PotentialSpatialWordEquations S u d (realVec i)) →
      ∀ p ∈ cylinder (ball 0 (1 / 2)) (-(1 / 2)) (1 / 2),
        ‖iteratedFDeriv ℝ k (fun z => u (z,p.2)) p.1‖ ≤ K k := by
  classical
  choose Cu hCu hWords using all_spatial_word_schauder_budgets hn hβ hβ1 hD hCi.le B hB
  choose Ct hCt hTensor using fun k : ℕ => spatial_tensor_basis_norm_budget (n := n) k
  let W : ℕ → ℝ := fun k => max Ci (Cu (k - 1))
  have hW (k : ℕ) : 0 < W k := hCi.trans_le (le_max_left _ _)
  refine ⟨fun k => Ct k * W k, fun k => mul_pos (hCt k) (hW k), ?_⟩
  intro k S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq p hp
  have hCore : p ∈ cylinder (ball 0 1) (-1) 1 :=
    ⟨ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  apply hTensor k _ (W k) (hW k).le
  intro m
  let vs := List.ofFn (fun i : Fin k => realVec (m i))
  have hvs : NativeFrameWord vs := by
    intro v hv
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
    exact ⟨m i, hi.symm⟩
  have hLen : vs.length = k := List.length_ofFn
  have hValue : |spatialDerivativeWord vs u p| ≤ W k := by
    by_cases hv : vs = []
    · have hk : k = 0 := by simpa only [hv, List.length_nil] using hLen.symm
      simpa only [hv, spatialDerivativeWord] using
        ((hInitial.2.2.1 p hCore).1.trans (le_max_left Ci (Cu (k - 1))))
    · obtain ⟨ws, i, hEqvs, hws, hlength⟩ := native_word_last_decomposition hvs hv
      have hwsLen : ws.length = k - 1 := by omega
      have hw := hWords (k - 1) S u d hInitial hSs hus hd hSj hdj hPos hBounds hEq i ws hws hwsLen
      have hR := bootstrapRadius_bounds (k - 1 + 1)
      change SchauderBound β
        (cylinder (ball 0 (bootstrapRadius (k - 1 + 1))) (-bootstrapRadius (k - 1 + 1)) (1 / 2))
        (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) (Cu (k - 1)) at hw
      have hRestricted := schauderBound_closed_cylinder_restrict
        (a := -bootstrapRadius (k - 1 + 1)) (b := 1 / 2)
        (by norm_num : (-(1 / 2) : ℝ) < 1 / 2)
        (ball_subset_ball hR.1.le) (fun t ht => ⟨by linarith [ht.1, hR.1], ht.2⟩) hw
      rw [hEqvs, spatialDerivativeWord_append]
      exact (hRestricted.2.2.1 p hp).1.trans (le_max_right _ _)
  rw [← spatialDerivativeWord_ofFn_eq_iteratedFDeriv isOpen_ball (hus p.2 hCore.2) k _ hCore.1]
  exact hValue

end Yau.NodeProofs.F01Aux
