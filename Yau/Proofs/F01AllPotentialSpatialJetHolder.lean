import Yau.Proofs.F01SchauderValueHolder
import Yau.Proofs.F01SpatialSchauderWords
import Yau.Proofs.F01SchauderClosedRestriction

/-! The genuine Schauder estimates for every native derivative word
control all full spatial potential jets, including orders zero and one.
Constants precede the realized potential. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem all_potential_spatial_jet_holder_budgets
    {Ci β : ℝ} (hCi : 0 < Ci) (hβ : β ≤ 1)
    (Cu : ℕ → ℝ) (hCu : ∀ k, 0 < Cu k) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ u : Point n → ℝ,
      (∀ t ∈ Icc (-(1 / 2) : ℝ) 0,
        ContDiffOn ℝ ∞ (fun x => u (x, t)) (ball 0 (1 / 2))) →
      SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0) u Ci →
      (∀ (i : RIdx n) (ws : List (Space n)), NativeFrameWord ws →
        SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
          (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) (Cu ws.length)) →
      ∀ k, HolderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
        (fun p => iteratedFDeriv ℝ k (fun x => u (x, p.2)) p.1) (B k) := by
  classical
  have each := fun k : ℕ => spatial_words_tensor_holder_budget (n := n) k
  choose D hD hTensor using each
  let W : ℕ → ℝ := fun k => max Ci (Cu (k - 1))
  have hW (k : ℕ) : 0 < W k := hCi.trans_le (le_max_left _ _)
  refine ⟨fun k => D k * W k, fun k => mul_pos (hD k) (hW k), ?_⟩
  intro u hu hInit hAll k
  apply hTensor k (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
    (ball 0 (1 / 2)) β (W k) isOpen_ball (hW k).le
    (fun p hp => ⟨hp.1, mem_univ _⟩) u (fun p hp => hu p.2 hp.2)
  intro m
  let vs := List.ofFn (fun i : Fin k => realVec (m i))
  have hvs : NativeFrameWord vs := by
    intro v hv
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hv
    exact ⟨m i, hi.symm⟩
  have hLen : vs.length = k := List.length_ofFn
  have hWord : SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
      (spatialDerivativeWord vs u) (W k) := by
    by_cases hEmpty : vs = []
    · simpa only [hEmpty, spatialDerivativeWord] using
        schauderBound_mono_const hInit (le_max_left Ci (Cu (k - 1)))
    · obtain ⟨ws, i, hEq, hws, hlength⟩ := native_word_last_decomposition hvs hEmpty
      have hwLen : ws.length = k - 1 := by omega
      rw [hEq, spatialDerivativeWord_append]
      apply schauderBound_mono_const (hAll i ws hws)
      rw [hwLen]
      exact le_max_right _ _
  exact schauder_fixed_core_value_holder hβ hWord

end Yau.NodeProofs.F01Aux
