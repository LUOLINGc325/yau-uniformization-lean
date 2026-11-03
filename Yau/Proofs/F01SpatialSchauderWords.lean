import Yau.Proofs.F01NativeFrameWordHolder
import Yau.Proofs.F01CommutatorSourceHolder

/-! Previous genuine Schauder estimates supply the next word's
supremum and the potential Hessians needed for the transformed matrix.
No derivative of the current unknown Hessian enters these reductions. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem word_cons_sup_of_schauder
    {Q : Set (Point n)} {β C : ℝ} {u : Point n → ℝ}
    (vs : List (Space n)) {v : Space n} (hv : ‖v‖ ≤ 1)
    (hu : SchauderBound β Q (spatialDerivativeWord vs u) C) :
    ∀ p ∈ Q, |spatialDerivativeWord (v :: vs) u p| ≤ C := by
  intro p hp
  change |spatialD (spatialDerivativeWord vs u) p v| ≤ C
  have he := (spatialD (spatialDerivativeWord vs u) p).le_opNorm v
  rw [Real.norm_eq_abs] at he
  exact he.trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans (hu.2.2.1 p hp).2)

theorem native_word_last_decomposition {vs : List (Space n)}
    (hvs : NativeFrameWord vs) (hne : vs ≠ []) :
    ∃ (ws : List (Space n)) (i : RIdx n),
      vs = ws ++ [realVec i] ∧ NativeFrameWord ws ∧ ws.length + 1 = vs.length := by
  obtain ⟨i, hi⟩ := hvs (vs.getLast hne) (List.getLast_mem hne)
  refine ⟨vs.dropLast, i, ?_, ?_, ?_⟩
  · rw [← hi]
    exact (List.dropLast_append_getLast hne).symm
  · intro v hv
    exact hvs v (List.mem_of_mem_dropLast hv)
  · have he := congrArg List.length (List.dropLast_append_getLast hne)
    simpa only [List.length_append, List.length_singleton] using he

theorem potential_word_hessian_from_previous
    {Q : Set (Point n)} {β C : ℝ} {u : Point n → ℝ} {order : ℕ}
    (hInitial : HolderBound β Q (spatialDD u) C)
    (hPrevious : ∀ (i : RIdx n) (ws : List (Space n)), NativeFrameWord ws →
      ws.length < order → SchauderBound β Q
        (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) C) :
    ∀ vs : List (Space n), NativeFrameWord vs → vs.length ≤ order →
      HolderBound β Q (spatialDD (spatialDerivativeWord vs u)) C := by
  intro vs hvs hlen
  by_cases he : vs = []
  · simpa only [he, spatialDerivativeWord] using hInitial
  · obtain ⟨ws, i, rfl, hws, hlength⟩ := native_word_last_decomposition hvs he
    rw [spatialDerivativeWord_append]
    exact (hPrevious i ws hws (by simp only [List.length_append, List.length_singleton] at hlen; omega)).2.2.2.1

end Yau.NodeProofs.F01Aux
