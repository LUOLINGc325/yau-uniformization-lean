import Yau.Proofs.D06HardyRadial

/-! The actual Fourier trace is a continuous linear map, so radial Hardy
convergence gives radial L² convergence for the same boundary functions. -/

open scoped lp Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyTraceLp_norm_le (a : HardySeq r) (j : Fin r) :
    ‖hardyTraceLp a j‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hardyTraceLp_norm_sq]
  have h : (∑' n : ℕ, ‖a (n, j)‖ ^ 2) ≤
      ∑ i : Fin r, ∑' n : ℕ, ‖a (n, i)‖ ^ 2 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    tsum_nonneg (fun n : ℕ => sq_nonneg ‖a (n, i)‖)) (Finset.mem_univ j)
  exact h.trans_eq (hardy_column_norm_sum a)

def hardyTraceLpLM (j : Fin r) : HardySeq r →ₗ[ℂ] Lp ℂ 2 hardyCircleMeasure where
  toFun a := hardyTraceLp a j
  map_add' a b := hardyTraceLp_add a b j
  map_smul' c a := hardyTraceLp_smul c a j

def hardyTraceLpCLM (j : Fin r) : HardySeq r →L[ℂ] Lp ℂ 2 hardyCircleMeasure :=
  (hardyTraceLpLM j).mkContinuous 1 (fun a => by
    change ‖hardyTraceLp a j‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using hardyTraceLp_norm_le a j)

theorem hardyTraceLp_radial_tendsto (s : ℕ → ℂ) (hs : ∀ n, ‖s n‖ ≤ 1)
    (hlim : Tendsto s atTop (𝓝 1)) (a : HardySeq r) (j : Fin r) :
    Tendsto (fun n => hardyTraceLp (hardyDilate (s n) (hs n) a) j)
      atTop (𝓝 (hardyTraceLp a j)) :=
  (hardyTraceLpCLM j).continuous.continuousAt.tendsto.comp (hardyDilate_tendsto s hs hlim a)

end Yau.NodeProofs.D06Aux
