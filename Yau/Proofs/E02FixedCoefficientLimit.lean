import Yau.Proofs.E02PSDTraceLimit
import Yau.Proofs.E02PosDefLower

open Matrix Filter Set
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- A single PSD subsequence is chosen using only the c/2 estimate.
All positive coefficient losses are then removed with that SAME limit. -/
theorem exists_psd_limit_forall_coefficient_losses {n : ℕ}
    (B : Herm n) (hB : B.PosDef) (Kseq Sseq : ℕ → Herm n) (S : Herm n)
    (rseq : ℕ → ℝ) (r c : ℝ) (hc : 0 < c)
    (hK : ∀ j, (Kseq j).PosSemidef) (hDom : ∀ j, (Kseq j-Sseq j).PosSemidef)
    (hS : Tendsto Sseq atTop (𝓝 S)) (hr : Tendsto rseq atTop (𝓝 r))
    (hLoss : ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
      (c-δ)*(Matrix.trace (Bᵀ*Kseq j)).re ≤ rseq j) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧
      c*(Matrix.trace (Bᵀ*K)).re ≤ r := by
  obtain ⟨β,hβ,hLower⟩ := posDef_exists_scalar_lower B hB
  have hHalf : 0 < c/2 := by positivity
  obtain ⟨R,hR⟩ := hr.bddAbove_range
  have hCap : ∀ᶠ j in atTop, (Matrix.trace (Kseq j)).re ≤ R/((c/2)*β) := by
    filter_upwards [hLoss (c/2) hHalf] with j hj
    apply (le_div_iff₀ (mul_pos hHalf hβ)).mpr
    have hOne := mul_le_mul_of_nonneg_left
      (scalar_lower_trace_bound B (Kseq j) β hLower (hK j)) hHalf.le
    have hRj : rseq j ≤ R := hR (mem_range_self j)
    nlinarith
  obtain ⟨Rcap,hRcap⟩ := (isBoundedUnder_of_eventually_le hCap).bddAbove_range
  obtain ⟨K,hK0,φ,hφ,hKL⟩ := exists_psd_trace_subsequence Kseq Rcap hK
    (fun j => hRcap (mem_range_self j))
  have hφLim : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hSSub := hS.comp hφLim
  have hDom0 : (K-S).PosSemidef := posSemidef_sub_of_tendsto
    (Kseq ∘ φ) (Sseq ∘ φ) K S hKL hSSub (fun j => hDom (φ j))
  have hCont : Continuous (fun L : Herm n => (Matrix.trace (Bᵀ*L)).re) :=
    Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace
  have hTL : Tendsto (fun j => (Matrix.trace (Bᵀ*Kseq (φ j))).re)
      atTop (𝓝 (Matrix.trace (Bᵀ*K)).re) := (hCont.tendsto K).comp hKL
  have hEvery : ∀ δ : ℝ, 0 < δ → (c-δ)*(Matrix.trace (Bᵀ*K)).re ≤ r := by
    intro δ hδ
    exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hTL) (hr.comp hφLim)
      (hφLim.eventually (hLoss δ hδ))
  refine ⟨K,hK0,hDom0,?_⟩
  have hSelf : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  have hNear : ∀ᶠ δ in 𝓝[>] (0:ℝ), (c-δ)*(Matrix.trace (Bᵀ*K)).re ≤ r :=
    hSelf.mono (fun δ hδ => hEvery δ hδ)
  have hAt : ContinuousAt (fun δ : ℝ => (c-δ)*(Matrix.trace (Bᵀ*K)).re) 0 := by fun_prop
  have hResult := le_of_tendsto (hAt.tendsto.mono_left nhdsWithin_le_nhds) hNear
  simpa only [sub_zero] using hResult

end Yau.NodeProofs.E02Aux
