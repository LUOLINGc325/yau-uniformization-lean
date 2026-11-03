import Yau.Proofs.E02PSDTraceSubsequence
import Yau.Proofs.E02PSDClosedLimit
import Yau.Proofs.V05Matrix

open Matrix Set Filter
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_lower_trace_bound {n : ℕ} (A K : Herm n) (c : ℝ)
    (hA : (A-(c:ℂ) • (1:Herm n)).PosSemidef) (hK : K.PosSemidef) :
    c*(Matrix.trace K).re ≤ (Matrix.trace (Aᵀ*K)).re := by
  have hh := V05Aux.trace_mul_nonneg hA.transpose hK
  have hr : 0 ≤ (Matrix.trace ((A-(c : ℂ) • (1 : Herm n))ᵀ*K)).re :=
    (RCLike.nonneg_iff.mp hh).1
  rw [Matrix.transpose_sub,Matrix.transpose_smul,Matrix.transpose_one,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul] at hr
  simpa only [Complex.sub_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,sub_nonneg] using hr

/-- Compactness of an ACTUAL PSD sequence removes one regularization
parameter. In E02 this is first applied at fixed κ and fixed Peano jets;
subsequent κ and weight limits are separate later applications. -/
theorem exists_psd_limit_of_coercive_trace_bound {n : ℕ}
    (Aseq Sseq Kseq : ℕ → Herm n) (A S : Herm n) (rseq : ℕ → ℝ) (r c R : ℝ)
    (hc : 0 < c) (hA : Tendsto Aseq atTop (𝓝 A)) (hS : Tendsto Sseq atTop (𝓝 S))
    (hr : Tendsto rseq atTop (𝓝 r))
    (hLower : ∀ j, (Aseq j-(c:ℂ) • (1:Herm n)).PosSemidef)
    (hK : ∀ j, (Kseq j).PosSemidef) (hDom : ∀ j, (Kseq j-Sseq j).PosSemidef)
    (hTrace : ∀ j, (Matrix.trace ((Aseq j)ᵀ*Kseq j)).re ≤ rseq j)
    (hR : ∀ j, rseq j ≤ R) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧ (Matrix.trace (Aᵀ*K)).re ≤ r := by
  have hBound : ∀ j, (Matrix.trace (Kseq j)).re ≤ R/c := by
    intro j
    apply (le_div_iff₀ hc).mpr
    have hb := (scalar_lower_trace_bound (Aseq j) (Kseq j) c (hLower j) (hK j)).trans
      ((hTrace j).trans (hR j))
    calc
      (Matrix.trace (Kseq j)).re*c = c*(Matrix.trace (Kseq j)).re := mul_comm _ _
      _ ≤ R := hb
  obtain ⟨K,_hK,φ,hφ,hKL⟩ := exists_psd_trace_subsequence Kseq (R/c) hK hBound
  have hφLim : Tendsto φ atTop atTop := hφ.tendsto_atTop
  refine ⟨K,?_⟩
  exact psd_majorant_trace_of_tendsto (Aseq ∘ φ) (Sseq ∘ φ) (Kseq ∘ φ)
    A S K (rseq ∘ φ) r (hA.comp hφLim) (hS.comp hφLim) hKL
    (hr.comp hφLim) (fun j => hK (φ j)) (fun j => hDom (φ j))
    (fun j => hTrace (φ j))

end Yau.NodeProofs.E02Aux
