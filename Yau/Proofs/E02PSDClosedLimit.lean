import Yau.Proofs.E02MatrixBasic
import Mathlib.Analysis.Matrix.Order

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_matrix_trace_pair (n : ℕ) :
    Continuous (fun p : Herm n × Herm n => (Matrix.trace (p.1ᵀ*p.2)).re) := by
  have hTranspose : Continuous (fun p : Herm n × Herm n => p.1ᵀ) :=
    continuous_fst.matrix_transpose
  have hMultiply : Continuous (fun p : Herm n × Herm n => p.1ᵀ*p.2) :=
    hTranspose.matrix_mul continuous_snd
  exact Complex.continuous_re.comp hMultiply.matrix_trace

/-- Closedness of the actual PSD cone in the finite matrix topology. -/
theorem posSemidef_of_tendsto {n : ℕ} (Kseq : ℕ → Herm n) (K : Herm n)
    (hlim : Tendsto Kseq atTop (𝓝 K)) (hK : ∀ j, (Kseq j).PosSemidef) :
    K.PosSemidef := by
  exact (Matrix.posSemidef_is_closed (𝕜 := ℂ) (n := Fin n)).mem_of_tendsto
    hlim (Eventually.of_forall hK)

theorem posSemidef_sub_of_tendsto {n : ℕ} (Kseq Sseq : ℕ → Herm n) (K S : Herm n)
    (hK : Tendsto Kseq atTop (𝓝 K)) (hS : Tendsto Sseq atTop (𝓝 S))
    (hDom : ∀ j, (Kseq j-Sseq j).PosSemidef) : (K-S).PosSemidef := by
  exact posSemidef_of_tendsto (fun j => Kseq j-Sseq j) (K-S) (hK.sub hS) hDom

theorem trace_pair_le_of_tendsto {n : ℕ}
    (Aseq Kseq : ℕ → Herm n) (A K : Herm n) (rseq : ℕ → ℝ) (r : ℝ)
    (hA : Tendsto Aseq atTop (𝓝 A)) (hK : Tendsto Kseq atTop (𝓝 K))
    (hr : Tendsto rseq atTop (𝓝 r))
    (hTrace : ∀ j, (Matrix.trace ((Aseq j)ᵀ*Kseq j)).re ≤ rseq j) :
    (Matrix.trace (Aᵀ*K)).re ≤ r := by
  have hEntry (i j : Fin n) :
      Tendsto (fun k => ((Aseq k) j i*(Kseq k) j i).re) atTop (𝓝 (A j i*K j i).re) := by
    have ha : Tendsto (fun k => (Aseq k) j i) atTop (𝓝 (A j i)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA j) i
    have hk : Tendsto (fun k => (Kseq k) j i) atTop (𝓝 (K j i)) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hK j) i
    exact (Complex.continuous_re.tendsto (A j i*K j i)).comp (ha.mul hk)
  have hSum : Tendsto (fun k => ∑ i : Fin n, ∑ j : Fin n, ((Aseq k) j i*(Kseq k) j i).re)
      atTop (𝓝 (∑ i : Fin n, ∑ j : Fin n, (A j i*K j i).re)) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hEntry i j))
  have hPairLim : Tendsto (fun j => (Matrix.trace ((Aseq j)ᵀ*Kseq j)).re)
      atTop (𝓝 (Matrix.trace (Aᵀ*K)).re) := by
    simpa only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,
      Complex.re_sum] using hSum
  exact le_of_tendsto_of_tendsto hPairLim hr (Eventually.of_forall hTrace)

/-- Actual matrix convergence preserves the PSD majorant and its
coefficient trace inequality. This is used separately in each ordered limit. -/
theorem psd_majorant_trace_of_tendsto {n : ℕ}
    (Aseq Sseq Kseq : ℕ → Herm n) (A S K : Herm n) (rseq : ℕ → ℝ) (r : ℝ)
    (hA : Tendsto Aseq atTop (𝓝 A)) (hS : Tendsto Sseq atTop (𝓝 S))
    (hKL : Tendsto Kseq atTop (𝓝 K)) (hr : Tendsto rseq atTop (𝓝 r))
    (hK : ∀ j, (Kseq j).PosSemidef) (hDom : ∀ j, (Kseq j-Sseq j).PosSemidef)
    (hTrace : ∀ j, (Matrix.trace ((Aseq j)ᵀ*Kseq j)).re ≤ rseq j) :
    K.PosSemidef ∧ (K-S).PosSemidef ∧ (Matrix.trace (Aᵀ*K)).re ≤ r := by
  exact ⟨posSemidef_of_tendsto Kseq K hKL hK,
    posSemidef_sub_of_tendsto Kseq Sseq K S hKL hS hDom,
    trace_pair_le_of_tendsto Aseq Kseq A K rseq r hA hKL hr hTrace⟩

end Yau.NodeProofs.E02Aux
