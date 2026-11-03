import Yau.Proofs.V01TraceCompact

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

theorem exists_subseq_psd_trace_eventually (S : ℕ → Herm n) (R : ℝ)
    (hS : ∀ᶠ m in atTop, (S m).PosSemidef ∧ (S m).trace.re ≤ R) :
    ∃ K : Herm n, K.PosSemidef ∧ K.trace.re ≤ R ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (S ∘ σ) atTop (𝓝 K) := by
  obtain ⟨K, hK, σ, hσ, hlim⟩ :=
    (isCompact_psd_trace_sublevel (n := n) R).tendsto_subseq' (x := S)
      (show ∃ᶠ m in atTop, S m ∈ {A : Herm n | A.PosSemidef ∧ A.trace.re ≤ R}
        from hS.frequently)
  exact ⟨K, hK.1, hK.2, σ, hσ, hlim⟩

theorem posSemidef_sub_of_tendsto
    {S B : ℕ → Herm n} {K B₀ : Herm n}
    (hS : Tendsto S atTop (𝓝 K)) (hB : Tendsto B atTop (𝓝 B₀))
    (hSB : ∀ᶠ m in atTop, (S m - B m).PosSemidef) : (K - B₀).PosSemidef :=
  Yau.NodeProofs.E01Aux.isClosed_posSemidef_matrices.mem_of_tendsto (hS.sub hB) hSB

theorem trace_pairing_tendsto
    {C S : ℕ → Herm n} {C₀ K : Herm n}
    (hC : Tendsto C atTop (𝓝 C₀)) (hS : Tendsto S atTop (𝓝 K)) :
    Tendsto (fun m => ((C m)ᵀ * S m).trace.re) atTop (𝓝 ((C₀ᵀ * K).trace.re)) := by
  have hsum : Tendsto (fun m => ∑ i : Fin n, ∑ j : Fin n, C m j i * S m j i)
      atTop (𝓝 (∑ i : Fin n, ∑ j : Fin n, C₀ j i * K j i)) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((hC.apply_nhds j).apply_nhds i).mul ((hS.apply_nhds j).apply_nhds i)
  simpa only [Function.comp_def, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply] using
    (Complex.continuous_re.tendsto _).comp hsum

theorem seqUpperZero_subseq {a : ℕ → ℝ} (ha : SeqUpperZero a)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) : SeqUpperZero (a ∘ σ) := by
  intro r hr
  exact hσ.tendsto_atTop.eventually (ha r hr)

/-- Only the PSD witness is compactified; the matrices that produced it need not be bounded. -/
theorem closed_psd_witness_of_trace_bound
    (S C B : ℕ → Herm n) (C₀ B₀ : Herm n) (τ R : ℝ)
    (hC : Tendsto C atTop (𝓝 C₀)) (hB : Tendsto B atTop (𝓝 B₀))
    (hS : ∀ᶠ m in atTop, (S m).PosSemidef ∧ (S m).trace.re ≤ R)
    (hSB : ∀ᶠ m in atTop, (S m - B m).PosSemidef)
    (hcost : SeqUpperZero (fun m => ((C m)ᵀ * S m).trace.re - τ)) :
    ∃ K : Herm n, K.PosSemidef ∧ (K - B₀).PosSemidef ∧
      (C₀ᵀ * K).trace.re ≤ τ := by
  obtain ⟨K, hK, _hKtrace, σ, hσ, hlim⟩ :=
    exists_subseq_psd_trace_eventually S R hS
  have hσtop : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hBsub : Tendsto (B ∘ σ) atTop (𝓝 B₀) := hB.comp hσtop
  have hSBsub : ∀ᶠ m in atTop, (S (σ m) - B (σ m)).PosSemidef :=
    hσtop.eventually hSB
  have hKB : (K - B₀).PosSemidef :=
    posSemidef_sub_of_tendsto hlim hBsub hSBsub
  have hcostlim : Tendsto (fun m => ((C (σ m))ᵀ * S (σ m)).trace.re)
      atTop (𝓝 ((C₀ᵀ * K).trace.re)) :=
    trace_pairing_tendsto (hC.comp hσtop) hlim
  have hcostsub : SeqUpperZero (fun m => ((C (σ m))ᵀ * S (σ m)).trace.re - τ) :=
    seqUpperZero_subseq hcost hσ
  exact ⟨K, hK, hKB, le_of_tendsto_of_seqUpperZero hcostlim hcostsub⟩


end Yau.Blueprint.V01Proof
