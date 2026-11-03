import Yau.Proofs.E01FeasibleCompact
import Mathlib.Topology.Sequences

/-! V01 scratch source. Uncompiled until the dedicated receiver is READY. -/

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

/-- A PSD matrix lies below its trace times the identity. This includes `n = 0`. -/
theorem psd_le_trace_one {A : Herm n} (hA : A.PosSemidef) :
    (((A.trace.re : ℂ) • (1 : Herm n)) - A).PosSemidef := by
  classical
  let U := hA.isHermitian.eigenvectorUnitary
  let d : Fin n → ℝ := hA.isHermitian.eigenvalues
  have ht : A.trace.re = ∑ i, d i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp [d]
  have hd (i : Fin n) : d i ≤ A.trace.re := by
    rw [ht]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hdiag : (Matrix.diagonal (fun i => ((A.trace.re - d i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast sub_nonneg.mpr (hd i)
  have heq : Matrix.diagonal (fun i => ((A.trace.re - d i : ℝ) : ℂ)) =
      (A.trace.re : ℂ) • (1 : Herm n) - Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hconj := hdiag.mul_mul_conjTranspose_same (U : Herm n)
  have hmap :
      (Unitary.conjStarAlgAut ℂ (Herm n) U
        (Matrix.diagonal (fun i => ((A.trace.re - d i : ℝ) : ℂ)))).PosSemidef := by
    simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hconj
  rw [heq, map_sub, map_smul, map_one] at hmap
  have hs : Unitary.conjStarAlgAut ℂ (Herm n) U
      (Matrix.diagonal (fun i => (d i : ℂ))) = A := by
    exact hA.isHermitian.spectral_theorem.symm
  rwa [hs] at hmap

theorem psd_le_real_bound_one {A : Herm n} (hA : A.PosSemidef)
    {R : ℝ} (hR : A.trace.re ≤ R) :
    (((R : ℂ) • (1 : Herm n)) - A).PosSemidef := by
  have hb : (((R - A.trace.re : ℝ) : ℂ) • (1 : Herm n)).PosSemidef :=
    Matrix.PosSemidef.smul (Matrix.PosSemidef.one) (by exact_mod_cast sub_nonneg.mpr hR)
  convert hb.add (psd_le_trace_one hA) using 1
  simp only [Complex.ofReal_sub, sub_smul]
  abel

theorem isCompact_psd_trace_sublevel (R : ℝ) :
    IsCompact {A : Herm n | A.PosSemidef ∧ A.trace.re ≤ R} := by
  have htrace : Continuous (fun A : Herm n => A.trace.re) := by fun_prop
  have hc : IsClosed {A : Herm n | A.PosSemidef ∧ A.trace.re ≤ R} :=
    Yau.NodeProofs.E01Aux.isClosed_posSemidef_matrices.inter
      (isClosed_le htrace continuous_const)
  apply (Yau.NodeProofs.E01Aux.isCompact_psd_order_interval ((R : ℂ) • (1 : Herm n))).of_isClosed_subset hc
  intro A hA
  exact ⟨hA.1, psd_le_real_bound_one hA.1 hA.2⟩

theorem exists_subseq_psd_trace_bounded
    (S : ℕ → Herm n) (R : ℝ)
    (hS : ∀ m, (S m).PosSemidef) (hR : ∀ m, (S m).trace.re ≤ R) :
    ∃ K : Herm n, K.PosSemidef ∧ K.trace.re ≤ R ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (S ∘ σ) atTop (𝓝 K) := by
  obtain ⟨K, hK, σ, hσ, hlim⟩ :=
    (isCompact_psd_trace_sublevel (n := n) R).tendsto_subseq (fun m => ⟨hS m, hR m⟩)
  exact ⟨K, hK.1, hK.2, σ, hσ, hlim⟩

/-- Quantified upper limits pass to a convergent real sequence. -/
theorem le_of_tendsto_of_seqUpperZero {a : ℕ → ℝ} {b τ : ℝ}
    (ha : Tendsto a atTop (𝓝 b)) (hupper : SeqUpperZero (fun m => a m - τ)) :
    b ≤ τ := by
  by_contra hn
  have he : 0 < (b - τ) / 2 := by linarith
  have hbound : ∀ᶠ m in atTop, a m ≤ τ + (b - τ) / 2 := by
    filter_upwards [hupper _ he] with m hm
    linarith
  have := le_of_tendsto ha hbound
  linarith

end Yau.Blueprint.V01Proof
