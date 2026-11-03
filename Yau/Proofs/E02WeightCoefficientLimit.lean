import Yau.Proofs.E02PSDTraceLimit
import Yau.Proofs.E02PosDefLower

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The final weight limit acts on the fixed original horizontal space.
The numbers of individual contacts may vary without entering this bound. -/
theorem exists_psd_majorant_limit_coefficients {n : ℕ}
    (B S : Herm n) (hB : B.PosDef) (r cmin : ℝ) (hcmin : 0 < cmin)
    (cseq : ℕ → ℝ) (hcseq : ∀ j, cmin ≤ cseq j)
    (hclim : Tendsto cseq atTop (𝓝 1))
    (hMajorants : ∀ j, ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧
      cseq j*(Matrix.trace (Bᵀ*K)).re ≤ r) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧
      (Matrix.trace (Bᵀ*K)).re ≤ r := by
  obtain ⟨β,hβ,hLower⟩ := posDef_exists_scalar_lower B hB
  choose K hK hDom hTrace using hMajorants
  have hCoercive : ∀ j, ((cseq j : ℂ) • B-((cmin*β : ℝ) : ℂ) • (1 : Herm n)).PosSemidef := by
    intro j
    have hExtra : (((cseq j-cmin : ℝ) : ℂ) • B).PosSemidef :=
      hB.posSemidef.smul (RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hcseq j)))
    have hBase : ((cmin : ℂ) • (B-(β : ℂ) • (1 : Herm n))).PosSemidef :=
      hLower.smul (RCLike.ofReal_nonneg.mpr hcmin.le)
    convert hExtra.add hBase using 1 <;> push_cast <;> module
  have hComplex : Tendsto (fun j => (cseq j : ℂ)) atTop (𝓝 (1:ℂ)) := by
    simpa only [Complex.ofReal_one] using hclim.ofReal
  have hALim : Tendsto (fun j => (cseq j : ℂ) • B) atTop (𝓝 B) := by
    simpa only [one_smul] using hComplex.smul (tendsto_const_nhds (x := B))
  have hTrace' : ∀ j, (Matrix.trace (((cseq j : ℂ) • B)ᵀ*K j)).re ≤ r := by
    intro j
    simpa only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hTrace j
  exact exists_psd_limit_of_coercive_trace_bound (fun j => (cseq j : ℂ) • B)
    (fun _ => S) K B S (fun _ => r) r (cmin*β) r (mul_pos hcmin hβ)
    hALim tendsto_const_nhds tendsto_const_nhds hCoercive hK hDom hTrace' (fun _ => le_rfl)

end Yau.NodeProofs.E02Aux
