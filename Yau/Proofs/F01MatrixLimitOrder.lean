import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Matrix.Order

/-! Actual entrywise matrix limits preserve native Hermitian order.
A genuine uniform positive lower order constructs positivity of the limit. -/
noncomputable section
open Set Filter
open scoped Topology Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem matrix_posSemidef_of_entry_limits
    (A : ℕ → Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hconv : ∀ i j, Tendsto (fun m => A m i j) atTop (𝓝 (B i j)))
    (hpos : ∀ᶠ m in atTop, (A m).PosSemidef) : B.PosSemidef := by
  have hmatrix : Tendsto A atTop (𝓝 B) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hconv i))
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hmatrix hpos

theorem matrix_upper_order_of_entry_limits
    (Gseq Hseq : ℕ → Matrix (Fin n) (Fin n) ℂ) (cseq : ℕ → ℝ)
    (G H : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hG : ∀ i j, Tendsto (fun m => Gseq m i j) atTop (𝓝 (G i j)))
    (hH : ∀ i j, Tendsto (fun m => Hseq m i j) atTop (𝓝 (H i j)))
    (hc : Tendsto cseq atTop (𝓝 c))
    (horder : ∀ᶠ m in atTop, ((cseq m : ℂ) • Gseq m - Hseq m).PosSemidef) :
    ((c : ℂ) • G - H).PosSemidef := by
  apply matrix_posSemidef_of_entry_limits (fun m => (cseq m : ℂ) • Gseq m - Hseq m)
    ((c : ℂ) • G - H) _ horder
  intro i j
  have hcC : Tendsto (fun m => (cseq m : ℂ)) atTop (𝓝 (c : ℂ)) :=
    (Complex.continuous_ofReal.tendsto c).comp hc
  exact (hcC.mul (hG i j)).sub (hH i j)

theorem matrix_lower_order_of_entry_limits
    (Gseq Hseq : ℕ → Matrix (Fin n) (Fin n) ℂ) (G H : Matrix (Fin n) (Fin n) ℂ)
    (ell : ℝ)
    (hG : ∀ i j, Tendsto (fun m => Gseq m i j) atTop (𝓝 (G i j)))
    (hH : ∀ i j, Tendsto (fun m => Hseq m i j) atTop (𝓝 (H i j)))
    (horder : ∀ᶠ m in atTop, (Hseq m - (ell : ℂ) • Gseq m).PosSemidef) :
    (H - (ell : ℂ) • G).PosSemidef := by
  apply matrix_posSemidef_of_entry_limits (fun m => Hseq m - (ell : ℂ) • Gseq m)
    (H - (ell : ℂ) • G) _ horder
  intro i j
  exact (hH i j).sub (tendsto_const_nhds.mul (hG i j))

theorem matrix_posDef_of_positive_lower_order
    {G H : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {ell : ℝ} (hell : 0 < ell)
    (horder : (H - (ell : ℂ) • G).PosSemidef) : H.PosDef := by
  have hp := hG.smul (Complex.zero_lt_real.mpr hell)
  simpa only [add_sub_cancel] using hp.add_posSemidef horder

end Yau.NodeProofs.F01Aux
