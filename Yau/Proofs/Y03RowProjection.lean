import Yau.Proofs.Y03RowRayleigh
import Yau.Proofs.Y03ProjectionMass
import Yau.Proofs.Y03CoordinateProjection

/-! The actual perturbed row image projects injectively across a strict rate gap. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem perturbed_row_projection_mass (μ ν : Fin n → ℝ) (U E : Herm n)
    (hU : Unitary U) {δ B r g : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) (hg : 0 < g) (hE : matOpNorm E ≤ δ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B)
    (horder : ∀ v : Fin n → ℂ, (∑ i, μ i * ‖(v ᵥ* U) i‖ ^ 2) ≤ ∑ i, ν i * ‖v i‖ ^ 2)
    (s : Finset (Fin n)) (hout : ∀ i, i ∉ s → r + g ≤ μ i)
    (hsmall : 32 * δ * B ≤ g / 2) (c : ComplexVector n) (hc : ∀ i, c i ≠ 0 → ν i ≤ r) :
    g / (2 * (B + g)) * ‖rowApply ((1 + E) * U) c‖ ^ 2 ≤
      ‖coordinateProjection s (rowApply ((1 + E) * U) c)‖ ^ 2 := by
  let a := rowApply ((1 + E) * U) c
  have hq := perturbed_row_rayleigh_bound μ ν U E hU hδ hδ' hB hr hrB hE hμ horder c hc
  have hquad : (∑ i, μ i * ‖a i‖ ^ 2) ≤ (r + g / 2) * (∑ i, ‖a i‖ ^ 2) := by
    rw [← EuclideanSpace.norm_sq_eq]
    exact hq.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hsmall) (sq_nonneg _))
  have hp := projection_mass_lower s μ (fun i => ‖a i‖ ^ 2)
    (fun i => (hμ i).1) (fun _ => sq_nonneg _) hr hg hrB hout hquad
  simpa only [← EuclideanSpace.norm_sq_eq, ← coordinateProjection_norm_sq] using hp

theorem norm_le_of_projection_mass {H E : Type*} [NormedAddCommGroup H] [NormedAddCommGroup E]
    (a : H) (p : E) {g B : ℝ} (hg : 0 < g) (hB : 0 ≤ B)
    (hp : g / (2 * (B + g)) * ‖a‖ ^ 2 ≤ ‖p‖ ^ 2) :
    ‖a‖ ≤ Real.sqrt (2 * (B + g) / g) * ‖p‖ := by
  have hden : 0 < B + g := by linarith
  have hratio : 0 ≤ 2 * (B + g) / g := by positivity
  have hcancel : (2 * (B + g) / g) * (g / (2 * (B + g))) = 1 := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hp hratio
  rw [← mul_assoc, hcancel, one_mul] at hmul
  apply (sq_le_sq₀ (norm_nonneg a) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg p))).1
  rw [mul_pow, Real.sq_sqrt hratio]
  exact hmul

end Yau.Blueprint.Alignment.Y03Proof
