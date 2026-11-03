import Yau.LeafProofs.L22Uniform
import Yau.LeafProofs.L22LeviCalculus

open scoped Topology ContDiff Matrix ComplexOrder
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

/-- Strict positivity of the actual Levi matrix has one positive quadratic
lower bound on a fixed compact subset of a chart, in every dimension. -/
theorem exists_uniform_levi_lower_bound_on_compact {n : ℕ}
    {O K : Set (ComplexVector n)} {f : ComplexVector n → ℝ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hpos : ∀ z ∈ K, (leviC f z).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ v,
      δ * ‖v‖ ^ 2 ≤ complexLeviQuadratic f z v := by
  have hq : ContinuousOn (fun p : ComplexVector n × ComplexVector n =>
      complexLeviQuadratic f p.1 p.2) (K ×ˢ Metric.sphere 0 1) := by
    intro p hp
    exact (complexLeviQuadratic_continuousAt
      (hf.contDiffAt (hO.mem_nhds (hKO hp.1))) p.2).continuousWithinAt
  have hp : ∀ p ∈ K ×ˢ Metric.sphere 0 1,
      0 < complexLeviQuadratic f p.1 p.2 := by
    rintro ⟨z, v⟩ ⟨hz, hv⟩
    apply (leviC_posDef_iff
      ((hf.contDiffAt (hO.mem_nhds (hKO hz))).of_le (by simp))).mp (hpos z hz) v
    intro hzero
    simpa [Metric.mem_sphere, hzero] using hv
  obtain ⟨δ, hδ, hbound⟩ := (hK.prod (isCompact_sphere (0 : ComplexVector n) 1)).exists_forall_le'
    hq hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · simp only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, complexLeviQuadratic, smul_zero, map_zero, zero_add, zero_div, le_refl]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : ComplexVector n := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : ComplexVector n) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      dsimp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hqw := hbound (z, w) ⟨hz, hw⟩
    have hvw : ‖v‖ • w = v := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have he := complexLeviQuadratic_smul f z w ‖v‖
    rw [hvw] at he
    rw [he]
    nlinarith [sq_nonneg ‖v‖]

end Yau.NodeProofs.P03Aux
