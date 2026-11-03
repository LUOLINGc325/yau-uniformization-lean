import Yau.Proofs.P03UniformSpatialLevi
import Yau.Proofs.P03PoleRegularizationJoint

open scoped Topology ContDiff
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

/-- A compact set away from the pole gives one cutoff-Levi bound before all
parameters in a closed interval, including the singular endpoint zero. -/
theorem exists_uniform_cutoffPole_levi_bound_away {n : ℕ}
    (c : ℝ) (θ : ComplexVector n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (a : ComplexVector n) {K : Set (ComplexVector n)} (hK : IsCompact K)
    (hKa : a ∉ K) (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) b, ∀ z ∈ K, ∀ v,
      |complexLeviQuadratic (cutoffPoleRegularization c θ a ε) z v| ≤ C * ‖v‖ ^ 2 := by
  let O : Set (ComplexVector n × ℝ) := {p | 0 < ‖p.1 - a‖ ^ 2 + p.2}
  have hO : IsOpen O := by
    exact isOpen_lt continuous_const
      (((continuous_fst.sub continuous_const).norm.pow 2).add continuous_snd)
  have hsub : K ×ˢ Icc (0 : ℝ) b ⊆ O := by
    rintro ⟨z, ε⟩ ⟨hz, hε⟩
    have hza : z ≠ a := by intro he; exact hKa (he ▸ hz)
    exact add_pos_of_pos_of_nonneg
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza))) hε.1
  obtain ⟨C, hC, hbound⟩ := exists_uniform_spatial_levi_bound_on_compact
    (fun p => cutoffPoleRegularization c θ a p.2 p.1) hO
    (cutoffPoleRegularization_joint_contDiffOn c θ hθ a)
    (hK.prod isCompact_Icc) hsub
  refine ⟨C, hC, ?_⟩
  intro ε hε z hz v
  exact hbound (z, ε) ⟨hz, hε⟩ v

end Yau.NodeProofs.P03Aux
