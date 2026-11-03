import Yau.Proofs.C02ODELift

/-! The finite-order tangent-lift induction. It is universal in the Banach
state space, so its induction hypothesis also applies to the lifted equation.
No common infinitely smooth neighborhood is inferred from an infinite germ. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
universe u
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux

theorem exists_localVariationalFlow_order (m : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F : E → E} {z₀ : E} {U : Set E},
      ContDiffAt ℝ ∞ F z₀ → IsOpen U → z₀ ∈ U →
      ∃ d : LocalVariationalFlow F z₀ U,
        ContDiffAt ℝ m (Function.uncurry d.solution) (z₀, 0) := by
  induction m with
  | zero =>
      intro E _ _ _ F z₀ U hF hU hz₀
      obtain ⟨d⟩ := exists_localVariationalFlow (hF.of_le (by simp)) hU hz₀
      exact ⟨d, (d.regularity.contDiffAt d.domain_mem_nhds).of_le (by simp)⟩
  | succ m ih =>
      intro E _ _ _ F z₀ U hF hU hz₀
      obtain ⟨d⟩ := exists_localVariationalFlow (hF.of_le (by simp)) hU hz₀
      obtain ⟨e, he⟩ := ih (odeVariationField_smoothAt hF) isOpen_univ (mem_univ _)
      exact ⟨d, localFlow_contDiffAt_succ_of_pair m hF d
        (localFlow_pair_contDiffAt_of_tangentLift m (hF.of_le (by simp)) d e he)⟩

namespace LocalVariationalFlow

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : E → E} {z₀ : E} {U : Set E}

theorem smoothAt_center (d : LocalVariationalFlow F z₀ U)
    (hF : ContDiffAt ℝ ∞ F z₀) :
    ContDiffAt ℝ ∞ (Function.uncurry d.solution) (z₀, 0) := by
  apply contDiffAt_infty.mpr
  intro m
  obtain ⟨e, he⟩ := exists_localVariationalFlow_order m
    (odeVariationField_smoothAt hF) isOpen_univ (mem_univ _)
  exact (localFlow_contDiffAt_succ_of_pair m hF d
    (localFlow_pair_contDiffAt_of_tangentLift m (hF.of_le (by simp)) d e he)).of_le
      (by exact_mod_cast Nat.le_succ m)

theorem exists_finiteOrder_rectangle (d : LocalVariationalFlow F z₀ U)
    (hF : ContDiffAt ℝ ∞ F z₀) (m : ℕ) :
    ∃ δ > (0 : ℝ),
      (Metric.ball z₀ δ ×ˢ Ioo (-δ) δ ⊆ d.domain) ∧
      ContDiffOn ℝ m (Function.uncurry d.solution)
        (Metric.ball z₀ δ ×ˢ Ioo (-δ) δ) := by
  obtain ⟨N, hN, hreg⟩ := (d.smoothAt_center hF).contDiffOn
    (m := (m : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hN d.domain_mem_nhds)
  have hrect : Metric.ball z₀ δ ×ˢ Ioo (-δ) δ ⊆ N ∩ d.domain := by
    intro p hp
    apply hsub
    simpa only [← ball_prod_same, Real.ball_eq_Ioo, zero_sub, zero_add] using hp
  exact ⟨δ, hδ, fun p hp => (hrect hp).2, hreg.mono (fun p hp => (hrect hp).1)⟩

end LocalVariationalFlow
end Yau.Blueprint.C02Proof
