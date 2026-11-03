import Yau.Proofs.F03PointwiseDomination
import Yau.Proofs.F03DirichletCompactUniform
import Yau.Proofs.F03L2Parts

/-! Actual compact heat bounds up to the domain boundary, before every L2 source. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletClassicalHeat_compact_boundary_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : Set M.Carrier) (hKc : IsCompact K)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ t : ℝ, τ ≤ t →
      ∀ x ∈ K, x ∈ Ω → |dirichletClassicalHeat g hK μ hμ Ω hΩ f x t| ≤ C*‖f‖ := by
  obtain ⟨C,hC,hWhole⟩ := dirichletClassicalHeat_compact_later_bound g hK μ hμ
    Set.univ isOpen_univ K hKc (subset_univ K) hτ
  have hPositive (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
      (t : ℝ) (ht : τ ≤ t) (x : M.Carrier) (hxK : x ∈ K) (hxΩ : x ∈ Ω) :
      0 ≤ dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ∧
        dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ≤ C*‖f‖ := by
    have ht0 := hτ.trans_le ht
    have hCompare := dirichletClassicalHeat_le_univ g hK μ hμ Ω hΩ f hf ht0 x hxΩ
    have hNorm : ‖l2Restriction μ Set.univ (l2ZeroExtension μ Ω hΩ.measurableSet f)‖ ≤ ‖f‖ :=
      (restrictL2_norm_le μ Set.univ _).trans_eq (l2ZeroExtension_norm μ Ω hΩ.measurableSet f)
    refine ⟨dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ f hf ht0 x hxΩ,?_⟩
    exact hCompare.trans ((le_abs_self _).trans ((hWhole _ t ht x hxK).trans
      (mul_le_mul_of_nonneg_left hNorm hC.le)))
  refine ⟨C,hC,?_⟩
  intro f t ht x hxK hxΩ
  have hp := hPositive (Lp.posPart f) (l2_posPart_nonneg _ f) t ht x hxK hxΩ
  have hn := hPositive (Lp.negPart f) (l2_negPart_nonneg _ f) t ht x hxK hxΩ
  have hpM := hp.2.trans (mul_le_mul_of_nonneg_left (l2_posPart_norm_le _ f) hC.le)
  have hnM := hn.2.trans (mul_le_mul_of_nonneg_left (l2_negPart_norm_le _ f) hC.le)
  have hsplit : dirichletClassicalHeat g hK μ hμ Ω hΩ f x t=
      dirichletClassicalHeat g hK μ hμ Ω hΩ (Lp.posPart f) x t-
        dirichletClassicalHeat g hK μ hμ Ω hΩ (Lp.negPart f) x t := by
    change dirichletHeatEvaluation g hK μ hμ Ω hΩ x hxΩ t (hτ.trans_le ht) f=
      dirichletHeatEvaluation g hK μ hμ Ω hΩ x hxΩ t (hτ.trans_le ht) (Lp.posPart f)-
        dirichletHeatEvaluation g hK μ hμ Ω hΩ x hxΩ t (hτ.trans_le ht) (Lp.negPart f)
    rw [← map_sub,← lp_posPart_sub_negPart f]
  rw [hsplit]
  exact abs_le.mpr ⟨by linarith only [hp.1,hnM],by linarith only [hpM,hn.1]⟩

end Yau.Proofs.F03Aux
