import Yau.Proofs.C01IndexCutoffIntegral
import Yau.Proofs.C01SecondDensityContinuity

/-! Integrating the true finite second-variation trace yields the
weighted Ricci integral inequality, with the precise cutoff cost. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace Yau.NodeProofs.C01Aux

theorem weighted_integral_le_of_secondVariation_trace
    {ι : Type*} [Fintype ι] (D : ι → ℝ → ℝ) (φ R : ℝ → ℝ)
    (hD : ∀ i, IntegrableOn (D i) (Set.Icc (0 : ℝ) 1) volume)
    (hφ : IntegrableOn (fun u => deriv φ u ^ 2) (Set.Icc (0 : ℝ) 1) volume)
    (hR : IntegrableOn (fun u => φ u ^ 2 * R u) (Set.Icc (0 : ℝ) 1) volume)
    (hpositive : ∀ i, 0 ≤ ∫ u in Set.Icc (0 : ℝ) 1, D i u)
    (htrace : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (∑ i, D i u) = 2 * (Fintype.card ι : ℝ) * deriv φ u ^ 2 - 2 * (φ u ^ 2 * R u)) :
    (∫ u in Set.Icc (0 : ℝ) 1, φ u ^ 2 * R u) ≤
      (Fintype.card ι : ℝ) * ∫ u in Set.Icc (0 : ℝ) 1, deriv φ u ^ 2 := by
  have hsum : 0 ≤ ∫ u in Set.Icc (0 : ℝ) 1, ∑ i, D i u := by
    rw [integral_finset_sum Finset.univ (fun i _ => hD i)]
    exact Finset.sum_nonneg (fun i _ => hpositive i)
  have heq : (∫ u in Set.Icc (0 : ℝ) 1, ∑ i, D i u) =
      (∫ u in Set.Icc (0 : ℝ) 1,
        2 * (Fintype.card ι : ℝ) * deriv φ u ^ 2 - 2 * (φ u ^ 2 * R u)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact htrace u hu
  rw [heq, integral_sub (hφ.const_mul _) (hR.const_mul _), integral_const_mul,
    integral_const_mul] at hsum
  linarith

theorem indexCutoff_weighted_integral_bound
    {ι : Type*} [Fintype ι] (D : ι → ℝ → ℝ) (R : ℝ → ℝ)
    (κ B : ℝ) (hκ : 0 < κ)
    (hD : ∀ i, IntegrableOn (D i) (Set.Icc (0 : ℝ) 1) volume)
    (hR : IntegrableOn (fun u => indexCutoff κ u ^ 2 * R u) (Set.Icc (0 : ℝ) 1) volume)
    (hpositive : ∀ i, 0 ≤ ∫ u in Set.Icc (0 : ℝ) 1, D i u)
    (htrace : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (∑ i, D i u) = 2 * (Fintype.card ι : ℝ) * deriv (indexCutoff κ) u ^ 2 -
        2 * (indexCutoff κ u ^ 2 * R u))
    (hcost : (∫ u in Set.Icc (0 : ℝ) 1, deriv (indexCutoff κ) u ^ 2) ≤ B / κ) :
    (∫ u in Set.Icc (0 : ℝ) 1, indexCutoff κ u ^ 2 * R u) ≤
      (Fintype.card ι : ℝ) * B / κ := by
  have hφ : IntegrableOn (fun u => deriv (indexCutoff κ) u ^ 2) (Set.Icc (0 : ℝ) 1) volume :=
    (((indexCutoff_contDiff κ).continuous_deriv (by simp)).pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have H := weighted_integral_le_of_secondVariation_trace D (indexCutoff κ) R hD hφ hR hpositive htrace
  exact H.trans ((mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg (Fintype.card ι))).trans_eq
    (by ring))

end Yau.NodeProofs.C01Aux
