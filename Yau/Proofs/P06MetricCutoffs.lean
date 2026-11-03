import Yau.Proofs.P06Geometry
import Yau.LeafProofs.L18

noncomputable section
open scoped Topology

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

/-- The annular construction gives the literal open-ball support and the
real metric gradient normalization of the original cutoff contract. -/
theorem metricCutoffFamily {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (o : M.Carrier) :
    ∃ χ : ℕ → M.Carrier → ℝ, MetricCutoffFamily g.form o χ := by
  classical
  obtain ⟨C, hC, hcut⟩ :=
    Yau.LeafProofs.L18Aux.exists_uniform_annular_scalar_energy_cutoffs n
  have hfamily : ∀ j : ℕ, ∃ η : M.Carrier → ℝ, 1 ≤ j →
      SmoothFn η ∧ HasCompactSupport η ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ distBall g.form o j, η x = 1) ∧
      tsupport η ⊆ distBall g.form o (2 * j) ∧
      ∀ x, realGradientNormSq g.form η x ≤ (C / j) ^ 2 := by
    intro j
    by_cases hj : 1 ≤ j
    · have hjpos : 0 < (j : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
      obtain ⟨η, _, hη, hcη, hηrange, hηone, hηsupport, hηgrad⟩ :=
        hcut M g o j (2 * j) hjpos (by linarith)
      refine ⟨η, fun _ => ⟨hη, hcη, hηrange, ?_, hηsupport, ?_⟩⟩
      · intro x hx
        exact hηone x ((Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hjpos).mp hx).le
      · intro x
        have heq : (2 : ℝ) * j - j = j := by ring
        rw [heq] at hηgrad
        simpa only [Yau.LeafProofs.L18Aux.scalarGradientPair,
          Yau.LeafProofs.L18Aux.chartGradientPair_eq_sum, realGradientNormSq] using hηgrad x
    · exact ⟨0, fun h => (hj h).elim⟩
  choose χ hχ using hfamily
  exact ⟨χ, C, hC, hχ⟩

end Yau.NodeProofs.P06Aux
