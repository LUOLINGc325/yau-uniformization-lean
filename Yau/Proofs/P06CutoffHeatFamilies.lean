import Yau.Proofs.P06L2HeatExistence
import Yau.Proofs.P06CutoffData

noncomputable section
open MeasureTheory

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem boundedOneOneData_global_norm (g : HermitianField M) (A : RealForm M 2)
    (hA : BoundedOneOneData g A) : ∃ B : ℝ, 0 < B ∧ ∀ x, formNormSq g A x ≤ B ^ 2 := by
  obtain ⟨_, h11, C, hC, hb⟩ := hA
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨((n : ℝ) + 1) * (C + 1), mul_pos (by linarith) (by linarith), ?_⟩
  intro x
  calc
    _ ≤ (n : ℝ) * C ^ 2 := G04Aux.norm_of_order g A h11 hC hb x
    _ ≤ ((n : ℝ) + 1) ^ 2 * C ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (n : ℝ)]) (sq_nonneg C)
    _ ≤ ((n : ℝ) + 1) ^ 2 * (C + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg ((n : ℝ) + 1))
    _ = _ := by ring

/-- The original L² theorem supplies an entire cutoff family; the unused
zeroth index imposes no condition on its chosen evolution. -/
theorem metricCutoff_exists_l2Heat_family (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2) (hA : SmoothRealForm A)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ) :
    ∃ Us : ℕ → ℝ → RealForm M 2,
      ∀ j, 1 ≤ j → IsL2FormHeat g.form μ (fun x => χ j x • A x) (Us j) := by
  classical
  have hchoice : ∀ j : ℕ, ∃ V : ℝ → RealForm M 2,
      1 ≤ j → IsL2FormHeat g.form μ (fun x => χ j x • A x) V := by
    intro j
    by_cases hj : 1 ≤ j
    · obtain ⟨V, hV, _⟩ := L2HeatExistence.exists_isL2FormHeat g μ hμ
        (fun x => χ j x • A x) (metricCutoff_smooth_l2 g μ hμ o χ hχ A hA j hj)
      exact ⟨V, fun _ => hV⟩
    · exact ⟨0, fun h => False.elim (hj h)⟩
  choose Us hUs using hchoice
  exact ⟨Us, hUs⟩

end Yau.NodeProofs.P06Aux
