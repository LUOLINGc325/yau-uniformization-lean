import Yau.Proofs.P06MetricCutoffs
import Yau.Proofs.P06FormDomain

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- Every cutoff allowed by the original contract produces actual L² data
from a smooth form, with no integrability premise on the original form. -/
theorem metricCutoff_smooth_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) (A : RealForm M k) (hA : SmoothRealForm A) :
    ∀ j, 1 ≤ j → L2RealForm g.form μ (fun x => χ j x • A x) := by
  obtain ⟨C, hC, hc⟩ := hχ
  intro j hj
  exact smooth_compactlySupported_l2RealForm g μ hμ _
    (smoothRealForm_multiply (χ j) A (hc j hj).1 hA)
    (compactlySupportedRealForm_multiply_scalar (χ j) (hc j hj).2.1 A)

theorem metricCutoff_eventually_one (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ) (x : M.Carrier) :
    ∀ᶠ j : ℕ in atTop, χ j x = 1 := by
  obtain ⟨C, hC, hc⟩ := hχ
  obtain ⟨N, hN⟩ := exists_nat_gt (inducedDistance g.form o x)
  filter_upwards [eventually_ge_atTop (max N 1)] with j hj
  have hj1 : 1 ≤ j := (le_max_right N 1).trans hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj1)
  apply (hc j hj1).2.2.2.1 x
  apply (Yau.LeafProofs.L12Aux.mem_distBall_iff g o x hjpos).mpr
  exact hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hj)

/-- Cutoff exhaustion for every admissible basepoint/family converges in
the original raw extended-real L² distance. The unused zeroth cutoff is
removed only inside the dominated-convergence proof. -/
theorem metricCutoff_l2_distance_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    Tendsto (fun j => formL2DistanceSq g.form μ (fun x => χ j x • A x) A) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC, hc⟩ := hχ
  let η : ℕ → M.Carrier → ℝ := fun j => if 1 ≤ j then χ j else 0
  have hη (j : ℕ) : SmoothFn (η j) := by
    by_cases hj : 1 ≤ j
    · simpa only [η, ite_eq_left hj] using (hc j hj).1
    · simp only [η, ite_eq_right hj]
      intro x
      exact contDiffOn_const
  have hηrange (j : ℕ) (x : M.Carrier) : η j x ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hj : 1 ≤ j
    · simpa only [η, ite_eq_left hj, Set.mem_Icc] using (hc j hj).2.2.1 x
    · simp [η, hj]
  have hηinit (x : M.Carrier) : Tendsto (fun j => η j x) atTop (𝓝 1) := by
    apply tendsto_congr' ?_ |>.mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1, metricCutoff_eventually_one g o χ ⟨C, hC, hc⟩ x]
      with j hj hx
    simp only [η, ite_eq_left hj, hx]
  have hlim := multiplyRealForm_l2_distance_tendsto g μ A hA η hη hηrange hηinit
  apply tendsto_congr' ?_ |>.mp hlim
  filter_upwards [eventually_ge_atTop 1] with j hj
  simp only [η, ite_eq_left hj]
  rfl

end Yau.NodeProofs.P06Aux
