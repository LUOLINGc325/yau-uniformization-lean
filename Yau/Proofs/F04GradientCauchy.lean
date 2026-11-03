import Yau.Proofs.F04GradientOrder

open scoped Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarGradientPair_cauchy (h : HermitianField M) (u v : M.Carrier → ℝ)
    (x : M.Carrier) :
    (scalarGradientPair h u v x) ^ 2 ≤
      scalarGradientPair h u u x * scalarGradientPair h v v x := by
  unfold scalarGradientPair
  rw [chartGradientPair_dotProduct, chartGradientPair_dotProduct, chartGradientPair_dotProduct]
  have hc := (Yau.LeafProofs.L12Aux.realMetricFn_posDef h x (chartPt x x)
    (mem_extChartAt_target x)).inv.star_dotProduct_mulVec_mul_le
      (fun i => rDeriv (inChart x u) (chartPt x x) i)
      (fun i => rDeriv (inChart x v) (chartPt x x) i)
  simpa only [star_trivial, pow_two] using hc

/-- The actual drift admits the absorption estimate used by the fixed-volume
 form. Only the rho-gradient bound enters its coefficient. -/
theorem scalarGradientPair_drift_absorption (h : HermitianField M)
    (ρ u : M.Carrier → ℝ) (x : M.Carrier) (v D : ℝ)
    (hD : scalarGradientPair h ρ ρ x ≤ D) :
    2 * |v * scalarGradientPair h ρ u x| ≤ scalarGradientPair h u u x + D * v ^ 2 := by
  let a := scalarGradientPair h ρ ρ x
  let b := scalarGradientPair h u u x
  let c := scalarGradientPair h ρ u x
  have ha : 0 ≤ a := scalarGradientPair_self_nonneg h ρ x
  have hb : 0 ≤ b := scalarGradientPair_self_nonneg h u x
  have hD0 : 0 ≤ D := ha.trans hD
  have hc : c ^ 2 ≤ D * b :=
    (scalarGradientPair_cauchy h ρ u x).trans (mul_le_mul_of_nonneg_right hD hb)
  have hvc : (v * c) ^ 2 ≤ (D * v ^ 2) * b := by
    calc
      _ = v ^ 2 * c ^ 2 := by ring
      _ ≤ v ^ 2 * (D * b) := mul_le_mul_of_nonneg_left hc (sq_nonneg v)
      _ = _ := by ring
  have hE : 0 ≤ D * v ^ 2 := mul_nonneg hD0 (sq_nonneg v)
  have habs : |v * c| ^ 2 ≤ (D * v ^ 2) * b := by simpa only [sq_abs] using hvc
  change 2 * |v * c| ≤ b + D * v ^ 2
  nlinarith [sq_nonneg (b - D * v ^ 2), abs_nonneg (v * c)]

end Yau.F04Proof
