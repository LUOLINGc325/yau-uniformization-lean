import Yau.Proofs.F04GradientCauchy

/-! Exact scalar Green cross terms are bounded in the project's physical gradient norm. -/
noncomputable section
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem abs_scalarGradientPair_le (g : HermitianField M) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (x : M.Carrier) :
    |scalarGradientPair g u v x| ≤
      2*Real.sqrt (gradNormSq g u x)*Real.sqrt (gradNormSq g v x) := by
  have hu0 : 0 ≤ gradNormSq g u x := by
    have h := scalarGradientPair_self_nonneg g u x
    rw [scalarGradientPair_eq_twice_gradNormSq g hu x] at h
    linarith
  have hv0 : 0 ≤ gradNormSq g v x := by
    have h := scalarGradientPair_self_nonneg g v x
    rw [scalarGradientPair_eq_twice_gradNormSq g hv x] at h
    linarith
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt hu0,Real.sq_sqrt hv0]
  have hc := F04Proof.scalarGradientPair_cauchy g u v x
  rw [scalarGradientPair_eq_twice_gradNormSq g hu x,
    scalarGradientPair_eq_twice_gradNormSq g hv x] at hc
  nlinarith

end Yau.Proofs.F03Aux
