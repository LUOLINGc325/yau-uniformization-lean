import Yau.Proofs.C02ComplexCoordinates

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartChristoffel_realCoord (h : HermitianField M) (c : M.Carrier)
    (y u v : ComplexVector n) (d : RIdx n) :
    realCoord (chartChristoffelBilin h c y u v) d =
      ∑ a, ∑ b, christoffel h c y d a b * realCoord u a * realCoord v b := by
  rw [chartChristoffelBilin_apply, realCoord_sum_realVec]

theorem chartChristoffelBilin_I (g : SmoothMetric M) (c : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget c) (u v : ComplexVector n) :
    chartChristoffelBilin g.form c y u (Complex.I • v) =
      Complex.I • chartChristoffelBilin g.form c y u v := by
  apply realCoord_injective n
  funext d
  rw [chartChristoffel_realCoord, realCoord_I_smul, chartChristoffel_realCoord]
  simp_rw [realCoord_I_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  calc
    _ = ∑ b, christoffel g.form c y d a (jIndex n b) * realCoord u a *
        (jSign b * realCoord v b) := by
      simpa only [jIndex_involutive] using ((jIndex n).sum_comp
        (fun b => christoffel g.form c y d a b * realCoord u a *
          (jSign (jIndex n b) * realCoord v (jIndex n b)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have h := christoffel_jIndex g g.kahler_equations c y hy a b d
      calc
        _ = (jSign b * christoffel g.form c y d a (jIndex n b)) * realCoord u a * realCoord v b := by ring
        _ = (jSign (jIndex n d) * christoffel g.form c y (jIndex n d) a b) * realCoord u a * realCoord v b := by rw [h]
        _ = _ := by ring

end Yau.Blueprint.C02Proof
