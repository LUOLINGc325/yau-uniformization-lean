import Yau.Proofs.G01ConnectionJ

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realCoord_I_smul (v : ComplexVector n) (a : RIdx n) :
    realCoord (Complex.I • v) a =
      jSign (jIndex n a) * realCoord v (jIndex n a) := by
  rcases a with ⟨i, k⟩
  fin_cases k <;>
    simp [realCoord, jSign, jIndex, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

theorem realCoord_chartChristoffelBilin (h : HermitianField M) (p : M.Carrier)
    (z u v : ComplexVector n) (c : RIdx n) :
    realCoord (chartChristoffelBilin h p z u v) c =
      ∑ a, ∑ b, christoffel h p z c a b * realCoord u a * realCoord v b := by
  rw [chartChristoffelBilin_apply, realCoord_sum_realVec]

theorem chartChristoffelBilin_I_right (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget p)
    (u v : ComplexVector n) :
    chartChristoffelBilin h p z u (Complex.I • v) =
      Complex.I • chartChristoffelBilin h p z u v := by
  apply realCoord_injective n
  funext c
  rw [realCoord_chartChristoffelBilin, realCoord_I_smul,
    realCoord_chartChristoffelBilin]
  calc
    _ = ∑ a, ∑ b, christoffel h p z c a (jIndex n b) * realCoord u a *
        realCoord (Complex.I • v) (jIndex n b) := by
      apply Finset.sum_congr rfl
      intro a _
      exact ((jIndex n).sum_comp (fun b =>
        christoffel h p z c a b * realCoord u a * realCoord (Complex.I • v) b)).symm
    _ = ∑ a, ∑ b, (jSign b * christoffel h p z c a (jIndex n b)) *
        realCoord u a * realCoord v b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [realCoord_I_smul]
      simp only [jIndex_involutive]
      ring
    _ = jSign (jIndex n c) *
        (∑ a, ∑ b, christoffel h p z (jIndex n c) a b * realCoord u a * realCoord v b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [G01Aux.christoffel_jIndex h hs hk p z hz a b c]
      ring

theorem chartChristoffelBilin_I_I (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget p)
    (v : ComplexVector n) :
    chartChristoffelBilin h p z (Complex.I • v) (Complex.I • v) =
      -chartChristoffelBilin h p z v v := by
  calc
    _ = Complex.I • chartChristoffelBilin h p z (Complex.I • v) v :=
      chartChristoffelBilin_I_right h hs hk p hz (Complex.I • v) v
    _ = Complex.I • chartChristoffelBilin h p z v (Complex.I • v) :=
      congrArg (fun w : ComplexVector n => Complex.I • w)
        (chartChristoffelBilin_symm h p z (Complex.I • v) v)
    _ = Complex.I • (Complex.I • chartChristoffelBilin h p z v v) :=
      congrArg (fun w : ComplexVector n => Complex.I • w)
        (chartChristoffelBilin_I_right h hs hk p hz v v)
    _ = _ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]

end Yau.NodeProofs.P02Aux
