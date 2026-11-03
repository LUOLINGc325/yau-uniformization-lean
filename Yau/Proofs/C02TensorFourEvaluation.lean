import Yau.LeafProofs.L23TensorMultilinear

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ}

theorem tensorFour_eval_sum (T : RealTensorForm n 4) (u v w z : ComplexVector n) :
    T ![u, v, w, z] = ∑ a, ∑ b, ∑ c, ∑ d,
      realCoord u a * realCoord v b * realCoord w c * realCoord z d *
        T ![realVec a, realVec b, realVec c, realVec d] := by
  have h1 : T ![u, v, w, z] = ∑ a, realCoord u a * T ![realVec a, v, w, z] := by
    change T.curryLeft u ![v, w, z] = _
    conv_lhs => rw [← sum_realCoord_realVec u]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, ContinuousMultilinearMap.curryLeft_apply, Matrix.Fin.cons_vecCons]
  have h2 (a : RIdx n) : T ![realVec a, v, w, z] =
      ∑ b, realCoord v b * T ![realVec a, realVec b, w, z] := by
    change (T.curryLeft (realVec a)).curryLeft v ![w, z] = _
    conv_lhs => rw [← sum_realCoord_realVec v]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, ContinuousMultilinearMap.curryLeft_apply, Matrix.Fin.cons_vecCons]
  have h3 (a b : RIdx n) : T ![realVec a, realVec b, w, z] =
      ∑ c, realCoord w c * T ![realVec a, realVec b, realVec c, z] := by
    change ((T.curryLeft (realVec a)).curryLeft (realVec b)).curryLeft w ![z] = _
    conv_lhs => rw [← sum_realCoord_realVec w]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, ContinuousMultilinearMap.curryLeft_apply, Matrix.Fin.cons_vecCons]
  have h4 (a b c : RIdx n) : T ![realVec a, realVec b, realVec c, z] =
      ∑ d, realCoord z d * T ![realVec a, realVec b, realVec c, realVec d] := by
    let S := (((T.curryLeft (realVec a)).curryLeft (realVec b)).curryLeft (realVec c)).curryLeft
    change (S z) ![] = _
    conv_lhs => rw [← sum_realCoord_realVec z]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul]
    rfl
  rw [h1]
  simp_rw [h2, h3, h4, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring

end Yau.Blueprint.C02Proof
