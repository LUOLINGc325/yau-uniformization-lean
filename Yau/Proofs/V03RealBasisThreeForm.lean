import Yau.Proofs.V03AreaNormalization
import Yau.Proofs.V03ExteriorCyclic

/-! A genuine native three-form vanishes when its coefficients in the
original real coordinate basis vanish, also in dimension zero. -/

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem threeForm_eq_zero_of_realVec {n : ℕ}
    (Ω : ComplexVector n [⋀^Fin 3]→L[ℝ] ℝ)
    (h : ∀ a b c : RIdx n, Ω ![realVec a, realVec b, realVec c] = 0) : Ω = 0 := by
  classical
  apply ContinuousAlternatingMap.ext
  intro v
  change Ω v = 0
  have hv : v = fun i => ∑ a : RIdx n, realCoord (v i) a • realVec a := by
    funext i
    exact (sum_realCoord_realVec (v i)).symm
  rw [hv]
  change Ω.toMultilinearMap (fun i => ∑ a : RIdx n, realCoord (v i) a • realVec a) = 0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro r _
  rw [MultilinearMap.map_smul_univ]
  have hr : (fun i : Fin 3 => realVec (r i)) = ![realVec (r 0), realVec (r 1), realVec (r 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  change (∏ i : Fin 3, realCoord (v i) (r i)) • Ω ![realVec (r 0), realVec (r 1), realVec (r 2)] = 0
  rw [h]
  simp

end Yau.Blueprint.V03Proof
