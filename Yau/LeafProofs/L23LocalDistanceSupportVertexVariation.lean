import Yau.LeafProofs.L23LocalDistanceSupportShortEdges
import Yau.LeafProofs.L23FieldMetricNormalDistanceVariation
import Yau.LeafProofs.L23FieldMetricCoordinatePairing

/-! Moving one genuine polygon vertex differentiates exactly its two adjacent distances. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldPolygonPoint_update (q y : M.Carrier) (v : Fin N → M.Carrier)
    (j : Fin N) (z : M.Carrier) (i : Fin (N+2)) :
    fieldPolygonPoint q y (Function.update v j z) i =
      if i = j.castSucc.succ then z else fieldPolygonPoint q y v i := by
  classical
  refine Fin.cases ?_ (fun k => ?_) i
  · have hne : (0 : Fin (N+2)) ≠ j.castSucc.succ := by
      intro H
      have Hv := congrArg Fin.val H
      simp only [Fin.val_zero,Fin.val_succ,Fin.val_castSucc] at Hv
      omega
    simp only [fieldPolygonPoint,Fin.cases_zero,if_neg hne]
  · refine Fin.lastCases ?_ (fun k' => ?_) k
    · have hne : (Fin.last N).succ ≠ j.castSucc.succ := by
        intro H
        have Hv := congrArg Fin.val H
        simp only [Fin.val_succ,Fin.val_last,Fin.val_castSucc] at Hv
        omega
      simp only [fieldPolygonPoint,Fin.cases_succ,Fin.lastCases_last,if_neg hne]
    · simp only [fieldPolygonPoint,Fin.cases_succ,Fin.lastCases_castSucc,Fin.succ_inj,
        Fin.castSucc_inj,Function.update_apply]

theorem fieldPolygonEnergy_update_hasDerivAt
    (h : HermitianField M) (q y : M.Carrier) (v : Fin N → M.Carrier)
    (j : Fin N) (β : ℝ → M.Carrier) {L R : ℝ}
    (hleft : HasDerivAt (fun r => inducedDistance h
      (fieldPolygonPoint q y v j.castSucc.castSucc) (β r)^2) L 0)
    (hright : HasDerivAt (fun r => inducedDistance h
      (β r) (fieldPolygonPoint q y v j.succ.succ)^2) R 0) :
    HasDerivAt (fun r => fieldPolygonEnergy h q y (Function.update v j (β r)))
      ((N+1 : ℕ)*(L+R)) 0 := by
  classical
  let d : Fin (N+1) → ℝ := fun i =>
    (if i = j.castSucc then L else 0)+(if i = j.succ then R else 0)
  have hneLR : j.castSucc ≠ j.succ := Fin.ne_of_val_ne (by
    simp only [Fin.val_castSucc,Fin.val_succ]
    omega)
  have hneLeft : j.castSucc.castSucc ≠ j.castSucc.succ := Fin.ne_of_val_ne (by
    simp only [Fin.val_castSucc,Fin.val_succ]
    omega)
  have hneRight : j.succ.succ ≠ j.castSucc.succ := Fin.ne_of_val_ne (by
    simp only [Fin.val_castSucc,Fin.val_succ]
    omega)
  have hmiddle : j.succ.castSucc = j.castSucc.succ := rfl
  have hedge (i : Fin (N+1)) : HasDerivAt (fun r => inducedDistance h
      (fieldPolygonPoint q y (Function.update v j (β r)) i.castSucc)
      (fieldPolygonPoint q y (Function.update v j (β r)) i.succ)^2) (d i) 0 := by
    by_cases hiL : i = j.castSucc
    · subst i
      have hd : d j.castSucc = L := by simp [d,hneLR]
      rw [hd]
      convert! hleft using 1
      funext r
      simp [fieldPolygonPoint_update,hneLeft]
    · by_cases hiR : i = j.succ
      · subst i
        have hd : d j.succ = R := by simp [d,hneLR.symm]
        rw [hd]
        convert! hright using 1
        funext r
        simp [fieldPolygonPoint_update,hmiddle,hneRight]
      · have hne₁ : i.castSucc ≠ j.castSucc.succ := by
          intro H
          apply hiR
          apply Fin.ext
          have Hv := congrArg Fin.val H
          simpa only [Fin.val_castSucc,Fin.val_succ] using Hv
        have hne₂ : i.succ ≠ j.castSucc.succ := by
          intro H
          apply hiL
          exact Fin.succ_injective _ H
        have hd : d i = 0 := by simp only [d,if_neg hiL,if_neg hiR,zero_add]
        rw [hd]
        convert! hasDerivAt_const (0 : ℝ) (inducedDistance h
          (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)^2) using 1
        funext r
        simp only [fieldPolygonPoint_update,if_neg hne₁,if_neg hne₂]
  have H := (HasDerivAt.sum (u := Finset.univ) (fun i _ => hedge i)).const_mul ((N+1 : ℕ) : ℝ)
  have hsum : (∑ i : Fin (N+1), d i) = L+R := by
    simp only [d,Finset.sum_add_distrib]
    simp
  rw [hsum] at H
  simpa only [fieldPolygonEnergy,Finset.sum_apply] using H

end Yau.LeafProofs.L23Aux
