import Yau.LeafProofs.L23LocalDistanceSupportPolygonLower

/-! Equality in finite polygon energy forces the sum of original edge distances to be d. -/
noncomputable section
open scoped BigOperators
namespace Yau.LeafProofs.L23Aux
variable {n N : ℕ} {M : ComplexManifold n}

theorem fieldPolygon_sum_dist_eq_of_energy_eq
    (h : HermitianField M) (hh : MetricSmooth h) (q y : M.Carrier) (v : Fin N → M.Carrier)
    (heq : fieldPolygonEnergy h q y v = inducedDistance h q y^2) :
    (∑ i : Fin (N+1), inducedDistance h
      (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)) = inducedDistance h q y := by
  letI := metricSpaceOfField h hh
  let d : Fin (N+1) → ℝ := fun i => inducedDistance h
    (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)
  have Htri : inducedDistance h q y ≤ ∑ i, d i := by
    have H := fin_chain_dist_le_sum (N+1) (fieldPolygonPoint q y v)
    have Hfinish : fieldPolygonPoint q y v (Fin.last (N+1)) = y := by
      change Fin.lastCases y v (Fin.last N) = y
      simp
    change inducedDistance h q (fieldPolygonPoint q y v (Fin.last (N+1))) ≤ ∑ i, d i at H
    rwa [Hfinish] at H
  have Hsum : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => inducedDistance_nonneg h hh _ _)
  have Hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (N+1))) (fun _ => (1 : ℝ)) d
  have Hcs' : (∑ i, d i)^2 ≤ fieldPolygonEnergy h q y v := by
    change (∑ i, d i)^2 ≤ (N+1 : ℕ)*∑ i, d i^2
    simpa only [one_mul,one_pow,Finset.sum_const,Fintype.card_fin,Finset.card_univ,
      nsmul_eq_mul,mul_one] using Hcs
  rw [heq] at Hcs'
  exact le_antisymm ((sq_le_sq₀ Hsum (inducedDistance_nonneg h hh q y)).mp Hcs') Htri

end Yau.LeafProofs.L23Aux
