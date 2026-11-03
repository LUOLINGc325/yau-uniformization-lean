import Yau.LeafProofs.L23LocalDistanceSupportPolygon

/-! Every finite polygon in the whole manifold has energy at least d². -/
noncomputable section
open scoped BigOperators
namespace Yau.LeafProofs.L23Aux
variable {n N : ℕ} {M : ComplexManifold n}

theorem fin_chain_dist_le_sum {α : Type*} [PseudoMetricSpace α] (N : ℕ)
    (x : Fin (N+1) → α) :
    dist (x 0) (x (Fin.last N)) ≤ ∑ i : Fin N, dist (x i.castSucc) (x i.succ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have H := ih (fun i => x i.castSucc)
    rw [Fin.sum_univ_castSucc]
    exact (dist_triangle (x 0) (x (Fin.last N).castSucc) (x (Fin.last (N+1)))).trans
      (add_le_add H le_rfl)

theorem inducedDistance_sq_le_fieldPolygonEnergy
    (h : HermitianField M) (hh : MetricSmooth h) (q y : M.Carrier) (v : Fin N → M.Carrier) :
    inducedDistance h q y ^ 2 ≤ fieldPolygonEnergy h q y v := by
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
  have Hsq : inducedDistance h q y ^ 2 ≤ (∑ i, d i)^2 :=
    (sq_le_sq₀ (inducedDistance_nonneg h hh q y) Hsum).mpr Htri
  have Hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (N+1)))
    (fun _ => (1 : ℝ)) d
  have Hcs' : (∑ i, d i)^2 ≤ (N+1 : ℕ)*∑ i, d i^2 := by simpa only [one_mul,one_pow,
    Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul,mul_one] using Hcs
  exact Hsq.trans Hcs'

end Yau.LeafProofs.L23Aux
