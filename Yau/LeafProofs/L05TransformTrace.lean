import Yau.LeafProofs.L05DualEllipticity
import Yau.LeafProofs.L05TransformAlgebra

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem rankOne_norm {n : ℕ} (v : RIdx n → ℝ) : ‖rankOne v‖=∑ i, (v i)^2 := by
  have hs : ‖rankOne v‖^2=(∑ i, (v i)^2)^2 := by
    change ‖(rankOne v : Mat n)‖^2=_
    rw [frobenius_norm_sq,rankOne_coe]
    simp only [mul_pow,← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hsum : 0 ≤ ∑ i : RIdx n, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith only [hs,norm_nonneg (rankOne v),hsum]

def symTraceLinear (n : ℕ) : Sym n →ₗ[ℝ] ℝ where
  toFun A := Matrix.trace (A : Mat n)
  map_add' A B := Matrix.trace_add _ _
  map_smul' c A := by
    change Matrix.trace (c • (A : Mat n))=c*Matrix.trace (A : Mat n)
    exact Matrix.trace_smul c (A : Mat n)

theorem chuTransform_trace_rankOne {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) {p : Point n} (hp : p ∈ backward 1) (v : RIdx n → ℝ) :
    K⁻¹*(∑ i, (v i)^2) ≤ Matrix.trace (T (rankOne v) p : Mat n) ∧
      Matrix.trace (T (rankOne v) p : Mat n) ≤ Real.sqrt (Fintype.card (RIdx n))*K*(∑ i, (v i)^2) := by
  have hh := hT.2.2.2 (rankOne v) (rankOne_posSemidef v) p hp
  have hlow := posSemidef_norm_le_trace hh.1
  have hupp := trace_le_sqrt_card_mul_norm (T (rankOne v) p : Mat n)
  rw [rankOne_norm] at hh
  constructor
  · exact hh.2.1.trans hlow
  · exact hupp.trans (by
      have hmul := mul_le_mul_of_nonneg_left hh.2.2 (Real.sqrt_nonneg (Fintype.card (RIdx n)))
      convert! hmul using 1 <;> simp only [mul_assoc])

theorem chuTransform_trace_bounds {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) {p : Point n} (hp : p ∈ backward 1) {P : Sym n}
    (hP : (P : Mat n).PosSemidef) :
    K⁻¹*Matrix.trace (P : Mat n) ≤ Matrix.trace (T P p : Mat n) ∧
      Matrix.trace (T P p : Mat n) ≤ Real.sqrt (Fintype.card (RIdx n))*K*Matrix.trace (P : Mat n) := by
  let l := (symTraceLinear n).comp (chuTransformLinear hT p hp)
  have hquad : ∀ v : RIdx n → ℝ, K⁻¹*(∑ i, (v i)^2) ≤ l (rankOne v) ∧
      l (rankOne v) ≤ Real.sqrt (Fintype.card (RIdx n))*K*(∑ i, (v i)^2) :=
    chuTransform_trace_rankOne hT hp
  have hA := dualMatrix_mem_slopeSet l hquad
  have hh := slopeSet_tracePair_bounds hA hP
  rw [← dualMatrix_apply l P] at hh
  exact hh

end Yau.LeafProofs.L05Aux
