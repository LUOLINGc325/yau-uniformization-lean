import Yau.LeafProofs.L05TransformTrace

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuIdentitySym (n : ℕ) : Sym n := ⟨1,IsSelfAdjoint.one _⟩

theorem tracePair_add_left {n : ℕ} (A B H : Sym n) : tracePair (A+B) H=tracePair A H+tracePair B H := by
  simp only [tracePair,AddSubgroup.coe_add,Matrix.add_mul,Matrix.trace_add]

theorem tracePair_smul_left {n : ℕ} (A H : Sym n) (c : ℝ) : tracePair (c • A) H=c*tracePair A H := by
  simp only [tracePair,selfAdjoint.val_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]

theorem tracePair_identity_left {n : ℕ} (H : Sym n) : tracePair (chuIdentitySym n) H=Matrix.trace (H : Mat n) := by
  change Matrix.trace ((1 : Mat n)*(H : Mat n))=_
  rw [Matrix.one_mul]

theorem sym_posSemidef_of_traceRankOne {n : ℕ} (H : Sym n)
    (hH : ∀ v : RIdx n → ℝ, 0 ≤ tracePair H (rankOne v)) : (H : Mat n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr H.property)
  intro v
  rw [← tracePair_rankOne]
  exact hH v

theorem sym_add_norm_identity_posSemidef {n : ℕ} (H : Sym n) :
    ((H+((Real.sqrt (Fintype.card (RIdx n))*‖H‖) • chuIdentitySym n) : Sym n) : Mat n).PosSemidef := by
  apply sym_posSemidef_of_traceRankOne
  intro v
  have hh : |tracePair H (rankOne v)| ≤ Real.sqrt (Fintype.card (RIdx n))*‖H‖*‖rankOne v‖ := by
    convert! abs_trace_mul_le (H : Mat n) (rankOne v : Mat n) using 1
  rw [rankOne_norm] at hh
  rw [tracePair_add_left,tracePair_smul_left,tracePair_identity_left,rankOne_trace]
  linarith only [(abs_le.mp hh).1]

def chuTransformNormConstant (n : ℕ) (K : ℝ) : ℝ :=
  K*(1+2*Real.sqrt (Fintype.card (RIdx n))*(Fintype.card (RIdx n):ℝ))

theorem chuTransform_norm_le {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hK : 0 ≤ K) (hT : ChuH2 T K beta) {p : Point n} (hp : p ∈ backward 1) (H : Sym n) :
    ‖T H p‖ ≤ chuTransformNormConstant n K*‖H‖ := by
  let r := Real.sqrt (Fintype.card (RIdx n))*‖H‖
  let R := r • chuIdentitySym n
  let P := H+R
  have hr : 0 ≤ r := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hR : (R : Mat n).PosSemidef := Matrix.PosSemidef.one.smul hr
  have hP : (P : Mat n).PosSemidef := sym_add_norm_identity_posSemidef H
  have hTP := (hT.2.2.2 P hP p hp).2.2
  have hTR := (hT.2.2.2 R hR p hp).2.2
  have hPR : P-R=H := by dsimp only [P]; abel
  have hlin := (chuTransformLinear hT p hp).map_sub P R
  change T (P-R) p=T P p-T R p at hlin
  rw [hPR] at hlin
  have hnorm : ‖T H p‖ ≤ K*‖P‖+K*‖R‖ := by
    rw [hlin]
    exact (norm_sub_le _ _).trans (add_le_add hTP hTR)
  have hI : ‖chuIdentitySym n‖ ≤ (Fintype.card (RIdx n):ℝ) := by
    change ‖(1 : Mat n)‖ ≤ _
    simpa only [Matrix.trace_one] using posSemidef_norm_le_trace (Matrix.PosSemidef.one : (1 : Mat n).PosSemidef)
  have hRn : ‖R‖ ≤ r*(Fintype.card (RIdx n):ℝ) := by
    change ‖r • chuIdentitySym n‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hI hr
  have hPn : ‖P‖ ≤ ‖H‖+‖R‖ := norm_add_le H R
  have hPK := mul_le_mul_of_nonneg_left hPn hK
  have hRK := mul_le_mul_of_nonneg_left hRn hK
  dsimp only [chuTransformNormConstant,r] at *
  nlinarith only [hnorm,hPK,hRK]

def chuTransformCLM {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hK : 0 ≤ K) (hT : ChuH2 T K beta) (p : Point n) (hp : p ∈ backward 1) : Sym n →L[ℝ] Sym n :=
  (chuTransformLinear hT p hp).mkContinuous (chuTransformNormConstant n K)
    (fun H => chuTransform_norm_le hK hT hp H)

end Yau.LeafProofs.L05Aux
