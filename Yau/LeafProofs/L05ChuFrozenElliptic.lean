import Yau.LeafProofs.L05ChuFrozenEquation

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem tracePair_rankOne_eq_principal {n : ℕ} (A : Sym n) (v : RIdx n → ℝ) :
    tracePair A (rankOne v)=∑ i, ∑ j, (A : Mat n) i j*v i*v j := by
  rw [tracePair_rankOne]
  simp only [star_trivial,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem slopeSet_elliptic_max {n : ℕ} {A : Sym n} {ell L : ℝ}
    (hell : 0 < ell) (hA : A ∈ slopeSet n ell L) (Q : Set (Point n)) :
    Elliptic Q (fun _ => (A : Mat n)) ell (max ell L) := by
  refine ⟨hell,le_max_left _ _,?_⟩
  intro p hp
  refine ⟨(Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property).isSymm,?_⟩
  intro v
  have hh := slopeSet_tracePair_bounds hA (rankOne_posSemidef v)
  rw [rankOne_trace,tracePair_rankOne_eq_principal] at hh
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))))⟩

theorem chuFrozenSlope_elliptic {n : ℕ} {E U : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {ell L K beta : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (hK : 0 < K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1) (Q : Set (Point n)) :
    Elliptic Q (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n))
      (chuCoarseLower ell K) (chuCoarseUpper n ell L K) := by
  exact slopeSet_elliptic_max (mul_pos hell (inv_pos.mpr hK))
    (chuFrozenSlope_mem_slopeSet hell.le hL hF hT hA0 hp0) Q

end Yau.LeafProofs.L05Aux
