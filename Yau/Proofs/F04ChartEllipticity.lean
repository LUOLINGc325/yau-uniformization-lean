import Yau.Proofs.F04ChartCoefficients

open Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L18Aux

theorem real_covector_coordinate_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosDef) (v : ι → ℝ) (i : ι) :
    (v i) ^ 2 ≤ Q i i * dotProduct v (Q⁻¹ *ᵥ v) := by
  let e : ι → ℝ := Pi.single i 1
  let w := Q *ᵥ e
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hw : Q⁻¹ *ᵥ w = e := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q hd, Matrix.one_mulVec]
  have hwi : w i = Q i i := by simp only [w, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have hh := hQ.inv.star_dotProduct_mulVec_mul_le v w
  simp only [star_trivial, hw, e, dotProduct_single_one] at hh
  simpa only [pow_two, hwi, mul_comm] using hh

theorem real_matrix_quadratic_le_norm {n : ℕ} (A : Mat n) (v : RIdx n → ℝ) :
    dotProduct v (A *ᵥ v) ≤ ‖A‖ * ∑ i, (v i) ^ 2 := by
  have heq : dotProduct v (A *ᵥ v) = ∑ i, ∑ j, A i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact (le_abs_self _).trans (quadratic_le_frobenius A v)

/-- Uniform ellipticity is constructed from compact physical coefficient data.
No completeness or supplied ellipticity for h_t is used. -/
theorem flowChartPrincipal_elliptic {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) {I : Set ℝ} (hh : MetricFamilySmooth h I) (x : M.Carrier)
    {K : Set (Point n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget x ×ˢ I) :
    ∃ lam upper : ℝ, Elliptic K (flowChartPrincipal h x) lam upper := by
  classical
  have hTc : ContinuousOn (fun p : Point n => ∑ i, realMetricFn (h p.2) x p.1 i i) K :=
    continuousOn_finsetSum Finset.univ (fun i _ => (hh x i i).continuousOn.mono hKt)
  have hinv : ContDiffOn ℝ ∞ (fun p : Point n => (realMetricFn (h p.2) x p.1)⁻¹)
      (chartTarget x ×ˢ I) :=
    matrix_contDiffOn_of_entries (contDiffOn_matrix_inv (hh x)
      (fun p hp => (LeafProofs.L12Aux.realMetricFn_posDef (h p.2) x p.1 hp.1).det_pos.ne'))
  obtain ⟨c, hc⟩ := hK.bddAbove_image hTc
  obtain ⟨d, hd⟩ := hK.bddAbove_image (hinv.continuousOn.norm.mono hKt)
  let B : ℝ := max c 1
  let U : ℝ := max d 1
  let lam : ℝ := 1 / (2 * B)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos (by norm_num) hB)
  refine ⟨lam, max (U / 2) lam, hlam, le_max_right _ _, ?_⟩
  intro p hp
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    change (1 / 2 : ℝ) * (realMetricFn (h p.2) x p.1)⁻¹ j i =
      (1 / 2 : ℝ) * (realMetricFn (h p.2) x p.1)⁻¹ i j
    rw [(realMetricFn_isSymm (h p.2) x p.1).inv.apply i j]
  intro v
  let Q := realMetricFn (h p.2) x p.1
  let P := dotProduct v (Q⁻¹ *ᵥ v)
  let S := ∑ i, (v i) ^ 2
  have hQ : Q.PosDef := LeafProofs.L12Aux.realMetricFn_posDef (h p.2) x p.1 (hKt hp).1
  have hP : 0 ≤ P := by
    simpa only [star_trivial] using hQ.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hlow : S ≤ B * P := by
    calc
      _ ≤ ∑ i, Q i i * P := Finset.sum_le_sum (fun i _ => real_covector_coordinate_sq_le Q hQ v i)
      _ = (∑ i, Q i i) * P := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right ((hc ⟨p, hp, rfl⟩).trans (le_max_left _ _)) hP
  have hupp : P ≤ U * S :=
    (real_matrix_quadratic_le_norm Q⁻¹ v).trans
      (mul_le_mul_of_nonneg_right ((hd ⟨p, hp, rfl⟩).trans (le_max_left _ _)) hS)
  have hq : (∑ i, ∑ j, flowChartPrincipal h x p i j * v i * v j) = P / 2 := by
    dsimp only [P, Q]
    simp only [flowChartPrincipal, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq]
  constructor
  · calc
      _ ≤ lam * (B * P) := mul_le_mul_of_nonneg_left hlow hlam.le
      _ = P / 2 := by dsimp only [lam]; field_simp
  · calc
      _ ≤ (U * S) / 2 := div_le_div_of_nonneg_right hupp (by norm_num)
      _ = (U / 2) * S := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hS

end Yau.F04Proof
