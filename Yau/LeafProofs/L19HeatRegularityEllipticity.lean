import Yau.LeafProofs.L19HeatRegularityWeakEquation

/-! Uniform ellipticity of the actual heat coefficients on compact chart regions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace Matrix
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every actual coordinate covector is bounded by the true inverse-metric
quadratic form with the covariant diagonal as its dual factor. -/
theorem scalarChart_covector_sq_le (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : RIdx n → ℝ) (i : RIdx n) :
    (v i)^2 ≤ realMetricFn g x z i i * dotProduct v ((realMetricFn g x z)⁻¹.mulVec v) := by
  classical
  let Q := realMetricFn g x z
  let e : RIdx n → ℝ := Pi.single i 1
  let w := Q.mulVec e
  have hQ : Q.PosDef := L12Aux.realMetricFn_posDef g x z hz
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hw : Q⁻¹.mulVec w = e := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q hd,Matrix.one_mulVec]
  have hwi : w i = Q i i := by simp only [w,e,Matrix.mulVec_single_one,Matrix.col_apply]
  have hh := hQ.inv.star_dotProduct_mulVec_mul_le v w
  simp only [star_trivial,hw,e,dotProduct_single_one] at hh
  simpa only [pow_two,hwi,mul_comm,Q] using hh

/-- An explicit finite-dimensional quadratic estimate, without choosing
an eigenbasis or any abstract ellipticity constants. -/
theorem scalarChart_matrix_quadratic_le {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    dotProduct v (A.mulVec v) ≤ (∑ i, ∑ j, |A i j|) * ∑ i, (v i)^2 := by
  classical
  let S := ∑ i, (v i)^2
  have hv (i : ι) : (v i)^2 ≤ S :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hab (i j : ι) : |v i * v j| ≤ S := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|v i| - |v j|),sq_abs (v i),sq_abs (v j),hv i,hv j]
  have ht (i j : ι) : v i * (A i j * v j) ≤ |A i j| * S := by
    calc
      _ ≤ |v i * (A i j * v j)| := le_abs_self _
      _ = |A i j| * |v i * v j| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hab i j) (abs_nonneg _)
  calc
    _ = ∑ i, ∑ j, v i * (A i j * v j) := by simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |A i j| * S := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = _ := by simp only [Finset.sum_mul,S]

/-- Positive lower and upper ellipticity constants are obtained internally
from the actual metric on every compact chart region. -/
theorem scalarHeatChartCoeff_elliptic (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget x) (I : Set ℝ) :
    ∃ lam upper : ℝ, Parabolic.Elliptic (K ×ˢ I) (scalarHeatChartCoeff g x) lam upper := by
  classical
  have hTc : ContinuousOn (fun z => ∑ i, realMetricFn g.form x z i i) K :=
    continuousOn_finsetSum Finset.univ (fun i _ =>
      (metricSmooth_of_smoothMetric g x i i).continuousOn.mono hKt)
  have hAc : ContinuousOn (fun z => ∑ i, ∑ j, |(realMetricFn g.form x z)⁻¹ i j|) K :=
    continuousOn_finsetSum Finset.univ (fun i _ => continuousOn_finsetSum Finset.univ (fun j _ =>
      ((realMetricFn_inverse_contDiffOn g x i j).continuousOn.mono hKt).abs))
  obtain ⟨c,hc⟩ := hK.bddAbove_image hTc
  obtain ⟨d,hd⟩ := hK.bddAbove_image hAc
  let B := max c 1
  let U := max d 1
  let lam := 1 / (2 * B)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos (by norm_num) hB)
  refine ⟨lam,max (U / 2) lam,hlam,le_max_right _ _,?_⟩
  intro p hp
  refine ⟨?_,?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    change (1 / 2 : ℝ) * (realMetricFn g.form x p.1)⁻¹ j i =
      (1 / 2 : ℝ) * (realMetricFn g.form x p.1)⁻¹ i j
    rw [(realMetricFn_isSymm g.form x p.1).inv.apply i j]
  · intro v
    let Q := realMetricFn g.form x p.1
    let P := dotProduct v (Q⁻¹.mulVec v)
    let S := ∑ i, (v i)^2
    have hQ : Q.PosDef := L12Aux.realMetricFn_posDef g.form x p.1 (hKt hp.1)
    have hP : 0 ≤ P := by
      simpa only [star_trivial] using hQ.inv.posSemidef.dotProduct_mulVec_nonneg v
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
    have hlow : S ≤ B * P := by
      calc
        S ≤ ∑ i, Q i i * P := Finset.sum_le_sum (fun i _ =>
          scalarChart_covector_sq_le g.form x (hKt hp.1) v i)
        _ = (∑ i, Q i i) * P := (Finset.sum_mul _ _ _).symm
        _ ≤ B * P := mul_le_mul_of_nonneg_right
          ((hc ⟨p.1,hp.1,rfl⟩).trans (le_max_left _ _)) hP
    have hupp : P ≤ U * S :=
      (scalarChart_matrix_quadratic_le Q⁻¹ v).trans (mul_le_mul_of_nonneg_right
        ((hd ⟨p.1,hp.1,rfl⟩).trans (le_max_left _ _)) hS)
    have hq : (∑ i, ∑ j, scalarHeatChartCoeff g x p i j * v i * v j) = P / 2 := by
      dsimp only [P,Q]
      simp only [scalarHeatChartCoeff,dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hq]
    refine ⟨?_,?_⟩
    · calc
        lam * S ≤ lam * (B * P) := mul_le_mul_of_nonneg_left hlow hlam.le
        _ = P / 2 := by dsimp only [lam]; field_simp
    · calc
        P / 2 ≤ (U * S) / 2 := div_le_div_of_nonneg_right hupp (by norm_num)
        _ = (U / 2) * S := by ring
        _ ≤ max (U / 2) lam * S := mul_le_mul_of_nonneg_right (le_max_left _ _) hS

end Yau.LeafProofs.L19Aux
