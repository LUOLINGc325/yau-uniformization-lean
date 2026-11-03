import Yau.Proofs.P06HermitianCoercivity

noncomputable section
open scoped Topology ComplexOrder Matrix Matrix.Norms.Elementwise

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

theorem matrix_quadratic_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) {d : ℝ} (hd : 0 ≤ d) (hA : ∀ i j, ‖A i j‖ ≤ d) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ (n : ℝ) ^ 2 * d * (∑ i, ‖v i‖ ^ 2) := by
  let S : ℝ := ∑ i, ‖v i‖ ^ 2
  have hv (i : Fin n) : ‖v i‖ ^ 2 ≤ S :=
    Finset.single_le_sum (fun j _ => sq_nonneg (‖v j‖)) (Finset.mem_univ i)
  have hab (i j : Fin n) : ‖v i‖ * ‖v j‖ ≤ S := by
    nlinarith [sq_nonneg (‖v i‖ - ‖v j‖), hv i, hv j]
  have hterm (i j : Fin n) : ‖star (v i) * (A i j * v j)‖ ≤ d * S := by
    rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ ‖v i‖ * (d * ‖v j‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)) (norm_nonneg _)
      _ = d * (‖v i‖ * ‖v j‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hab i j) hd
  calc
    _ ≤ ‖star v ⬝ᵥ (A *ᵥ v)‖ := Complex.re_le_norm _
    _ = ‖∑ i, ∑ j, star (v i) * (A i j * v j)‖ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ‖∑ j, star (v i) * (A i j * v j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖star (v i) * (A i j * v j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, d * S :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem leviDirection_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) :
    leviDirection (A - B) v = leviDirection A v - leviDirection B v := by
  simp only [leviDirection, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- On a compact chart set the same original Hermitian metric at nearby
points has arbitrarily small relative quadratic variation, uniformly in
every complex direction. -/
theorem hMat_uniform_relative_upper {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKO : K ⊆ chartTarget x) {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, ∀ a : ComplexVector n, dist a z < r →
      a ∈ chartTarget x ∧ ∀ v : ComplexVector n,
        leviDirection (hMat g.form x a) v ≤ (1 + η) * leviDirection (hMat g.form x z) v := by
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨ρ, hρ, hρO⟩ := hK.exists_cthickening_subset_open hO hKO
  let D : Set (ComplexVector n) := Metric.cthickening ρ K
  have hD : IsCompact D := hK.cthickening
  obtain ⟨ell, hell, hcoercive⟩ := hMat_uniform_coercivity g x hK hKO
  let d : ℝ := η * ell / ((n : ℝ) ^ 2 + 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hc : ContinuousOn (fun z => hMat g.form x z) D := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact ((Yau.LeafProofs.L18Aux.hMat_contDiffOn g x) i j).continuousOn.mono hρO
  have hUC := hD.uniformContinuousOn_of_continuous hc
  obtain ⟨s, hs, hdist⟩ :=
    (Metric.uniformContinuousOn_iff (f := fun z : ComplexVector n => hMat g.form x z) (s := D)).mp hUC d hd
  refine ⟨min ρ s, lt_min hρ hs, ?_⟩
  intro z hz a ha
  have haD : a ∈ D := Metric.closedBall_subset_cthickening hz ρ
    (by exact (ha.trans_le (min_le_left ρ s)).le)
  have hzD : z ∈ D := Metric.self_subset_cthickening K hz
  refine ⟨hρO haD, ?_⟩
  intro v
  have hmat := hdist a haD z hzD (ha.trans_le (min_le_right ρ s))
  have hb : ∀ i j, ‖(hMat g.form x a - hMat g.form x z) i j‖ ≤ d := by
    intro i j
    rw [Matrix.sub_apply, ← dist_eq_norm]
    exact ((dist_le_pi_dist (hMat g.form x a i) (hMat g.form x z i) j).trans
      (dist_le_pi_dist (hMat g.form x a) (hMat g.form x z) i)).trans hmat.le
  have hq := matrix_quadratic_entry_bound (hMat g.form x a - hMat g.form x z)
    (WithLp.ofLp v) hd.le hb
  change leviDirection (hMat g.form x a - hMat g.form x z) v ≤
    (n : ℝ) ^ 2 * d * (∑ i, ‖WithLp.ofLp v i‖ ^ 2) at hq
  rw [leviDirection_sub] at hq
  have hfac : (n : ℝ) ^ 2 * d ≤ η * ell := by
    dsimp only [d]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < (n : ℝ) ^ 2 + 1 by positivity)).mpr
    nlinarith [mul_pos hη hell]
  have hS : 0 ≤ ∑ i, ‖WithLp.ofLp v i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right hfac hS
  have h2 := mul_le_mul_of_nonneg_left (hcoercive z hz (WithLp.ofLp v)) hη.le
  simp only [WithLp.toLp_ofLp] at h2
  nlinarith

end Yau.NodeProofs.P06Aux
