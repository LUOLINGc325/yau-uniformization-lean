import Yau.LeafProofs.L03HodgeDivergenceWeak

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

/-- A smooth positive matrix field has a uniform quadratic lower bound
on each compact subset of its actual positive domain. Empty index types
are included, and no global ellipticity is asserted. -/
theorem uniform_matrix_coercivity_on_compact {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    (T : E → Matrix ι ι ℝ) (O : Set E)
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z => T z i j) O)
    (hpos : ∀ z ∈ O, (T z).PosDef)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ z ∈ K, ∀ v : ι → ℝ,
      ell * (∑ i, (v i) ^ 2) ≤ dotProduct v ((T z).mulVec v) := by
  classical
  have hinv (i j : ι) : ContDiffOn ℝ ∞ (fun z => (T z)⁻¹ i j) O :=
    L18Aux.contDiffOn_matrix_inv hT (fun z hz => ne_of_gt (hpos z hz).det_pos) i j
  have hdiag : ContinuousOn (fun z => ∑ i, |(T z)⁻¹ i i|) K :=
    continuousOn_finsetSum Finset.univ (fun i _ => ((hinv i i).continuousOn.mono hKO).abs)
  obtain ⟨d, hd⟩ := hK.bddAbove_image hdiag
  let D : ℝ := max d 0 + 1
  have hD : 0 < D := by dsimp only [D]; linarith [le_max_right d 0]
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro z hz v
  have hTz := hpos z (hKO hz)
  have hq : 0 ≤ dotProduct v ((T z).mulVec v) := by
    simpa only [star_trivial] using hTz.posSemidef.dotProduct_mulVec_nonneg v
  have hs : (∑ i, (v i) ^ 2) ≤ (∑ i, |(T z)⁻¹ i i|) * dotProduct v ((T z).mulVec v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : (v i) ^ 2 ≤ (T z)⁻¹ i i * dotProduct v ((T z).mulVec v) := by
      simpa only [star_trivial] using matrix_coordinate_sq_le (T z) hTz v i
    exact hi.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) hq)
  have hdz : (∑ i, |(T z)⁻¹ i i|) ≤ D := by
    have h := hd ⟨z, hz, rfl⟩
    dsimp only [D]
    linarith [le_max_left d 0]
  have hfinal := hs.trans (mul_le_mul_of_nonneg_right hdz hq)
  have hdiv := (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hfinal)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

namespace HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

/-- The actual principal tensor is the positive tensor product of the
inverse base metric and the volume-weighted form Gram. -/
def principalMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) : Matrix (RIdx n × α) (RIdx n × α) ℝ :=
  Matrix.kronecker (realMetricFn g x z)⁻¹ (gram g x b z)

theorem principalMatrix_entry {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (z : ComplexVector n) (i j : RIdx n) (r c : α) :
    principalMatrix g x b z (i, r) (j, c) = a g x b r c i j z := rfl

theorem principalMatrix_posDef {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) : (principalMatrix g x b z).PosDef :=
  (realMetricFn_posDef_of_mem_target g x hz).inv.kronecker (gram_posDef g x b hz)

theorem principalMatrix_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (i j : RIdx n × α) :
    ContDiffOn ℝ ∞ (fun z => principalMatrix g.form x b z i j) (chartTarget x) :=
  (L18Aux.realMetricFn_inverse_contDiffOn g x i.1 j.1).mul
    (gram_contDiffOn g x b i.2 j.2)

/-- The genuine Hodge principal tensor is uniformly coercive on every
compact chart buffer, including all form degrees and dimension zero. -/
theorem principalMatrix_uniform_coercivity {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ chartTarget x) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ z ∈ K, ∀ v : RIdx n × α → ℝ,
      ell * (∑ i, (v i) ^ 2) ≤ dotProduct v ((principalMatrix g.form x b z).mulVec v) :=
  uniform_matrix_coercivity_on_compact (principalMatrix g.form x b) (chartTarget x)
    (principalMatrix_contDiffOn g x b) (fun _ hz => principalMatrix_posDef g.form x b hz) hK hKO

/-- Coordinate form of the same actual tensor-product coercivity, in
the row/column ordering of the genuine divergence operator. -/
theorem a_uniform_coercivity {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ chartTarget x) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ z ∈ K, ∀ v : RIdx n × α → ℝ,
      ell * (∑ i, (v i) ^ 2) ≤
        ∑ r, ∑ c, ∑ i, ∑ j, a g.form x b r c i j z * v (j, c) * v (i, r) := by
  classical
  obtain ⟨ell, hell, hb⟩ := principalMatrix_uniform_coercivity g x b hK hKO
  refine ⟨ell, hell, fun z hz v => (hb z hz v).trans_eq ?_⟩
  have hqexpand : dotProduct v ((principalMatrix g.form x b z).mulVec v) =
      ∑ i, ∑ r, ∑ j, ∑ c, v (i, r) * (a g.form x b r c i j z * v (j, c)) := by
    simp only [dotProduct, Matrix.mulVec]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, principalMatrix_entry]
  rw [hqexpand]
  calc
    (∑ i, ∑ r, ∑ j, ∑ c, v (i, r) * (a g.form x b r c i j z * v (j, c))) =
        ∑ r, ∑ i, ∑ j, ∑ c, v (i, r) * (a g.form x b r c i j z * v (j, c)) := Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ c, ∑ j, v (i, r) * (a g.form x b r c i j z * v (j, c)) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ r, ∑ c, ∑ i, ∑ j, v (i, r) * (a g.form x b r c i j z * v (j, c)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end HodgeDivergenceWeak

end Yau.LeafProofs.L03
