import Yau.LeafProofs.L09

/-! Coordinate energy bounds for the original L10 Sobolev norms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem multilinear_basis_expansion
    {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) (m : Fin k → E) :
    T m = ∑ w : Fin k → ι,
      (∏ j, b.repr (m j) (w j)) • T (fun j => b (w j)) := by
  classical
  conv_lhs => rw [show m = fun j => ∑ i, b.repr (m j) i • b i by
    funext j; exact (b.sum_repr (m j)).symm]
  change T.toMultilinearMap (fun j => ∑ i, b.repr (m j) i • b i) = _
  rw [T.toMultilinearMap.map_sum]
  simp_rw [T.toMultilinearMap.map_smul_univ]
  rfl

theorem multilinear_norm_le_basis_sum
    {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :
    ‖T‖ ≤ ∑ w : Fin k → ι, ‖T (fun j => b (w j))‖ := by
  classical
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro m
  rw [multilinear_basis_expansion b T m]
  calc
    _ ≤ ∑ w : Fin k → ι,
        ‖(∏ j, b.repr (m j) (w j)) • T (fun j => b (w j))‖ := norm_sum_le _ _
    _ ≤ ∑ w : Fin k → ι, (∏ j, ‖m j‖) * ‖T (fun j => b (w j))‖ := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      rw [b.repr_apply_apply]
      exact (norm_inner_le_norm _ _).trans_eq (by rw [b.norm_eq_one, one_mul])
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem multilinear_basis_energy_le
    {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :
    ∑ w : Fin k → ι, ‖T (fun j => b (w j))‖ ^ 2 ≤
      (Fintype.card ι : ℝ) ^ k * ‖T‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ _w : Fin k → ι, ‖T‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa [b.norm_eq_one] using T.le_opNorm (fun j => b (w j))
    _ = _ := by simp

theorem multilinear_norm_sq_le_basis_energy
    {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :
    ‖T‖ ^ 2 ≤ ∑ w : Fin k → ι, ‖T (fun j => b (w j))‖ ^ 2 := by
  classical
  let H := ∑ w : Fin k → ι, ‖T (fun j => b (w j))‖ ^ 2
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : ‖T‖ ≤ Real.sqrt H := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg _)
    intro m
    have hcoords : (∑ w : Fin k → ι, (∏ j, ‖b.repr (m j) (w j)‖) ^ 2) =
        (∏ j, ‖m j‖) ^ 2 := by
      simp_rw [← Finset.prod_pow]
      rw [← Fintype.prod_sum (fun j i => ‖b.repr (m j) i‖ ^ 2)]
      congr 1
      funext j
      simp_rw [b.repr_apply_apply]
      exact b.sum_sq_norm_inner_right (m j)
    have hnorm : ‖T m‖ ≤ ∑ w : Fin k → ι,
        (∏ j, ‖b.repr (m j) (w j)‖) * ‖T (fun j => b (w j))‖ := by
      rw [multilinear_basis_expansion b T m]
      simpa only [norm_smul, norm_prod] using
        norm_sum_le (s := Finset.univ) (f := fun w : Fin k → ι =>
          (∏ j, b.repr (m j) (w j)) • T (fun j => b (w j)))
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun w : Fin k → ι => ∏ j, ‖b.repr (m j) (w j)‖)
      (fun w : Fin k → ι => ‖T (fun j => b (w j))‖)
    rw [hcoords] at hsq
    have hnormsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hprod : 0 ≤ ∏ j, ‖m j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hsqrt := Real.sq_sqrt hH
    dsimp only [H] at hsqrt ⊢
    nlinarith [Real.sqrt_nonneg H, mul_nonneg (Real.sqrt_nonneg H) hprod]
  have := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rwa [Real.sq_sqrt hH] at this

/-- An ordered real-coordinate derivative, retaining the original ambient derivative. -/
def ellipticWordDerivative {n k : ℕ} (u : ComplexVector n → ℂ)
    (w : Fin k → RIdx n) (z : ComplexVector n) : ℂ :=
  iteratedFDeriv ℝ k u z (fun j => realVec (w j))

/-- The Hilbert--Schmidt energy is used only as a proved comparison norm. -/
def ellipticWordEnergy {n : ℕ} (u : ComplexVector n → ℂ)
    (k : ℕ) (z : ComplexVector n) : ℝ :=
  ∑ w : Fin k → RIdx n, ‖ellipticWordDerivative u w z‖ ^ 2

theorem ellipticWordDerivative_succ {n k : ℕ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    {z : ComplexVector n} (hz : z ∈ O) (w : Fin (k + 1) → RIdx n) :
    ellipticWordDerivative u w z =
      fderiv ℝ (ellipticWordDerivative u (Fin.tail w)) z (realVec (w 0)) := by
  have hD := (hu.contDiffAt (hO.mem_nhds hz)).differentiableAt_iteratedFDeriv
    (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
  exact hD.iteratedFDeriv_succ_apply_left'

theorem ellipticWordDerivative_norm_le {n k : ℕ} (u : ComplexVector n → ℂ)
    (w : Fin k → RIdx n) (z : ComplexVector n) :
    ‖ellipticWordDerivative u w z‖ ≤ ‖iteratedFDeriv ℝ k u z‖ := by
  have hn (j : Fin k) : ‖realVec (w j)‖ = 1 := by
    rw [← complexVector_realOrthonormalBasis_apply]
    exact (complexVector_realOrthonormalBasis n).norm_eq_one _
  simpa [ellipticWordDerivative, hn] using
    (iteratedFDeriv ℝ k u z).le_opNorm (fun j => realVec (w j))

theorem iteratedFDeriv_sq_le_ellipticWordEnergy {n : ℕ}
    (u : ComplexVector n → ℂ) (k : ℕ) (z : ComplexVector n) :
    ‖iteratedFDeriv ℝ k u z‖ ^ 2 ≤ ellipticWordEnergy u k z := by
  simpa only [ellipticWordEnergy, ellipticWordDerivative,
    complexVector_realOrthonormalBasis_apply] using
    multilinear_norm_sq_le_basis_energy (complexVector_realOrthonormalBasis n)
      (iteratedFDeriv ℝ k u z)

theorem ellipticWordEnergy_le_iteratedFDeriv_sq {n : ℕ}
    (u : ComplexVector n → ℂ) (k : ℕ) (z : ComplexVector n) :
    ellipticWordEnergy u k z ≤ (2 * n : ℝ) ^ k * ‖iteratedFDeriv ℝ k u z‖ ^ 2 := by
  simpa only [ellipticWordEnergy, ellipticWordDerivative,
    complexVector_realOrthonormalBasis_apply, RIdx, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, mul_comm (n : ℝ) 2] using
    multilinear_basis_energy_le (complexVector_realOrthonormalBasis n)
      (iteratedFDeriv ℝ k u z)

theorem ellipticWordDerivative_continuousOn {n k : ℕ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (w : Fin k → RIdx n) : ContinuousOn (ellipticWordDerivative u w) O := by
  intro z hz
  exact (((hu.contDiffAt (hO.mem_nhds hz)).differentiableAt_iteratedFDeriv
    (m := k) (by exact_mod_cast ENat.natCast_lt_top k)).continuousMultilinear_apply_const
      (fun j => realVec (w j))).continuousAt.continuousWithinAt

theorem ellipticWordDerivative_sq_integrableOn {n k : ℕ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (hi : IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖ ^ 2) O (lebesgueC n))
    (w : Fin k → RIdx n) :
    IntegrableOn (fun z => ‖ellipticWordDerivative u w z‖ ^ 2) O (lebesgueC n) := by
  apply hi.mono' ((ellipticWordDerivative_continuousOn hO hu w).norm.pow 2
    |>.aestronglyMeasurable hO.measurableSet)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (ellipticWordDerivative_norm_le u w z) 2

theorem ellipticWordEnergy_integrableOn {n : ℕ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    {k : ℕ} (hi : IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖ ^ 2)
      O (lebesgueC n)) : IntegrableOn (ellipticWordEnergy u k) O (lebesgueC n) := by
  classical
  exact integrable_finsetSum _ (fun w _ => ellipticWordDerivative_sq_integrableOn hO hu hi w)

theorem integral_iteratedFDeriv_sq_le_ellipticWordEnergy {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O) {k : ℕ}
    (hi : IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖ ^ 2) O (lebesgueC n)) :
    (∫ z in O, ‖iteratedFDeriv ℝ k u z‖ ^ 2 ∂lebesgueC n) ≤
      ∫ z in O, ellipticWordEnergy u k z ∂lebesgueC n :=
  integral_mono hi (ellipticWordEnergy_integrableOn hO hu hi)
    (iteratedFDeriv_sq_le_ellipticWordEnergy u k)

theorem sobolevNormSq_dimension_zero (u : ComplexVector 0 → ℂ)
    (s : ℕ) {r : ℝ} (hr : 0 < r) :
    LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector 0) r) u s = ‖u 0‖ ^ 2 := by
  have hu : u = fun _ => u 0 := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  have hball : Metric.ball (0 : ComplexVector 0) r = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    simpa only [Subsingleton.elim x 0] using Metric.mem_ball_self hr
  unfold LeafCandidates.sobolevNormSq
  simp only [hball, lebesgueC_zero, Measure.restrict_univ, integral_dirac]
  rw [Finset.sum_eq_single 0]
  · simp only [norm_iteratedFDeriv_zero]
  · intro k _ hk
    rw [hu, iteratedFDeriv_const_of_ne hk]
    simp
  · simp

end Yau.LeafProofs
