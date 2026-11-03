import Yau.LeafProofs.L10Tensor

/-! The actual nondivergence operator and its computed divergence drift. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology ComplexConjugate

namespace Yau.LeafProofs

def ellipticAdjustedDrift {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (z : ComplexVector n) (j : RIdx n) : ℝ :=
  b z j - ∑ i, fderiv ℝ (fun w => a w i j) z (realVec i)

def ellipticDivergence {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (u : ComplexVector n → ℂ) (z : ComplexVector n) : ℂ :=
  ∑ i, fderiv ℝ (fun w => ∑ j,
    (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z (realVec i)

theorem ellipticDivergence_expand {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (u : ComplexVector n → ℂ) (z : ComplexVector n)
    (ha : ∀ i j, DifferentiableAt ℝ (fun w => a w i j) z)
    (hu : ∀ j, DifferentiableAt ℝ (fun w => fderiv ℝ u w (realVec j)) z) :
    ellipticDivergence a u z =
      (∑ i, ∑ j, (a z i j : ℂ) *
        fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) z (realVec i)) +
      ∑ j, ((∑ i, fderiv ℝ (fun w => a w i j) z (realVec i) : ℝ) : ℂ) *
        fderiv ℝ u z (realVec j) := by
  classical
  have hac (i j : RIdx n) : HasFDerivAt (fun w => (a w i j : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun w => a w i j) z)) z := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasFDerivAt.comp z (ha i j).hasFDerivAt
  have hprod (i j : RIdx n) :
      fderiv ℝ (fun w => (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z (realVec i) =
        (a z i j : ℂ) * fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) z (realVec i) +
        (fderiv ℝ (fun w => a w i j) z (realVec i) : ℂ) *
          fderiv ℝ u z (realVec j) := by
    rw [fderiv_fun_mul (hac i j).differentiableAt (hu j)]
    rw [(hac i j).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    ring
  have hsum (i : RIdx n) :
      fderiv ℝ (fun w => ∑ j, (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z =
      ∑ j, fderiv ℝ (fun w => (a w i j : ℂ) * fderiv ℝ u w (realVec j)) z := by
    exact fderiv_fun_sum (fun j _ => (hac i j).differentiableAt.mul (hu j))
  unfold ellipticDivergence
  simp only [hsum,
    sum_apply, hprod, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

theorem ellipticOp_eq_divergence_add_drift {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℂ)
    (z : ComplexVector n)
    (ha : ∀ i j, DifferentiableAt ℝ (fun w => a w i j) z)
    (hu : ∀ j, DifferentiableAt ℝ (fun w => fderiv ℝ u w (realVec j)) z) :
    LeafCandidates.ellipticOp a b u z = ellipticDivergence a u z +
      ∑ j, (ellipticAdjustedDrift a b z j : ℂ) * fderiv ℝ u z (realVec j) := by
  rw [ellipticDivergence_expand a u z ha hu]
  unfold LeafCandidates.ellipticOp ellipticAdjustedDrift
  simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem ellipticOp_eq_divergence_add_drift_on {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => a w i j) O)
    (hu : ContDiffOn ℝ ∞ u O) {z : ComplexVector n} (hz : z ∈ O) :
    LeafCandidates.ellipticOp a b u z = ellipticDivergence a u z +
      ∑ j, (ellipticAdjustedDrift a b z j : ℂ) * fderiv ℝ u z (realVec j) := by
  apply ellipticOp_eq_divergence_add_drift
  · intro i j
    exact ((ha i j).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  · intro j
    have hu2 : ContDiffAt ℝ 2 u z := (hu.contDiffAt (hO.mem_nhds hz)).of_le (by simp)
    have hD : DifferentiableAt ℝ (fderiv ℝ u) z :=
      (hu2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hD.clm_apply (by fun_prop)

theorem elliptic_complex_coercivity {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (ell : ℝ)
    (h : ∀ v : ι → ℝ, ell * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, a i j * v i * v j)
    (v : ι → ℂ) :
    ell * ∑ i, ‖v i‖ ^ 2 ≤
      (∑ i, ∑ j, (a i j : ℂ) * v j * conj (v i)).re := by
  have hr := h (fun i => (v i).re)
  have hi := h (fun i => (v i).im)
  have hnorm : (∑ i, ‖v i‖ ^ 2) =
      (∑ i, (v i).re ^ 2) + ∑ i, (v i).im ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Finset.sum_add_distrib]
    simp only [pow_two]
  have hreal : (∑ i, ∑ j, (a i j : ℂ) * v j * conj (v i)).re =
      (∑ i, ∑ j, a i j * (v i).re * (v j).re) +
      ∑ i, ∑ j, a i j * (v i).im * (v j).im := by
    change Complex.reCLM _ = _
    simp only [map_sum, Complex.reCLM_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hnorm, hreal]
  linarith

theorem elliptic_coefficient_directional_bound {n : ℕ}
    (a : ComplexVector n → ℝ) (z : ComplexVector n) (i : RIdx n) {A : ℝ}
    (hA : ‖iteratedFDeriv ℝ 1 a z‖ ≤ A) :
    |fderiv ℝ a z (realVec i)| ≤ A := by
  have hn : ‖realVec i‖ = 1 := by
    rw [← complexVector_realOrthonormalBasis_apply]
    exact (complexVector_realOrthonormalBasis n).norm_eq_one _
  have h := (fderiv ℝ a z).le_opNorm (realVec i)
  rw [hn, mul_one, Real.norm_eq_abs] at h
  exact h.trans (by simpa only [norm_iteratedFDeriv_one] using hA)

theorem ellipticAdjustedDrift_abs_le {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (z : ComplexVector n) (j : RIdx n) {A : ℝ}
    (hb : |b z j| ≤ A) (ha : ∀ i, ‖iteratedFDeriv ℝ 1 (fun w => a w i j) z‖ ≤ A) :
    |ellipticAdjustedDrift a b z j| ≤ (2 * n + 1 : ℝ) * A := by
  unfold ellipticAdjustedDrift
  calc
    _ ≤ |b z j| + |∑ i, fderiv ℝ (fun w => a w i j) z (realVec i)| := abs_sub _ _
    _ ≤ A + ∑ i, |fderiv ℝ (fun w => a w i j) z (realVec i)| :=
      add_le_add hb (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ A + ∑ _i : RIdx n, A := by
      gcongr with i
      exact elliptic_coefficient_directional_bound _ z i (ha i)
    _ = _ := by simp [RIdx, Nat.cast_mul]; ring

theorem elliptic_original_coefficient_bounds {n s : ℕ} (hn : 0 < n)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {O : Set (ComplexVector n)} {A : ℝ}
    (hbound : ∀ k ≤ s + 1, ∀ z ∈ O, ∀ i j,
      ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
      ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A)
    {z : ComplexVector n} (hz : z ∈ O) :
    (∀ i j, |a z i j| ≤ A) ∧ (∀ i, |b z i| ≤ A) ∧
      (∀ i j k, |fderiv ℝ (fun w => a w i j) z (realVec k)| ≤ A) ∧
      ∀ j, |ellipticAdjustedDrift a b z j| ≤ (2 * n + 1 : ℝ) * A := by
  let j₀ : RIdx n := (⟨0, hn⟩, 0)
  have hb (i : RIdx n) : |b z i| ≤ A := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      (hbound 0 (by omega) z hz i j₀).2
  have ha1 (i j : RIdx n) : ‖iteratedFDeriv ℝ 1 (fun w => a w i j) z‖ ≤ A :=
    (hbound 1 (by omega) z hz i j).1
  refine ⟨?_, hb, ?_, ?_⟩
  · intro i j
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      (hbound 0 (by omega) z hz i j).1
  · intro i j k
    exact elliptic_coefficient_directional_bound _ z k (ha1 i j)
  · intro j
    exact ellipticAdjustedDrift_abs_le a b z j (hb j) (fun i => ha1 i j)

theorem interiorEllipticEstimate_dimension_zero_bound (s : ℕ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (a : ComplexVector 0 → Matrix (RIdx 0) (RIdx 0) ℝ)
    (b : ComplexVector 0 → RIdx 0 → ℝ) (u : ComplexVector 0 → ℂ) :
    Real.sqrt (LeafCandidates.sobolevNormSq (Metric.ball 0 r) u (s + 2)) ≤
      Real.sqrt (LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0) +
        Real.sqrt (LeafCandidates.sobolevNormSq (Metric.ball 0 R)
          (LeafCandidates.ellipticOp a b u) s) := by
  rw [sobolevNormSq_dimension_zero u (s + 2) hr,
    sobolevNormSq_dimension_zero u 0 hR]
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

end Yau.LeafProofs
