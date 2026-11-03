import Yau.LeafProofs.L23TensorNormCalculus
import Yau.LeafProofs.L23RicciBound

/-! The finite tensor contraction estimate underlying Kato's inequality. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem covTensorPair_symm (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A B : CovTensor n r) : covTensorPair G A B=covTensorPair G B A :=
  tensorContraction_symm _ (by
    change G⁻¹ᵀ=G⁻¹
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.inv.isHermitian.eq) A B

theorem covTensorPair_sub_left (G : Matrix (RIdx n) (RIdx n) ℝ) (A B C : CovTensor n r) :
    covTensorPair G (fun v => A v-B v) C=covTensorPair G A C-covTensorPair G B C := by
  simp only [covTensorPair,sub_mul,Finset.sum_sub_distrib]

theorem covTensorPair_sub_right (G : Matrix (RIdx n) (RIdx n) ℝ) (A B C : CovTensor n r) :
    covTensorPair G A (fun v => B v-C v)=covTensorPair G A B-covTensorPair G A C := by
  simp only [covTensorPair,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem covTensorPair_mul_left (G : Matrix (RIdx n) (RIdx n) ℝ) (A B : CovTensor n r) (c : ℝ) :
    covTensorPair G (fun v => c*A v) B=c*covTensorPair G A B := by
  simp only [covTensorPair,Finset.mul_sum,mul_assoc]

theorem covTensorPair_mul_right (G : Matrix (RIdx n) (RIdx n) ℝ) (A B : CovTensor n r) (c : ℝ) :
    covTensorPair G A (fun v => c*B v)=c*covTensorPair G A B := by
  simp only [covTensorPair,Finset.mul_sum,mul_assoc,mul_left_comm]

theorem covTensorPair_succ (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n (r+1)) :
    covTensorPair G A B = ∑ i, ∑ j, G⁻¹ i j*
      covTensorPair G (fun v => A (Fin.cons i v)) (fun v => B (Fin.cons j v)) := by
  unfold covTensorPair
  simp only [sum_tensor_cons,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- Contraction with a fixed rank-r tensor is bounded by its norm, with
the derivative slot contracted by the same original inverse metric. -/
theorem tensor_inner_gradient_sq_le (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A : CovTensor n r) (T : CovTensor n (r+1)) :
    (∑ i, ∑ j, G⁻¹ i j*covTensorPair G A (fun v => T (Fin.cons i v))*
      covTensorPair G A (fun v => T (Fin.cons j v))) ≤
      covTensorNormSq G A*covTensorNormSq G T := by
  let N := covTensorNormSq G A
  let P := fun i => covTensorPair G A (fun v => T (Fin.cons i v))
  have hN : 0 ≤ N := covTensorNormSq_nonneg G hG A
  by_cases hNzero : N=0
  · have hp (i : RIdx n) : P i=0 := by
      have hh := covTensorPair_sq_le G hG A (fun v => T (Fin.cons i v))
      change P i^2 ≤ N*_ at hh
      rw [hNzero,zero_mul] at hh
      nlinarith
    change (∑ i, ∑ j, G⁻¹ i j*P i*P j) ≤ N*_
    simp only [hp,mul_zero,Finset.sum_const_zero,hNzero,zero_mul,le_refl]
  · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNzero)
    let S : CovTensor n (r+1) := fun v => T v-(P (v 0)/N)*A (fun j => v j.succ)
    have hS := covTensorNormSq_nonneg G hG S
    have hpair (i j : RIdx n) :
        covTensorPair G (fun v => S (Fin.cons i v)) (fun v => S (Fin.cons j v)) =
          covTensorPair G (fun v => T (Fin.cons i v)) (fun v => T (Fin.cons j v)) -
            P i*P j/N := by
      simp only [S,Fin.cons_zero,Fin.cons_succ,covTensorPair_sub_left,
        covTensorPair_sub_right,covTensorPair_mul_left,covTensorPair_mul_right,covTensorPair_self]
      rw [covTensorPair_symm G hG (fun v => T (Fin.cons i v)) A]
      change (covTensorPair G (fun v => T (Fin.cons i v)) (fun v => T (Fin.cons j v))-
        P i/N*P j)-P j/N*(P i-P i/N*N) =
        covTensorPair G (fun v => T (Fin.cons i v)) (fun v => T (Fin.cons j v))-P i*P j/N
      field_simp [hNzero]
      ring
    have hfull : covTensorNormSq G S = covTensorNormSq G T -
        (∑ i, ∑ j, G⁻¹ i j*P i*P j)/N := by
      change covTensorPair G S S = covTensorPair G T T-_
      rw [covTensorPair_succ,covTensorPair_succ]
      simp_rw [hpair]
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_div,mul_div_assoc,mul_assoc]
    rw [hfull] at hS
    change (∑ i, ∑ j, G⁻¹ i j*P i*P j) ≤ N*_
    have hdiv : (∑ i, ∑ j, G⁻¹ i j*P i*P j)/N ≤ covTensorNormSq G T := by linarith
    simpa only [mul_comm] using (div_le_iff₀ hNpos).mp hdiv

variable {M : ComplexManifold n}

theorem chartTensorNormSq_gradient_le (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    L18Aux.chartGradientPair h c
      (fun w => covTensorNormSq (realMetricFn h c w) (A w))
      (fun w => covTensorNormSq (realMetricFn h c w) (A w)) z ≤
      4*covTensorNormSq (realMetricFn h c z) (A z)*
        covTensorNormSq (realMetricFn h c z) (covariantD h c A z) := by
  rw [L18Aux.chartGradientPair_eq_sum]
  simp_rw [rDeriv_covTensorNormSq h hh c A hA hz]
  have hb := tensor_inner_gradient_sq_le (realMetricFn h c z)
    (L12Aux.realMetricFn_posDef h c z hz) (A z) (covariantD h c A z)
  have heq : (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      (2*covTensorPair (realMetricFn h c z) (A z) (fun v => covariantD h c A z (Fin.cons a v)))*
      (2*covTensorPair (realMetricFn h c z) (A z) (fun v => covariantD h c A z (Fin.cons b v)))) =
      4*(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        covTensorPair (realMetricFn h c z) (A z) (fun v => covariantD h c A z (Fin.cons a v))*
        covTensorPair (realMetricFn h c z) (A z) (fun v => covariantD h c A z (Fin.cons b v))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq]
  nlinarith

theorem chartJetSq_gradient_le (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (k : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    L18Aux.chartGradientPair h c
      (fun w => covTensorNormSq (realMetricFn h c w) (rmJet h c k w))
      (fun w => covTensorNormSq (realMetricFn h c w) (rmJet h c k w)) z ≤
      4*covTensorNormSq (realMetricFn h c z) (rmJet h c k z)*
        covTensorNormSq (realMetricFn h c z) (rmJet h c (k+1) z) :=
  chartTensorNormSq_gradient_le h hh c (rmJet h c k)
    (rmJet_contDiffOn h hh c k) hz

end Yau.LeafProofs.L23Aux
