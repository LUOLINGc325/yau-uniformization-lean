import Yau.LeafProofs.L23TensorMetricAlgebra
import Yau.LeafProofs.L23CurvatureCalculus

/-! Spatial differentiation of the actual rank-r metric contraction. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n} {r : ℕ}

theorem rDeriv_prod {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → ComplexVector n → ℝ) {z : ComplexVector n}
    (hf : ∀ j, DifferentiableAt ℝ (f j) z) (i : RIdx n) :
    rDeriv (fun w => ∏ j, f j w) z i =
      ∑ j, rDeriv (f j) z i*∏ k ∈ Finset.univ.erase j, f k z := by
  unfold rDeriv
  rw [fderiv_finsetProd (fun j _ => hf j)]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorContraction_rDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ComplexVector n → Matrix ι ι ℝ)
    (A B : ComplexVector n → (Fin r → ι) → ℝ) {z : ComplexVector n}
    (hH : ∀ a b, DifferentiableAt ℝ (fun w => H w a b) z)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) (i : RIdx n) :
    rDeriv (fun w => tensorContraction (H w) (A w) (B w)) z i =
      tensorContraction (H z) (fun v => rDeriv (fun w => A w v) z i) (B z)+
      tensorContraction (H z) (A z) (fun v => rDeriv (fun w => B w v) z i)+
      tensorMetricVariation (H z) (fun a b => rDeriv (fun w => H w a b) z i) (A z) (B z) := by
  have hprod (v w : Fin r → ι) :=
    (HasFDerivAt.finsetProd (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
      (hH (v j) (w j)).hasFDerivAt)).differentiableAt
  have hterm (v w : Fin r → ι) := ((hA v).mul (hB w)).mul (hprod v w)
  have hinner (v : Fin r → ι) : DifferentiableAt ℝ
      (fun u => ∑ w : Fin r → ι, A u v*B u w*∏ j : Fin r, H u (v j) (w j)) z :=
    DifferentiableAt.fun_sum (fun w _ => hterm v w)
  have htermD (v w : Fin r → ι) :
      rDeriv (fun u => A u v*B u w*∏ j : Fin r, H u (v j) (w j)) z i =
        (rDeriv (fun u => A u v) z i*B z w+A z v*rDeriv (fun u => B u w) z i)*
          (∏ j : Fin r, H z (v j) (w j)) +
        A z v*B z w*(∑ j : Fin r, rDeriv (fun u => H u (v j) (w j)) z i*
          ∏ k ∈ Finset.univ.erase j, H z (v k) (w k)) := by
    rw [rDeriv_mul (f := fun u => A u v*B u w)
      (k := fun u => ∏ j : Fin r, H u (v j) (w j)) ((hA v).mul (hB w)) (hprod v w),
      rDeriv_mul (f := fun u => A u v) (k := fun u => B u w) (hA v) (hB w)]
    rw [rDeriv_prod (fun j u => H u (v j) (w j)) (fun j => hH _ _) i]
  have hinnerD (v : Fin r → ι) := rDeriv_sum
    (fun w u => A u v*B u w*∏ j : Fin r, H u (v j) (w j)) (hterm v) i
  unfold tensorContraction
  rw [rDeriv_sum _ hinner]
  simp_rw [hinnerD,htermD]
  have hvar : (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A z v*B z w*(∑ j : Fin r, rDeriv (fun u => H u (v j) (w j)) z i*
        ∏ k ∈ Finset.univ.erase j, H z (v k) (w k))) =
        tensorMetricVariation (H z) (fun a b => rDeriv (fun w => H w a b) z i) (A z) (B z) := by
    simp only [Finset.mul_sum,tensorMetricVariation]
    conv_lhs =>
      arg 2
      ext v
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1
    funext j
    congr 1
    funext v
    congr 1
    funext w
    ring
  simp only [add_mul,mul_add,Finset.sum_add_distrib]
  rw [hvar]

/-- Every inverse-metric derivative is included; the result is the
covariant derivative of the original tensor, not a coordinate derivative. -/
theorem rDeriv_covTensorNormSq (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) :
    rDeriv (fun w => covTensorNormSq (realMetricFn h c w) (A w)) z i =
      2*covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c A z (Fin.cons i v)) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hInv (a b : RIdx n) :=
    ((realMetricFn_inverse_contDiffOn h hh c a b).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAdiff (v : Fin r → RIdx n) :=
    ((hA v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  let H := (realMetricFn h c z)⁻¹
  let D := L12Aux.connectionMatrix h c z i
  have hHsym : H.IsSymm := (L18Aux.realMetricFn_isSymm h c z).inv
  have hdot : (fun a b => rDeriv (fun w => (realMetricFn h c w)⁻¹ a b) z i) =
      -(D*H+H*Dᵀ) := inverseMetric_directional_derivative h hh c hz i
  have hd := tensorContraction_rDeriv (fun w => (realMetricFn h c w)⁻¹) A A
    hInv hAdiff hAdiff i
  rw [hdot,tensorMetricVariation_connection _ _ hHsym] at hd
  have hsym := tensorContraction_symm H hHsym (A z)
    (fun v => rDeriv (fun w => A w v) z i)
  change rDeriv (fun w => tensorContraction (realMetricFn h c w)⁻¹ (A w) (A w)) z i =
    2*tensorContraction H (A z) (fun v => covariantD h c A z (Fin.cons i v))
  rw [tensorContraction_symm H hHsym (A z)]
  simp_rw [covariantD_cons]
  rw [tensorContraction_sub_left]
  dsimp only [H,D] at hsym ⊢
  linarith [hd,hsym]

theorem rDeriv_covTensorPair (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A B : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) :
    rDeriv (fun w => covTensorPair (realMetricFn h c w) (A w) (B w)) z i =
      covTensorPair (realMetricFn h c z)
        (fun v => covariantD h c A z (Fin.cons i v)) (B z)+
      covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c B z (Fin.cons i v)) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hInv (a b : RIdx n) :=
    ((realMetricFn_inverse_contDiffOn h hh c a b).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAdiff (v : Fin r → RIdx n) :=
    ((hA v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hBdiff (v : Fin r → RIdx n) :=
    ((hB v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  let H := (realMetricFn h c z)⁻¹
  let D := L12Aux.connectionMatrix h c z i
  have hHsym : H.IsSymm := (L18Aux.realMetricFn_isSymm h c z).inv
  have hdot : (fun a b => rDeriv (fun w => (realMetricFn h c w)⁻¹ a b) z i) =
      -(D*H+H*Dᵀ) := inverseMetric_directional_derivative h hh c hz i
  have hd := tensorContraction_rDeriv (fun w => (realMetricFn h c w)⁻¹) A B
    hInv hAdiff hBdiff i
  rw [hdot,tensorMetricVariation_connection_pair _ _ hHsym] at hd
  change rDeriv (fun w => tensorContraction (realMetricFn h c w)⁻¹ (A w) (B w)) z i =
    tensorContraction H (fun v => covariantD h c A z (Fin.cons i v)) (B z)+
      tensorContraction H (A z) (fun v => covariantD h c B z (Fin.cons i v))
  simp_rw [covariantD_cons]
  rw [tensorContraction_sub_left,tensorContraction_sub_right]
  dsimp only [H,D] at hd ⊢
  linarith [hd]

end Yau.LeafProofs.L23Aux
