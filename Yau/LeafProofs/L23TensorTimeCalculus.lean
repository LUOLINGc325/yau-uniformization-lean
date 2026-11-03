import Yau.LeafProofs.L23TensorKato
import Yau.LeafProofs.L23MetricTimeCalculus

/-! Actual time differentiation includes every inverse-metric factor. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem tensorContraction_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (H : ℝ → Matrix ι ι ℝ) (J : Matrix ι ι ℝ)
    (A B : ℝ → (Fin r → ι) → ℝ) (A' B' : (Fin r → ι) → ℝ) (t : ℝ)
    (hH : ∀ a b, HasDerivAt (fun s => H s a b) (J a b) t)
    (hA : ∀ v, HasDerivAt (fun s => A s v) (A' v) t)
    (hB : ∀ v, HasDerivAt (fun s => B s v) (B' v) t) :
    HasDerivAt (fun s => tensorContraction (H s) (A s) (B s))
      (tensorContraction (H t) A' (B t)+tensorContraction (H t) (A t) B'+
        tensorMetricVariation (H t) J (A t) (B t)) t := by
  have hprod (v w : Fin r → ι) := HasDerivAt.fun_finsetProd
    (u := (Finset.univ : Finset (Fin r))) (fun j _ => hH (v j) (w j))
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin r → ι))) (fun v _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin r → ι))) (fun w _ =>
      ((hA v).mul (hB w)).mul (hprod v w)))
  have hvar : (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A t v*B t w*(∑ j : Fin r,
        (∏ k ∈ Finset.univ.erase j, H t (v k) (w k))*J (v j) (w j))) =
      tensorMetricVariation (H t) J (A t) (B t) := by
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
  convert hsum using 1
  · funext s
    simp only [tensorContraction,Finset.sum_fn,Pi.mul_apply]
  · symm
    simp only [tensorContraction,smul_eq_mul,Pi.mul_apply,add_mul,Finset.sum_add_distrib]
    rw [hvar]

variable {n r : ℕ} {M : ComplexManifold n}

theorem localRealRicciFlow_covTensorNormSq_hasDerivAt
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (A : ℝ → CovTensor n r) (A' : CovTensor n r)
    (hA : ∀ v, HasDerivAt (fun s => A s v) (A' v) t) :
    HasDerivAt (fun s => covTensorNormSq (realMetricFn (h s) x (chartPt x x)) (A s))
      (2*covTensorPair (realMetricFn (h t) x (chartPt x x)) A' (A t)+
        tensorMetricVariation (realMetricFn (h t) x (chartPt x x))⁻¹
          (fun i j => σ*∑ k, ∑ l, (realMetricFn (h t) x (chartPt x x))⁻¹ i k*
            realRicciCoeff (h t) x (chartPt x x) k l*
              (realMetricFn (h t) x (chartPt x x))⁻¹ l j) (A t) (A t)) t := by
  have hd := tensorContraction_hasDerivAt
    (fun s => (realMetricFn (h s) x (chartPt x x))⁻¹)
    (fun i j => σ*∑ k, ∑ l, (realMetricFn (h t) x (chartPt x x))⁻¹ i k*
      realRicciCoeff (h t) x (chartPt x x) k l*
        (realMetricFn (h t) x (chartPt x x))⁻¹ l j)
    A A A' A' t
    (localRealRicciFlow_inverseMetric_hasDerivAt h O a b σ hflow x hx t ht) hA hA
  change HasDerivAt (fun s => covTensorNormSq (realMetricFn (h s) x (chartPt x x)) (A s))
    (covTensorPair (realMetricFn (h t) x (chartPt x x)) A' (A t)+
      covTensorPair (realMetricFn (h t) x (chartPt x x)) (A t) A'+_) t at hd
  have hsym := covTensorPair_symm (realMetricFn (h t) x (chartPt x x))
    (L12Aux.realMetricFn_posDef (h t) x _ (mem_extChartAt_target x)) (A t) A'
  convert hd using 1
  linarith [hsym]

end Yau.LeafProofs.L23Aux
