import Yau.LeafProofs.L23TensorAlgebra

/-! Time derivatives of the actual inverse metric. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux

theorem matrixInverse_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (B : Matrix ι ι ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (B i j) t)
    (hdet : (A t).det ≠ 0) (i j : ι) :
    HasDerivAt (fun s => (A s)⁻¹ i j) ((-(A t)⁻¹*B*(A t)⁻¹) i j) t := by
  have hD : L12Aux.matrixDirectionalDerivative A t (1 : ℝ) = B := by
    ext k l
    exact (hA k l).deriv
  have hd := L12Aux.matrixDirectionalDerivative_inv
    (fun k l => (hA k l).differentiableAt) hdet (1 : ℝ)
  rw [hD] at hd
  have heq := congrArg (fun C : Matrix ι ι ℝ => C i j) hd
  have hdiff := L12Aux.matrixInverse_entries_differentiableAt
    (fun k l => (hA k l).differentiableAt) hdet i j
  change deriv (fun s => (A s)⁻¹ i j) t = _ at heq
  have hh := hdiff.hasDerivAt
  rw [heq] at hh
  convert hh using 1 <;> simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg]

variable {n : ℕ} {M : ComplexManifold n}

theorem localRealRicciFlow_metric_hasDerivAt
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (i j : RIdx n) :
    HasDerivAt (fun s => realMetricFn (h s) x (chartPt x x) i j)
      (-σ*realRicciCoeff (h t) x (chartPt x x) i j) t :=
  (hflow.2 x hx t ⟨ht.1.le,ht.2.le⟩ i j).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem localRealRicciFlow_inverseMetric_hasDerivAt
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (i j : RIdx n) :
    HasDerivAt (fun s => (realMetricFn (h s) x (chartPt x x))⁻¹ i j)
      (σ*∑ k, ∑ l, (realMetricFn (h t) x (chartPt x x))⁻¹ i k *
        realRicciCoeff (h t) x (chartPt x x) k l *
          (realMetricFn (h t) x (chartPt x x))⁻¹ l j) t := by
  have hh := matrixInverse_hasDerivAt
    (fun s => realMetricFn (h s) x (chartPt x x))
    (fun k l => -σ*realRicciCoeff (h t) x (chartPt x x) k l) t
    (localRealRicciFlow_metric_hasDerivAt h O a b σ hflow x hx t ht)
    (L12Aux.realMetricFn_posDef (h t) x _ (mem_extChartAt_target x)).det_pos.ne' i j
  convert hh using 1
  change (σ*∑ k, ∑ l, (realMetricFn (h t) x (chartPt x x))⁻¹ i k *
      realRicciCoeff (h t) x (chartPt x x) k l *
        (realMetricFn (h t) x (chartPt x x))⁻¹ l j) =
    ∑ l, (∑ k, -(realMetricFn (h t) x (chartPt x x))⁻¹ i k *
      (-σ*realRicciCoeff (h t) x (chartPt x x) k l))*
        (realMetricFn (h t) x (chartPt x x))⁻¹ l j
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Yau.LeafProofs.L23Aux
