import Yau.Proofs.F03GradientAlgebra
import Yau.Proofs.F03DyadicConvexBudget

/-! Actual local finite sums give the physical gradient formula for dyadic gluing. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem sqrt_gradNormSq_congr_of_eventuallyEq (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier)
    (hEq : f =ᶠ[𝓝 x] q) :
    Real.sqrt (gradNormSq g f x)=Real.sqrt (gradNormSq g q x) := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hInv : ContinuousAt (chartInv x) (chartPt x x) :=
    continuousAt_extChartAt_symm'' (mem_extChartAt_target x)
  have hLim : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
    simpa only [hinv] using hInv.tendsto
  have hChart : inChart x f =ᶠ[𝓝 (chartPt x x)] inChart x q := hLim.eventually hEq
  rw [sqrt_gradNormSq_eq_physicalCovector g hf,sqrt_gradNormSq_eq_physicalCovector g hq]
  unfold physicalCovector
  rw [hChart.fderiv_eq]

theorem dyadicGluing_local_finite_partition (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (F : ℕ → M.Carrier → ℝ → ℝ) (x : M.Carrier) (hx : 1 ≤ u x) (t : ℝ) :
    ∃ N : ℕ,(∑ j ∈ Finset.range (N+1),dyadicPartition j (u x))=1 ∧
      (fun y => dyadicGluing u F y t) =ᶠ[𝓝 x]
        (fun y => ∑ j ∈ Finset.range (N+1),dyadicPartition j (u y)*F j y t) := by
  obtain ⟨q,_hq,hq'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 2)
  refine ⟨q+1,dyadicPartition_sum_one hq'.le,?_⟩
  filter_upwards [(continuous_of_smoothFn hu).continuousAt.eventually (Iio_mem_nhds hq')] with y hy
  apply dyadicGluing_eq_sum_of_tail
  intro j hj
  cases j with
  | zero => omega
  | succ j =>
    apply dyadicPartition_succ_zero_below
    exact hy.le.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))

theorem dyadicGluing_gradient_finite_bound (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,1 ≤ u x)
    (F : ℕ → M.Carrier → ℝ → ℝ) (t : ℝ) (hF : ∀ j,SmoothFn (fun y => F j y t))
    (hGlued : SmoothFn (fun y => dyadicGluing u F y t)) (x : M.Carrier) :
    ∃ N : ℕ,(∑ j ∈ Finset.range (N+1),dyadicPartition j (u x))=1 ∧
      Real.sqrt (gradNormSq g (fun y => dyadicGluing u F y t) x) ≤
        ∑ j ∈ Finset.range (N+1),
          (dyadicPartition j (u x)*Real.sqrt (gradNormSq g (fun y => F j y t) x)+
            |deriv (dyadicPartition j) (u x)| * |F j x t| * Real.sqrt (gradNormSq g u x)) := by
  obtain ⟨N,hN,hEq⟩ := dyadicGluing_local_finite_partition u hu F x (hu0 x) t
  have hProfile (j : ℕ) : SmoothFn (fun y => dyadicPartition j (u y)) :=
    fun a => (dyadicPartition_contDiff j).comp_contDiffOn (hu a)
  have hProd (j : ℕ) : SmoothFn (fun y => dyadicPartition j (u y)*F j y t) :=
    fun a => (hProfile j a).mul (hF j a)
  have hSum : SmoothFn (fun y => ∑ j ∈ Finset.range (N+1),dyadicPartition j (u y)*F j y t) :=
    fun a => ContDiffOn.sum (fun j _ => hProd j a)
  refine ⟨N,hN,?_⟩
  rw [sqrt_gradNormSq_congr_of_eventuallyEq g hGlued hSum x hEq]
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1),Real.sqrt
        (gradNormSq g (fun y => dyadicPartition j (u y)*F j y t) x) :=
      sqrt_gradNormSq_sum_le g _ _ (fun j _ => hProd j) x
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      have hh := sqrt_gradNormSq_mul_le g (hProfile j) (hF j) x
      rw [sqrt_gradNormSq_scalar_comp g hu (dyadicPartition j) (dyadicPartition_contDiff j) x,
        abs_of_nonneg (dyadicPartition_nonnegative j (zero_le_one.trans (hu0 x)))] at hh
      convert hh using 1 <;> ring

end Yau.Proofs.F03Aux
