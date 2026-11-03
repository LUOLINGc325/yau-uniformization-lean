import Yau.LeafProofs.L23UpperCurvatureDerivative

/-! Exact contractions that enter the arbitrary-rank Ricci-flow
commutator cancellation. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem weighted_trace_raise_swap {ι : Type*} [Fintype ι]
    (H : ι → ι → ℝ) (K : ι → ℝ) (R : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, H a b*∑ q, K q*R a b q)=
      ∑ q, K q*∑ a, ∑ b, H a b*R a b q := by
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_contract_rmTensor (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i q : RIdx n) :
    realRicciCoeff h c z i q=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*rmTensor h c z ![i,a,b,q] := by
  change (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*rmTensor h c z ![a,i,q,b])=_
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have h1 := rmTensor_swap_first h c z i a b q
  have h2 := rmTensor_swap_last h hh c hz a i b q
  linarith [h1,h2]

theorem riemannCoeff_inverse_trace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i p : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a b p)=
      ∑ q, (realMetricFn h c z)⁻¹ p q*realRicciCoeff h c z i q := by
  simp_rw [riemannCoeff_raise_last h c hz]
  rw [weighted_trace_raise_swap]
  simp_rw [←realRicciCoeff_contract_rmTensor h hh c hz]

theorem upperCurvatureDerivative_inverse_trace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i p k : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*upperCurvatureDerivativeMatrix h c z a i b p k)=
      ∑ q, (realMetricFn h c z)⁻¹ p q*
        (covariantD h c (ricciTensor h c) z ![k,i,q]-
          covariantD h c (ricciTensor h c) z ![q,i,k]) := by
  simp_rw [upperCurvatureDerivative_raise h hh c hz]
  rw [weighted_trace_raise_swap]
  simp_rw [covariantD_rmTensor_contractedBianchi h hh c hz]

end Yau.LeafProofs.L23Aux
