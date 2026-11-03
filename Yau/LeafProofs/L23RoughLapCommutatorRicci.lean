import Yau.LeafProofs.L23TensorFlowCommutator
import Yau.LeafProofs.L23RicciCurvatureContractions

/-! The all-rank spatial commutator after the exact Ricci contractions. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem covariantD_roughLap_commutator_ricci (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (roughLap h c A) z (Fin.cons i v)-
      roughLap h c (covariantD h c A) z (Fin.cons i v)=
      -(∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*realRicciCoeff h c z i q*
        covariantD h c A z (Fin.cons p v))-
      2*(∑ a, ∑ b, ∑ s : Fin r, ∑ p,
        (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a (v s) p*
          covariantD h c A z (Fin.cons b (Function.update v s p)))-
      (∑ s : Fin r, ∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*
        (covariantD h c (ricciTensor h c) z ![v s,i,q]-
          covariantD h c (ricciTensor h c) z ![q,i,v s])*A z (Function.update v s p)) := by
  have h1 : (∑ a, ∑ b, ∑ p, (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a b p*
      covariantD h c A z (Fin.cons p v))=
      ∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*realRicciCoeff h c z i q*
        covariantD h c A z (Fin.cons p v) := by
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    calc
      _=(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*riemannCoeff h c z i a b p)*
          covariantD h c A z (Fin.cons p v) := by simp only [Finset.sum_mul]
      _=_ := by rw [riemannCoeff_inverse_trace h hh c hz,Finset.sum_mul]
  have h3 : (∑ a, ∑ b, ∑ s : Fin r, ∑ p,
      (realMetricFn h c z)⁻¹ a b*upperCurvatureDerivativeMatrix h c z a i b p (v s)*
        A z (Function.update v s p))=
      ∑ s : Fin r, ∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*
        (covariantD h c (ricciTensor h c) z ![v s,i,q]-
          covariantD h c (ricciTensor h c) z ![q,i,v s])*A z (Function.update v s p) := by
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext s
      arg 2
      ext a
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext s
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro p _
    calc
      _=(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
          upperCurvatureDerivativeMatrix h c z a i b p (v s))*A z (Function.update v s p) := by
        simp only [Finset.sum_mul]
      _=_ := by rw [upperCurvatureDerivative_inverse_trace h hh c hz,Finset.sum_mul]
  rw [covariantD_roughLap_commutator_upper h hh c A hA hz,h1,h3]

end Yau.LeafProofs.L23Aux
