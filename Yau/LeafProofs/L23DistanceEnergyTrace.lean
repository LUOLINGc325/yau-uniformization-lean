import Yau.LeafProofs.L23DistanceEnergyCurvatureForm
import Yau.LeafProofs.L23CurvatureJetSymmetry
import Yau.LeafProofs.L23JetNaturality

/-! The full actual curvature trace in any complete physical orthonormal frame. -/

noncomputable section
open scoped Topology ContDiff Matrix
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem sum_four_swap_pairs {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ k, ∑ j, ∑ l, f i k j l)=∑ j, ∑ l, ∑ i, ∑ k, f i k j l := by
  have hs := Finset.sum_comm (s := (Finset.univ : Finset (ι × ι)))
    (t := (Finset.univ : Finset (ι × ι))) (f := fun p q => f p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type] using hs

theorem bilinear_frame_trace {κ : Type*} [Fintype κ]
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (H : Matrix (RIdx n) (RIdx n) ℝ) (W : κ → ComplexVector n)
    (hW : ∀ i j, ∑ s, realCoord (W s) i*realCoord (W s) j=H i j) :
    (∑ s, B (W s) (W s))=∑ i, ∑ j, H i j*B (realVec i) (realVec j) := by
  have he : (∑ s, B (W s) (W s))=
      ∑ s, ∑ i, ∑ j, realCoord (W s) i*realCoord (W s) j*B (realVec i) (realVec j) :=
    Finset.sum_congr rfl (fun s _ => realBilin_eq_sum B (W s) (W s))
  rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.sum_mul,hW]

def curvaturePairBilin (h : HermitianField M) (c : M.Carrier) (z T : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ)
    ((realMetricInChart h c z).flip T)).comp
      ((connectionCurvatureMap (chartChristoffelBilin h c) z).flip T)

theorem curvaturePairBilin_apply (h : HermitianField M) (c : M.Carrier) (z T u v : ComplexVector n) :
    curvaturePairBilin h c z T u v=
      realMetricInChart h c z (connectionCurvature (chartChristoffelBilin h c) z u T v) T := rfl

theorem curvaturePairBilin_basis (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (T : ComplexVector n) (i k : RIdx n) :
    curvaturePairBilin h c z T (realVec i) (realVec k)=
      ∑ j, ∑ l, realCoord T j*realCoord T l*rmTensor h c z ![i,j,k,l] := by
  rw [curvaturePairBilin_apply,connectionCurvature_pair_eq_sum h hh c hz]
  simp [realCoord_realVec,mul_assoc]

theorem rmTensor_middle_trace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z∈chartTarget c) (j l : RIdx n) :
    (∑ i, ∑ k, (realMetricFn h c z)⁻¹ i k*rmTensor h c z ![i,j,k,l])=
      -realRicciCoeff h c z j l := by
  calc
    _=∑ i, ∑ k, (realMetricFn h c z)⁻¹ i k*(-rmTensor h c z ![i,j,l,k]) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [rmTensor_swap_last h hh c hz i j k l]
    _=_ := by simp only [mul_neg,Finset.sum_neg_distrib]; rfl

theorem connectionCurvature_frame_trace {κ : Type*} [Fintype κ]
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z : ComplexVector n} (hz : z∈chartTarget c) (T : ComplexVector n) (W : κ → ComplexVector n)
    (hW : ∀ i j, ∑ s, realCoord (W s) i*realCoord (W s) j=(realMetricFn h c z)⁻¹ i j) :
    (∑ s, realMetricInChart h c z
      (connectionCurvature (chartChristoffelBilin h c) z (W s) T (W s)) T)=
        -(∑ j, ∑ l, realRicciCoeff h c z j l*realCoord T j*realCoord T l) := by
  change (∑ s, curvaturePairBilin h c z T (W s) (W s))=_
  rw [bilinear_frame_trace _ _ W hW]
  simp only [curvaturePairBilin_basis h hh c hz,Finset.mul_sum]
  rw [sum_four_swap_pairs]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  calc
    _=(∑ i, ∑ k, (realMetricFn h c z)⁻¹ i k*rmTensor h c z ![i,j,k,l])*
        realCoord T j*realCoord T l := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _=_ := by rw [rmTensor_middle_trace h hh c hz]; ring

theorem realMetricInChart_quadratic_eq_matrix (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z∈chartTarget c) (T : ComplexVector n) :
    realMetricInChart h c z T T=realCoord T ⬝ᵥ (realMetricFn h c z *ᵥ realCoord T) := by
  rw [realBilin_eq_sum]
  simp only [realMetricInChart_basis h c z hz,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realRicciCoeff_quadratic_abs_le_of_curvatureBound
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z : ComplexVector n} (hz : z∈chartTarget c) (T : ComplexVector n) (K : ℝ)
    (hK : curvatureJetNorm h 0 (chartInv c z)≤K) :
    |∑ j, ∑ l, realRicciCoeff h c z j l*realCoord T j*realCoord T l|≤
      (2*n : ℕ)*K*realMetricInChart h c z T T := by
  have hb := realRicciCoeff_quadratic_abs_le h c z hz (realCoord T)
  have he : Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmTensor h c z))=
      curvatureJetNorm h 0 (chartInv c z) := by
    change Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmTensor h c z))=
      Real.sqrt (jetSq h 0 (chartInv c z))
    have hjet : jetSq h 0 (chartInv c z)=covTensorNormSq (realMetricFn h c z) (rmTensor h c z) :=
      jetSq_inChart h hh 0 c hz
    exact congrArg Real.sqrt hjet.symm
  rw [he,←realMetricInChart_quadratic_eq_matrix h c hz T] at hb
  have hnonneg : 0≤realMetricInChart h c z T T := by
    rw [realMetricInChart_quadratic_eq_matrix h c hz]
    exact (realMetricFn_posDef h c z hz).posSemidef.dotProduct_mulVec_nonneg _
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)) hnonneg)

end Yau.LeafProofs.L23Aux
