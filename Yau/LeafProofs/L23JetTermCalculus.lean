import Yau.LeafProofs.L23ContractionWordCalculus
import Yau.LeafProofs.L23ContractionWordNorm
import Yau.LeafProofs.L23TensorNormLinear

/-! Actual finite jet terms and their differentiation and norm estimates. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {M : ComplexManifold n}

def jetConvolution (h : HermitianField M) (c : M.Carrier) (k : ℕ) (z : ComplexVector n) : ℝ :=
  ∑ i : Fin (k+1), Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c i.val z))*
    Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c (k-i.val) z))

theorem jetConvolution_nonneg (h : HermitianField M) (c : M.Carrier) (k : ℕ) (z : ComplexVector n) :
    0 ≤ jetConvolution h c k z :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

namespace JetTerm

def eval (e : JetTerm k) (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : CovTensor n (4+k) :=
  fun v => e.coeff.toReal*e.word.eval (realMetricFn h c z)⁻¹
    (rmJet h c e.leftOrder z) (rmJet h c e.rightOrder z) v

theorem eval_contDiffOn (e : JetTerm k) (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (v : Fin (4+k) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => e.eval h c z v) (chartTarget c) :=
  contDiffOn_const.mul (e.word.eval_contDiffOn h hh c _ _
    (rmJet_contDiffOn h hh c e.leftOrder) (rmJet_contDiffOn h hh c e.rightOrder) v)

theorem covariantD_eval (e : JetTerm k) (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    covariantD h c (e.eval h c) z (Fin.cons i v)=
      e.dLeft.eval h c z (Fin.cons i v)+e.dRight.eval h c z (Fin.cons i v) := by
  have hW (u : Fin (4+k) → RIdx n) := ((e.word.eval_contDiffOn h hh c _ _
    (rmJet_contDiffOn h hh c e.leftOrder) (rmJet_contDiffOn h hh c e.rightOrder) u).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  change covariantD h c (fun w v => e.coeff.toReal*
    e.word.eval (realMetricFn h c w)⁻¹ (rmJet h c e.leftOrder w) (rmJet h c e.rightOrder w) v)
      z (Fin.cons i v)=_
  rw [covariantD_const_mul_at h c _ z hW]
  change e.coeff.toReal*covariantD h c
    (fun w => e.word.eval (realMetricFn h c w)⁻¹ (rmJet h c e.leftOrder w) (rmJet h c e.rightOrder w))
      z (Fin.cons i v)=_
  rw [e.word.covariantD_eval h hh c _ _
    (rmJet_contDiffOn h hh c e.leftOrder) (rmJet_contDiffOn h hh c e.rightOrder) hz]
  change e.coeff.toReal*(_+_)=e.coeff.toReal*_+e.coeff.toReal*_
  dsimp only [dLeft,dRight,rmJet]
  ring

theorem eval_norm_le (e : JetTerm k) (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    Real.sqrt (covTensorNormSq (realMetricFn h c z) (e.eval h c z)) ≤
      (2*n : ℕ)*Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c e.leftOrder z))*
        Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c e.rightOrder z)) := by
  change Real.sqrt (covTensorNormSq (realMetricFn h c z) (fun v => e.coeff.toReal*
    e.word.eval (realMetricFn h c z)⁻¹ (rmJet h c e.leftOrder z) (rmJet h c e.rightOrder z) v))≤_
  rw [sqrt_covTensorNormSq_const_mul]
  calc
    _≤1*Real.sqrt (covTensorNormSq (realMetricFn h c z)
        (e.word.eval (realMetricFn h c z)⁻¹ (rmJet h c e.leftOrder z) (rmJet h c e.rightOrder z))) :=
      mul_le_mul_of_nonneg_right e.coeff.abs_toReal_le_one (Real.sqrt_nonneg _)
    _≤_ := by
      rw [one_mul]
      exact e.word.eval_norm_le _ (L12Aux.realMetricFn_posDef h c z hz) _ _

theorem eval_norm_le_convolution (e : JetTerm k) (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    Real.sqrt (covTensorNormSq (realMetricFn h c z) (e.eval h c z)) ≤
      (2*n : ℕ)*jetConvolution h c k z := by
  have htotal := e.total
  have hi : e.leftOrder<k+1 := by omega
  have hr : e.rightOrder=k-e.leftOrder := by omega
  let j : Fin (k+1) := ⟨e.leftOrder,hi⟩
  have hsingle :
      Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c e.leftOrder z))*
        Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c e.rightOrder z))≤
          jetConvolution h c k z := by
    unfold jetConvolution
    rw [hr]
    exact Finset.single_le_sum (f := fun i : Fin (k+1) =>
      Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c i.val z))*
        Real.sqrt (covTensorNormSq (realMetricFn h c z) (rmJet h c (k-i.val) z)))
      (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ j)
  exact (eval_norm_le e h c hz).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg _))

end JetTerm

end Yau.LeafProofs.L23Aux
