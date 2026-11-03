import Yau.LeafProofs.L21WeightedDomainsMaximal
import Yau.LeafProofs.L21ScaledComplex

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedTPrincipal (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (j : Fin n) (_ : Unit) (a : Yau.RIdx n) (x : X n) : ℂ :=
  (rho x : ℂ)*dbarRealCoefficient A j a x

def weightedSPrincipal (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (r : Fin n × Fin n) (k : Fin n) (a : Yau.RIdx n) (x : X n) : ℂ :=
  (rho x : ℂ)*((if k = r.2 then dbarRealCoefficient A r.1 a x else 0)-
    (if k = r.1 then dbarRealCoefficient A r.2 a x else 0))

def weightedSZeroOrder (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (r : Fin n × Fin n) (k : Fin n) (x : X n) : ℂ :=
  (if k = r.1 then dbarA A r.2 (fun y => (rho y : ℂ)) x else 0)-
    (if k = r.2 then dbarA A r.1 (fun y => (rho y : ℂ)) x else 0)

def weightedTstarPrincipal (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (_ : Unit) (j : Fin n) (a : Yau.RIdx n) (x : X n) : ℂ :=
  -(rho x : ℂ)*star (dbarRealCoefficient A j a x)

def weightedTstarZeroOrder (K : ℝ) (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (_ : Unit) (j : Fin n) (x : X n) : ℂ :=
  (rho x : ℂ)*(conjugateD A j (fun y => (boundaryWeight K y : ℂ)) x-conjugateDivergence A j x)-
    conjugateD A j (fun y => (rho y : ℂ)) x

theorem weightedTPrincipal_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (j : Fin n) (c : Unit) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (weightedTPrincipal A j c a) (Metric.ball 0 1) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn.mul (dbarRealCoefficient_smoothOn hA j a)

theorem weightedSPrincipal_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (r : Fin n × Fin n) (k : Fin n) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (weightedSPrincipal A r k a) (Metric.ball 0 1) := by
  apply (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn.mul
  apply ContDiffOn.sub
  · split_ifs <;> first | exact dbarRealCoefficient_smoothOn hA _ _ | exact contDiffOn_const
  · split_ifs <;> first | exact dbarRealCoefficient_smoothOn hA _ _ | exact contDiffOn_const

theorem weightedSZeroOrder_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (r : Fin n × Fin n) (k : Fin n) :
    ContDiffOn ℝ ∞ (weightedSZeroOrder A r k) (Metric.ball 0 1) := by
  have hd (i : Fin n) := contDiffOn_dbarA Metric.isOpen_ball hA i
    (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn
  apply ContDiffOn.sub
  · split_ifs <;> first | exact hd _ | exact contDiffOn_const
  · split_ifs <;> first | exact hd _ | exact contDiffOn_const

theorem weightedTstarPrincipal_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (c : Unit) (j : Fin n) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (weightedTstarPrincipal A c j a) (Metric.ball 0 1) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn.neg.mul
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA j a))

theorem weightedDomains_conjugateD_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    {f : X n → ℂ} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 1)) (j : Fin n) :
    ContDiffOn ℝ ∞ (conjugateD A j f) (Metric.ball 0 1) :=
  contDiffOn_real_row_sum Metric.isOpen_ball Yau.realVec _
    (fun a => (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA j a)) hf

theorem weightedTstarZeroOrder_smooth (K : ℝ)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (c : Unit) (j : Fin n) :
    ContDiffOn ℝ ∞ (weightedTstarZeroOrder K A c j) (Metric.ball 0 1) := by
  have hdiv : ContDiffOn ℝ ∞ (conjugateDivergence A j) (Metric.ball 0 1) :=
    ContDiffOn.sum fun a _ =>
      (((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA j a)).fderiv_of_isOpen
        Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  exact ((Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn.mul
    ((weightedDomains_conjugateD_smooth hA
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_boundaryWeight K)) j).sub hdiv)).sub
    (weightedDomains_conjugateD_smooth hA (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffOn j)

/-- The actual maximal weak rho-scaled scalar graph operator. -/
def weightedMaximalT (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    WeightedScalar n K →ₗ.[ℂ] WeightedOneForm n K :=
  weightedMaximalRows K hK (fun _ : Unit => ContinuousLinearMap.id ℂ (WeightedScalar n K))
    (weightedFieldProjection K) Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
    (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const)

/-- The actual maximal weak scaled curl, with all ordered pairs. -/
def weightedMaximalS (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    WeightedOneForm n K →ₗ.[ℂ] WeightedTwoForm n K :=
  weightedMaximalRows K hK (weightedFieldProjection K) (weightedFieldProjection K) Yau.realVec
    (weightedSPrincipal A) (weightedSZeroOrder A) (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA)

/-- The maximal distribution realization of the literal weighted formal
adjoint. Its zero order need not be bounded near the true boundary. -/
def weightedMaximalFormalTstar (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    WeightedOneForm n K →ₗ.[ℂ] WeightedScalar n K :=
  weightedMaximalRows K hK (weightedFieldProjection K)
    (fun _ : Unit => ContinuousLinearMap.id ℂ (WeightedScalar n K)) Yau.realVec
    (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
    (weightedTstarPrincipal_smooth hA) (weightedTstarZeroOrder_smooth K hA)

theorem weightedMaximalT_isClosed (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    (weightedMaximalT K hK A hA).IsClosed := by
  unfold weightedMaximalT
  apply weightedMaximalRows_isClosed
  exact weightedField_eq_zero_of_projections K

theorem weightedMaximalS_isClosed (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    (weightedMaximalS K hK A hA).IsClosed := by
  unfold weightedMaximalS
  apply weightedMaximalRows_isClosed
  exact weightedField_eq_zero_of_projections K

theorem weightedMaximalFormalTstar_isClosed (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    (weightedMaximalFormalTstar K hK A hA).IsClosed := by
  unfold weightedMaximalFormalTstar
  apply weightedMaximalRows_isClosed
  intro y hy
  exact hy ()

end Yau.LeafProofs.L21Aux
