import Yau.LeafProofs.L17PotentialMetricNaturality

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance metricMatrixPositivityTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

theorem undo_matrix_congruence {n : ℕ} (H J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : IsUnit J.det) : J⁻¹ᴴ*(Jᴴ*H*J)*J⁻¹=H := by
  calc
    _ = (J*J⁻¹)ᴴ*H*(J*J⁻¹) := by rw [Matrix.conjTranspose_mul]; noncomm_ring
    _ = H := by rw [Matrix.mul_nonsing_inv J hJ]; simp only [Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]

theorem posDef_of_matrix_congruence {n : ℕ} {H J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.det≠0) (hH : (Jᴴ*H*J).PosDef) : H.PosDef := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hi : Function.Injective (J⁻¹).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (Matrix.isUnit_nonsing_inv_det J hu).ne_zero
  have h := hH.conjTranspose_mul_mul_same hi
  rw [undo_matrix_congruence H J hu] at h
  exact h

theorem posSemidef_of_matrix_congruence {n : ℕ} {H J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.det≠0) (hH : (Jᴴ*H*J).PosSemidef) : H.PosSemidef := by
  have h := hH.conjTranspose_mul_mul_same J⁻¹
  rw [undo_matrix_congruence H J (isUnit_iff_ne_zero.mpr hJ)] at h
  exact h

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ} {hT : 0<T}

theorem potentialMetricMatrix_comparison (hg : MetricSmooth g)
    (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (q : Cylinder M T) :
    (potentialMetricMatrix u q).PosDef ∧
      (potentialMetricMatrix u q-(1/2 : ℂ) • gMat g q.1).PosSemidef ∧
      ((2 : ℂ) • gMat g q.1-potentialMetricMatrix u q).PosSemidef := by
  obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
  let r : LocalCylinder P T := ⟨p,(z,q.2)⟩
  let e := P.charts.chart p
  let x : M.Carrier := e z
  let J := linearMatrix (coordinateDifferential e x z)
  have hz : (z : ComplexVector n)∈e.source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hJ : J.det≠0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e (P.charts.differentiable p)
      (P.charts.inverse_differentiable p) x hz (mem_extChartAt_source x))
  have hrq : chartPoint P T r.1 r.2=q := Prod.ext hzx rfl
  have hG : pullbackMatrix g e z=Jᴴ*gMat g q.1*J := by
    have he := pullbackMatrix_eq_congruence g e x z (mem_extChartAt_source x)
    have heG : pullbackMatrix g e z=Jᴴ*gMat g x*J := he
    simpa only [show x=q.1 from hzx] using heG
  have hNat : pullbackMatrix g e z+coordinateMetricError u r=Jᴴ*potentialMetricMatrix u q*J := by
    simpa only [hrq] using coordinateMetricMatrix_eq_congruence hg u r
  obtain ⟨hPos,hLo,hHi⟩ := coordinateMetric_half_double u hSmall r
  have hLo' : (Jᴴ*(potentialMetricMatrix u q-(1/2 : ℂ) • gMat g q.1)*J).PosSemidef := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,←hNat,←hG]
    exact hLo
  have hHi' : (Jᴴ*((2 : ℂ) • gMat g q.1-potentialMetricMatrix u q)*J).PosSemidef := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,←hNat,←hG]
    exact hHi
  exact ⟨posDef_of_matrix_congruence hJ (hNat ▸ hPos),
    posSemidef_of_matrix_congruence hJ hLo',posSemidef_of_matrix_congruence hJ hHi'⟩

theorem potentialMetricMatrix_initial (u : SchauderSpace P T γ hT) (x : M.Carrier) :
    potentialMetricMatrix u (x,⟨0,⟨le_refl 0,hT.le⟩⟩)=gMat g x := by
  have hU : (fun y => schauderFun u (y,⟨0,⟨le_refl 0,hT.le⟩⟩))=fun _ => (0:ℝ) :=
    funext (schauderFun_initial u)
  have h0 : levi (fun _ : M.Carrier => (0:ℝ)) x=0 := by
    change leviC (fun _ : ComplexVector n => (0:ℝ)) (chartPt x x)=0
    exact leviC_const 0 (chartPt x x)
  simp only [potentialMetricMatrix,hU,h0,Complex.ofReal_zero,zero_smul,sub_zero,add_zero]

end Yau.LeafProofs.L17Aux
