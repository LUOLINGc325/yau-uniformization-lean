import Yau.Proofs.F03ClassicalCaloricEnergy

/-! The actual smooth nondivergence operator equals its computed divergence form. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem local_joint_spatial_hessian {D : Set (Point d)} (hD : IsOpen D)
    {v : Point d → ℝ} (hv : ContDiffOn ℝ ∞ v D) (p : Point d) (hp : p ∈ D) (i j : RIdx d) :
    fderiv ℝ (fun q => fderiv ℝ v q (realVec j,0)) p (realVec i,0)=
      spatialDD v p (realVec i) (realVec j) := by
  have hDj : ContDiffOn ℝ ∞ (fun q => fderiv ℝ v q (realVec j,0)) D :=
    (hv.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  rw [← d_eq_joint_fderiv ((hDj.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)) i]
  have hSlice : (fun x : Space d => fderiv ℝ v (x,p.2) (realVec j,0)) =ᶠ[𝓝 p.1]
      (fun x => fderiv ℝ (fun y => v (y,p.2)) x (realVec j)) := by
    filter_upwards [((continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hD.mem_nhds hp))] with x hx
    exact (d_eq_joint_fderiv ((hv.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)) j).symm
  unfold Parabolic.d
  rw [hSlice.fderiv_eq]
  unfold spatialDD
  apply fderiv_clm_const_eval
  have hvSlice : ContDiffAt ℝ ∞ (fun x : Space d => v (x,p.2)) p.1 :=
    (hv.contDiffAt (hD.mem_nhds hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  exact (hvSlice.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)

theorem classicalCaloric_flux_derivative {D : Set (Point d)} (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v D) (p : Point d) (hp : p ∈ D) (i : RIdx d) :
    fderiv ℝ (fun q => energyFlux a (classicalCaloricGradient v) q i) p (realVec i,0)=
      ∑ j, (Parabolic.d (fun x => a (x,p.2) i j) p.1 i*classicalCaloricGradient v p j+
        a p i j*spatialDD v p (realVec i) (realVec j)) := by
  have hA (j : RIdx d) : DifferentiableAt ℝ (fun q => a q i j) p :=
    (((matrixEntryCLM i j).contDiff.comp_contDiffOn hAB.1).contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have hGcont (j : RIdx d) : ContDiffOn ℝ ∞ (fun q => classicalCaloricGradient v q j) D :=
    (hv.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  have hG (j : RIdx d) : DifferentiableAt ℝ (fun q => classicalCaloricGradient v q j) p :=
    ((hGcont j).contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have hDiff (j : RIdx d) (_ : j ∈ Finset.univ) :
      DifferentiableAt ℝ (fun q : Point d => a q i j*classicalCaloricGradient v q j) p :=
    (hA j).mul (hG j)
  change fderiv ℝ (fun q => ∑ j,a q i j*classicalCaloricGradient v q j) p (realVec i,0)=_
  rw [fderiv_fun_sum hDiff]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (hA j) (hG j)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have hCoeff : fderiv ℝ (fun q => a q i j) p (realVec i,0)=
      Parabolic.d (fun x => a (x,p.2) i j) p.1 i := (d_eq_joint_fderiv (hA j) i).symm
  change a p i j*fderiv ℝ (fun q => fderiv ℝ v q (realVec j,0)) p (realVec i,0)+
    classicalCaloricGradient v p j*fderiv ℝ (fun q => a q i j) p (realVec i,0)=_
  rw [hCoeff,local_joint_spatial_hessian hD hv p hp i j]
  ring

theorem classicalCaloric_operator_divergence {D : Set (Point d)} (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v D) (p : Point d) (hp : p ∈ D) :
    fderiv ℝ v p (0,1)-
      (∑ i,fderiv ℝ (fun q => energyFlux a (classicalCaloricGradient v) q i) p (realVec i,0))-
      (∑ j,energyDrift a b p j*classicalCaloricGradient v p j)=linearOp D a b v p := by
  have hFlux := classicalCaloric_flux_derivative hD a b hAB v hv p hp
  have hSpatial (i : RIdx d) : classicalCaloricGradient v p i=spatialD v p (realVec i) :=
    (d_eq_joint_fderiv ((hv.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)) i).symm
  have hTime : fderiv ℝ v p (0,1)=deriv (fun t => v (p.1,t)) p.2 :=
    (test_timeDerivative_eq_joint_fderiv ((hv.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp))).symm
  simp_rw [hFlux,energyDrift,Finset.sum_add_distrib,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  have hSwap : (∑ i,∑ j,Parabolic.d (fun x => a (x,p.2) i j) p.1 i*classicalCaloricGradient v p j)=
      ∑ j,∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i*classicalCaloricGradient v p j := Finset.sum_comm
  rw [hSwap]
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen hD hp,hTime]
  simp_rw [hSpatial]
  ring

end Yau.Proofs.F03Aux
