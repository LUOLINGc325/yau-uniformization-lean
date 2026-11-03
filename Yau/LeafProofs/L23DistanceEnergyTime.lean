import Yau.LeafProofs.L23DistanceEnergyIntegral
import Yau.LeafProofs.L23LocalDistanceSupportEnergy
import Yau.LeafProofs.L23LocalDistanceSupport

/-! The fixed path is differentiated only through the original evolving metric. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

theorem fieldPathSpeedSq_time_hasDerivAt
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (γ : ℝ → M.Carrier) (u : ℝ) (hu : γ u∈O) (t : ℝ) (ht : t∈Set.Ioo a b) :
    HasDerivAt (fun s => fieldPathSpeed (h s) γ u^2)
      (-σ*fieldRealRicciQuadratic (h t) (γ u)
        (realTangentEquiv (γ u) (realCurveVelocity γ u))) t := by
  simpa only [fieldPathSpeed_sq] using localRealRicciFlow_tangentNorm_hasDerivAt h hflow hu ht
    (realTangentEquiv (γ u) (realCurveVelocity γ u))

theorem fieldPathEnergy_time_deriv_lower
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ K d : ℝ)
    (hσ : 0≤σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (γ : ℝ → M.Carrier) (hγ : ∀ u∈Set.Icc (0 : ℝ) 1, γ u∈O)
    (t : ℝ) (ht : t∈Set.Ioo a b)
    (hcurv : ∀ u∈Set.Icc (0 : ℝ) 1, curvatureJetNorm (h t) 0 (γ u)≤K)
    (hspeed : ∀ u∈Set.Icc (0 : ℝ) 1, fieldPathSpeed (h t) γ u^2=d^2)
    (T J : Set ℝ) (hT : IsOpen T) (hJ : IsOpen J) (htT : t∈T)
    (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => fieldPathSpeed (h p.1) γ p.2^2) (T ×ˢ J)) :
    -σ*(2*n : ℕ)*K*d^2≤deriv (fun s => fieldPathEnergy (h s) γ) t := by
  let F : ℝ × ℝ → ℝ := fun p => fieldPathSpeed (h p.1) γ p.2^2
  let D : ℝ → ℝ := fun u => parameterDerivative F (t,u) 1
  have hDP : ContinuousOn (fun u => parameterDerivative F (t,u)) (Set.Icc (0 : ℝ) 1) :=
    (parameterDerivative_contDiffOn hT hJ 0 (by simpa only [Nat.cast_zero,zero_add] using hF)).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨htT,hIJ hu⟩)
  have hDPint : IntegrableOn (fun u => parameterDerivative F (t,u)) (Set.Icc (0 : ℝ) 1) :=
    hDP.integrableOn_Icc
  have hDcont : ContinuousOn D (Set.Icc (0 : ℝ) 1) :=
    hDP.clm_apply continuousOn_const
  have hDint : IntegrableOn D (Set.Icc (0 : ℝ) 1) := hDcont.integrableOn_Icc
  have hDer : HasDerivAt (fun s => fieldPathEnergy (h s) γ) (∫ u in Set.Icc (0 : ℝ) 1,D u) t := by
    have H := (hasFDerivAt_unitIntegral hT hJ hIJ hF htT).hasDerivAt
    rw [ContinuousLinearMap.integral_apply hDPint] at H
    exact H
  have hDval (u : ℝ) (hu : u∈Set.Icc (0 : ℝ) 1) :
      D u=-σ*fieldRealRicciQuadratic (h t) (γ u)
        (realTangentEquiv (γ u) (realCurveVelocity γ u)) := by
    have hp : DifferentiableAt ℝ F (t,u) :=
      (hF.contDiffAt ((hT.prod hJ).mem_nhds ⟨htT,hIJ hu⟩)).differentiableAt_one
    exact (parameterDerivative_hasFDerivAt F (p := (t,u)) hp).hasDerivAt.unique
      (fieldPathSpeedSq_time_hasDerivAt h O a b σ hflow γ u (hγ u hu) t ht)
  have hDlower (u : ℝ) (hu : u∈Set.Icc (0 : ℝ) 1) : -σ*(2*n : ℕ)*K*d^2≤D u := by
    let v := realTangentEquiv (γ u) (realCurveVelocity γ u)
    have hR := realRicciQuadratic_abs_le (h t) (γ u) v
    change |fieldRealRicciQuadratic (h t) (γ u) v|≤
      (2*n : ℕ)*curvatureJetNorm (h t) 0 (γ u)*(2*hermitianNormSq ((h t) (γ u)) v) at hR
    have hspeed' : 2*hermitianNormSq ((h t) (γ u)) v=d^2 := by
      rw [←fieldPathSpeed_sq]
      exact hspeed u hu
    rw [hspeed'] at hR
    have hUpper : fieldRealRicciQuadratic (h t) (γ u) v≤(2*n : ℕ)*K*d^2 :=
      (le_abs_self _).trans (hR.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcurv u hu) (Nat.cast_nonneg _)) (sq_nonneg d)))
    have H := mul_le_mul_of_nonneg_left hUpper hσ
    rw [hDval u hu]
    change -σ*(2*n : ℕ)*K*d^2≤-σ*fieldRealRicciQuadratic (h t) (γ u) v
    nlinarith [H]
  rw [hDer.deriv]
  have HI := setIntegral_mono_on (integrableOn_const (by simp)) hDint measurableSet_Icc hDlower
  simpa [Measure.real] using HI

end Yau.LeafProofs.L23Aux
