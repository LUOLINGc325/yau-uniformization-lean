import Yau.LeafProofs.L16WeakEvolutionCalculus
import Yau.LeafProofs.L16WeakCutoff

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem weakDivergenceEvolutionOn_cutoff {n : ℕ} {Q : Set (Point n)}
    {w R η : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict Q))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q))
    (hEq : WeakDivergenceEvolutionOn Q w P R) (hη : Test Q η) :
    WeakDivergenceEvolution Set.univ Set.univ (fun p => η p*w p)
      (fun p i => η p*P p i) (cutoffEvolutionSource w P R η) := by
  intro φ hφ
  have hTest := test_mul_smooth hη hφ.1
  have h := hEq (fun p => η p*φ p) hTest
  rw [← integral_divergence_test_form hw hP hR hTest] at h
  have hVanish (p : Point n) (hp : p ∉ Q) :
      -w p*fderiv ℝ (fun q => η q*φ q) p (0,1)+
        (∑ i, P p i*fderiv ℝ (fun q => η q*φ q) p (Yau.realVec i,0))-R p*(η p*φ p) = 0 := by
    have hZero : η p*φ p = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun q => η q*φ q) (fun h => hp (hTest.2.2 h))
    have hTime : fderiv ℝ (fun q => η q*φ q) p (0,1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun q : Point n => fderiv ℝ (fun z => η z*φ z) q (0,1))
        (fun h => hp ((test_directionalDerivative hTest (0,1)).2.2 h))
    have hSpace (i : Yau.RIdx n) : fderiv ℝ (fun q => η q*φ q) p (Yau.realVec i,0) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun q : Point n => fderiv ℝ (fun z => η z*φ z) q (Yau.realVec i,0))
        (fun h => hp ((test_directionalDerivative hTest (Yau.realVec i,0)).2.2 h))
    simp only [hZero,hTime,hSpace,mul_zero,Finset.sum_const_zero,add_zero,sub_self]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hVanish] at h
  rw [productVolume_eq_restrict]
  simp only [Set.univ_prod_univ,Measure.restrict_univ]
  convert h using 1
  congr 1
  ext p
  simp only [cutoffEvolutionSource]
  rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) p),
    test_timeDerivative_eq_joint_fderiv (hη.1.differentiable (by simp) p)]
  simp_rw [d_eq_joint_fderiv (hφ.1.differentiable (by simp) p),
    d_eq_joint_fderiv (hη.1.differentiable (by simp) p)]
  rw [fderiv_fun_mul (hη.1.differentiable (by simp) p) (hφ.1.differentiable (by simp) p)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring_nf
  simp only [Finset.mul_sum,mul_assoc]

theorem cutoffEvolutionSource_memLp_of_memLp {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {w R η : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict Q))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q)) (hη : Test Q η) :
    MemLp (cutoffEvolutionSource w P R η) 2 volume := by
  have hR0 := test_mul_memLp_global hQ hη hR
  have hTime : MemLp (fun p => w p*deriv (fun t => η (p.1,t)) p.2) 2 volume := by
    simpa only [mul_comm] using test_mul_memLp_global hQ (test_timeDerivative hη) hw
  have hSpace (i : Yau.RIdx n) :
      MemLp (fun p => P p i*d (fun x => η (x,p.2)) p.1 i) 2 volume := by
    simpa only [mul_comm] using test_mul_memLp_global hQ (test_spatialDerivative hη i) (hP i)
  have hSum := memLp_finsetSum Finset.univ (fun i _ => hSpace i)
  convert! (hR0.add hTime).sub hSum using 1

theorem weakDivergenceEvolutionOn_cutoff_fields {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {w R η : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict Q))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q))
    (hEq : WeakDivergenceEvolutionOn Q w P R) (hη : Test Q η) :
    MemLp (fun p => η p*w p) 2 volume ∧ HasCompactSupport (fun p => η p*w p) ∧
      (∀ i, MemLp (fun p => η p*P p i) 2 volume ∧ HasCompactSupport (fun p => η p*P p i)) ∧
      MemLp (cutoffEvolutionSource w P R η) 2 volume ∧
      HasCompactSupport (cutoffEvolutionSource w P R η) ∧
      WeakDivergenceEvolution Set.univ Set.univ (fun p => η p*w p)
        (fun p i => η p*P p i) (cutoffEvolutionSource w P R η) := by
  exact ⟨test_mul_memLp_global hQ hη hw,hη.2.1.mul_right,
    fun i => ⟨test_mul_memLp_global hQ hη (hP i),hη.2.1.mul_right⟩,
    cutoffEvolutionSource_memLp_of_memLp hQ hw hP hR hη,cutoffEvolutionSource_compact w P R hη,
    weakDivergenceEvolutionOn_cutoff hw hP hR hEq hη⟩

end Yau.LeafProofs.L16Aux
