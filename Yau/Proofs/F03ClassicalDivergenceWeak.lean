import Yau.Proofs.F03ClassicalCaloricEnergy

/-! Smooth local classical divergence solutions satisfy the exact frozen weak tests. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem local_classical_divergence_weak (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (v : Point d → ℝ) (P : Point d → RIdx d → ℝ) (R : Point d → ℝ)
    (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    (hP : ∀ i, ContDiffOn ℝ ∞ (fun p => P p i) (O ×ˢ I))
    (hR : ContinuousOn R (O ×ˢ I))
    (hClass : ∀ p ∈ O ×ˢ I, fderiv ℝ v p (0,1)-
      (∑ i,fderiv ℝ (fun q => P q i) p (realVec i,0))-R p=0) :
    WeakDivergenceEvolution O I v P R := by
  intro φ hφ
  obtain ⟨V,hV,hKV,hVD,hVc⟩ := exists_open_between_and_isCompact_closure hφ.2.1 hD hφ.2.2
  have hVD' : V ⊆ O ×ˢ I := subset_closure.trans hVD
  have hφV : Test V φ := ⟨hφ.1,hφ.2.1,hKV⟩
  have hMem : ∀ f : Point d → ℝ, ContinuousOn f (O ×ˢ I) → MemLp f 2 (volume.restrict V) := by
    intro f hf
    exact (continuousOn_memLp_two_of_isCompact hVc (hf.mono hVD)).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  let T : Point d → ℝ := fun p => fderiv ℝ v p (0,1)
  let S : RIdx d → Point d → ℝ := fun i p => fderiv ℝ (fun q => P q i) p (realVec i,0)
  have hTdiff : ContDiffOn ℝ ∞ T (O ×ˢ I) :=
    (hv.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  have hSdiff : ∀ i, ContDiffOn ℝ ∞ (S i) (O ×ˢ I) := fun i =>
    ((hP i).fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  have hT : ContinuousOn T (O ×ˢ I) := hTdiff.continuousOn
  have hS : ∀ i, ContinuousOn (S i) (O ×ˢ I) := fun i => (hSdiff i).continuousOn
  have hTInt : Integrable (fun p => T p*φ p) (volume.restrict V) :=
    (hMem T hT).integrable_mul (test_memLp hφV)
  have hSInt : ∀ i, Integrable (fun p => S i p*φ p) (volume.restrict V) := fun i =>
    (hMem (S i) (hS i)).integrable_mul (test_memLp hφV)
  have hRInt : Integrable (fun p => R p*φ p) (volume.restrict V) :=
    (hMem R hR).integrable_mul (test_memLp hφV)
  have hSumInt : Integrable (fun p => (∑ i,S i p)*φ p) (volume.restrict V) := by
    simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => hSInt i)
  have hZero : (∫ p, (T p-(∑ i,S i p)-R p)*φ p ∂volume.restrict V)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
    change (fderiv ℝ v p (0,1)-(∑ i,fderiv ℝ (fun q => P q i) p (realVec i,0))-R p)*φ p=0
    rw [hClass p (hVD' hp),zero_mul]
  have hIntegrated : (∫ p,T p*φ p ∂volume.restrict V)-
      (∑ i,∫ p,S i p*φ p ∂volume.restrict V)-(∫ p,R p*φ p ∂volume.restrict V)=0 := by
    have hSplit1 := integral_sub (hTInt.sub hSumInt) hRInt
    have hSplit2 := integral_sub hTInt hSumInt
    simp only [Pi.sub_apply] at hSplit1 hSplit2
    simp_rw [sub_mul] at hZero
    rw [hSplit1,hSplit2] at hZero
    simp_rw [Finset.sum_mul] at hZero
    rw [integral_finsetSum Finset.univ (fun i _ => hSInt i)] at hZero
    exact hZero
  rw [productVolume_eq_restrict]
  simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
    d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)]
  rw [divergence_test_integral_restrict_eq_global hφ,
    ← divergence_test_integral_restrict_eq_global hφV,
    integral_divergence_test_form (hMem v hv.continuousOn) (fun i => hMem (fun p => P p i) (hP i).continuousOn)
      (hMem R hR) hφV]
  rw [local_smooth_test_directional_ibp hV (hv.mono hVD') hφV (0,1)]
  simp_rw [local_smooth_test_directional_ibp hV ((hP _).mono hVD') hφV (realVec _,0)]
  rw [Finset.sum_neg_distrib]
  dsimp only [T,S] at hIntegrated
  linarith only [hIntegrated]

end Yau.Proofs.F03Aux
