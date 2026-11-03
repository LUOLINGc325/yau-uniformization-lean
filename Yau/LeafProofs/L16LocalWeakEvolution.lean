import Yau.LeafProofs.L16WeakEvolutionCalculus

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem divergence_test_integral_restrict_eq_global {n : ℕ} {Q : Set (Point n)}
    {φ : Point n → ℝ} (hφ : Test Q φ) (w : Point n → ℝ)
    (P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ) :
    (∫ p, -w p*fderiv ℝ φ p (0,1)+
      (∑ i, P p i*fderiv ℝ φ p (Yau.realVec i,0))-R p*φ p ∂volume.restrict Q) =
      ∫ p, -w p*fderiv ℝ φ p (0,1)+
        (∑ i, P p i*fderiv ℝ φ p (Yau.realVec i,0))-R p*φ p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hZero : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hφ.2.2 h))
  have hTime : fderiv ℝ φ p (0,1) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q (0,1))
      (fun h => hp ((test_directionalDerivative hφ (0,1)).2.2 h))
  have hSpace (i : Yau.RIdx n) : fderiv ℝ φ p (Yau.realVec i,0) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q (Yau.realVec i,0))
      (fun h => hp ((test_directionalDerivative hφ (Yau.realVec i,0)).2.2 h))
  simp only [hZero,hTime,hSpace,mul_zero,Finset.sum_const_zero,add_zero,sub_self]

theorem weakDivergenceEvolutionOn_of_frozen_local {n : ℕ}
    {O : Set (Space n)} {I : Set ℝ} {V : Set (Point n)} (hVQ : V ⊆ O ×ˢ I)
    {w R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict V))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (volume.restrict V))
    (hR : MemLp R 2 (volume.restrict V))
    (hEq : WeakDivergenceEvolution O I w P R) :
    WeakDivergenceEvolutionOn V w P R := by
  intro φ hφ
  have hφQ : Test (O ×ˢ I) φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hVQ⟩
  have h := hEq φ hφQ
  rw [productVolume_eq_restrict] at h
  simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
    d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)] at h
  rw [divergence_test_integral_restrict_eq_global hφQ] at h
  rw [← divergence_test_integral_restrict_eq_global hφ] at h
  rw [integral_divergence_test_form hw hP hR hφ] at h
  exact h

end Yau.LeafProofs.L16Aux
