import Yau.Proofs.F03CaloricCutoffs
import Yau.Proofs.F03CaloricCoefficientBounds
import Yau.LeafProofs.L16Caccioppoli

/-! The native compact energy identity supplies a genuine two-cutoff L² estimate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem weak_caloric_test_gradient_integral_bound
    (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (η : Point d → ℝ) (hη : Test (O ×ˢ Ioo l r) η) (hηrange : ∀ p, η p ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point d → ℝ) (G : Point d → RIdx d → ℝ),
      LocalEnergy O (Ioo l r) u G → WeakEquation O (Ioo l r) a b (fun _ => 0) u G →
      MemLp u 2 (volume.restrict (O ×ˢ Ioo l r)) →
      Integrable (fun p => η p^2*(∑ i,(G p i)^2)) volume ∧
      (∫ p, η p^2*(∑ i,(G p i)^2)) ≤ C*(∫ p in O ×ˢ Ioo l r,(u p)^2) := by
  obtain ⟨A,B,hA,hB,ha,hb⟩ := caloric_coefficients_compact_bounds (O ×ˢ Ioo l r)
    (hO.prod isOpen_Ioo) a b hAB (tsupport η) hη.2.1 hη.2.2
  obtain ⟨M,hM,hTime,hSpace⟩ := test_joint_directional_derivatives_bounded η hη
  obtain ⟨C,hC,hCaccioppoli⟩ := exists_caccioppoli_constant d lam upper A B M hEll.1 hA.le hB.le hM.le
  obtain ⟨χ,hχ,hχrange,hχnear⟩ := exists_nonnegative_test_eq_one_near_compact
    (hO.prod isOpen_Ioo) hη.2.1 hη.2.2
  have hχone : ∀ p ∈ tsupport η, χ p=1 := fun p hp => (hχnear p hp).eq_of_nhds
  have hηBound : ∀ p, |η p| ≤ 1 := fun p => by rw [abs_of_nonneg (hηrange p).1];exact (hηrange p).2
  have hEllη : Elliptic (tsupport η) a lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hη.2.2 hp)⟩
  have hηSupp : Test (tsupport η) η := ⟨hη.1,hη.2.1,subset_rfl⟩
  refine ⟨C,hC,?_⟩
  intro u G hE hWE hu
  let w : Point d → ℝ := fun p => χ p*u p
  let H : Point d → RIdx d → ℝ := fun p i => χ p*G p i
  let P : Point d → RIdx d → ℝ := fun p i => χ p*energyFlux a G p i
  let R : Point d → ℝ := fun p => χ p*(∑ j,energyDrift a b p j*G p j)
  have hCut := localEnergy_cutoff_memLp hO hE hχ.1.continuous hχ.2.1 hχ.2.2
  have hw : MemLp w 2 volume := hCut.1
  have hH : ∀ i, MemLp (fun p => H p i) 2 volume := hCut.2
  have hP : ∀ i, MemLp (fun p => P p i) 2 volume :=
    fun i => localEnergy_cutoff_flux_memLp hO hAB hE hχ i
  have hR : MemLp R 2 volume := localEnergy_cutoff_drift_memLp hO hAB hE hχ
  have hFlux : ∀ p ∈ tsupport η, ∀ i, P p i=energyFlux a H p i+(0 : ℝ) := by
    intro p _hp i
    change χ p*(∑ j,a p i j*G p j)=(∑ j,a p i j*(χ p*G p j))+0
    rw [add_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSource : ∀ p ∈ tsupport η, R p=(∑ i,energyDrift a b p i*H p i)+(0 : ℝ) := by
    intro p _hp
    change χ p*(∑ i,energyDrift a b p i*G p i)=(∑ i,energyDrift a b p i*(χ p*G p i))+0
    rw [add_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hψ : Test (O ×ˢ Ioo l r) (fun p => η p^2) := by
    simpa only [pow_two] using test_mul_smooth hη hη.1
  have hψSupp : tsupport (fun p => η p^2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  have hEnergy : compactEnergyFunctional (fun p => η p^2) w H P R=0 := by
    have hNative := localEnergy_homogeneous_compact_energy_identity hO hAB hE hWE hψ
    have hCongr : compactEnergyFunctional (fun p => η p^2) u G (energyFlux a G)
        (fun p => ∑ j,energyDrift a b p j*G p j)=
        compactEnergyFunctional (fun p => η p^2) w H P R := by
      apply compactEnergyFunctional_congr_on_support
      · intro p hp
        change u p=χ p*u p
        rw [hχone p (hψSupp hp),one_mul]
      · intro i p hp
        change G p i=χ p*G p i
        rw [hχone p (hψSupp hp),one_mul]
      · intro i p hp
        change energyFlux a G p i=χ p*energyFlux a G p i
        rw [hχone p (hψSupp hp),one_mul]
      · intro p hp
        change (∑ j,energyDrift a b p j*G p j)=χ p*(∑ j,energyDrift a b p j*G p j)
        rw [hχone p (hψSupp hp),one_mul]
    exact hCongr.symm.trans hNative
  have hBound := hCaccioppoli (tsupport η) a (energyDrift a b) η w (fun _ => 0) H P (fun _ _ => 0) R
    hEllη ha hb hηSupp hηBound hTime hSpace hw hH hP hR (fun _ => MemLp.zero') MemLp.zero'
      hFlux hSource hEnergy
  have hWeightedInt : Integrable (fun p => η p^2*(∑ i,(H p i)^2)) volume := by
    have hEach : ∀ i, Integrable (fun p => η p^2*(H p i)^2) volume := by
      intro i
      have hSq : Integrable (fun p => (H p i)^2) volume := by
        apply ((hH i).integrable_mul (hH i)).congr
        exact ae_of_all _ (fun p => by change H p i*H p i=(H p i)^2;ring)
      have hηMeas : AEStronglyMeasurable (fun p => η p^2) volume := (hη.1.continuous.pow 2).aestronglyMeasurable
      apply hSq.bdd_mul (c := (1 : ℝ)) hηMeas
      filter_upwards [] with p
      change |η p^2| ≤ 1
      have hηsq : η p^2 ≤ 1 := by nlinarith [mul_nonneg (hηrange p).1 (sub_nonneg.mpr (hηrange p).2)]
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (η p))] using hηsq
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hEach i)
  have hWeightedEq : (fun p => η p^2*(∑ i,(H p i)^2))=(fun p => η p^2*(∑ i,(G p i)^2)) := by
    funext p
    by_cases hp : p ∈ tsupport η
    · simp only [H,hχone p hp,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hp]
      simp
  rw [hWeightedEq] at hWeightedInt hBound
  have hwSq : Integrable (fun p => (w p)^2) volume := by
    apply (hw.integrable_mul hw).congr
    exact ae_of_all _ (fun p => by change w p*w p=(w p)^2;ring)
  have huSq : Integrable (fun p => (u p)^2) (volume.restrict (O ×ˢ Ioo l r)) := by
    apply (hu.integrable_mul hu).congr
    exact ae_of_all _ (fun p => by change u p*u p=(u p)^2;ring)
  have hwIntBound : (∫ p,(w p)^2) ≤ ∫ p in O ×ˢ Ioo l r,(u p)^2 := by
    have heq : (∫ p in O ×ˢ Ioo l r,(w p)^2)=(∫ p,(w p)^2) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hχzero : χ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hχ.2.2 h))
      change (χ p*u p)^2=0
      rw [hχzero,zero_mul]
      norm_num
    rw [← heq]
    apply integral_mono (hwSq.mono_measure Measure.restrict_le_self) huSq
    intro p
    change (χ p*u p)^2 ≤ (u p)^2
    rw [mul_pow]
    have hχsq : χ p^2 ≤ 1 := by nlinarith [mul_nonneg (hχrange p).1 (sub_nonneg.mpr (hχrange p).2)]
    exact (mul_le_mul_of_nonneg_right hχsq (sq_nonneg (u p))).trans_eq (one_mul _)
  refine ⟨hWeightedInt,?_⟩
  have hBound' : (∫ p,η p^2*(∑ i,(G p i)^2)) ≤ C*(∫ p,(w p)^2) := by
    change (∫ p,η p^2*(∑ i,(G p i)^2)) ≤
      C*(∫ p,(w p)^2+(∑ i : RIdx d,(0 : ℝ)^2)+(0 : ℝ)^2) at hBound
    simpa only [show (0 : ℝ)^2=0 by norm_num,Finset.sum_const_zero,add_zero] using hBound
  exact hBound'.trans (mul_le_mul_of_nonneg_left hwIntBound hC.le)

end Yau.Proofs.F03Aux
