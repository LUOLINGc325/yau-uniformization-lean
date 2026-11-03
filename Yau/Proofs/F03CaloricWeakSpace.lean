import Yau.Proofs.F03CaloricTestSpace

/-! Membership in the explicit closed space gives the literal native weak PDE. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem caloricGradientTestCLM_apply (D : Set (Point d)) (φ : testFunctionSpace D)
    (i : RIdx d) (e : CaloricAmbient D) :
    caloricGradientTestCLM D φ i e=
      (∫ p, e.1 p*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i ∂volume.restrict D)+
        (∫ p, e.2 i p*φ.val p ∂volume.restrict D) := by
  change caloricTestPair D (caloricSpatialTest D φ i) e.1+caloricTestPair D φ (e.2 i)=_
  rw [caloricTestPair_apply,caloricTestPair_apply]
  rfl

theorem caloricEquation_integrand_eq (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (u : Point d → ℝ) (G : Point d → RIdx d → ℝ) (p : Point d) :
    -u p*deriv (fun t => φ.val (p.1,t)) p.2+
      (∑ i,∑ j,a p i j*G p j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)-
      (∑ j,(b p j-∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i)*G p j*φ.val p) =
      -(u p*deriv (fun t => φ.val (p.1,t)) p.2)+
        ∑ j,G p j*(caloricEquationTest D hD a b hAB φ j).val p := by
  have hsum : (∑ i,∑ j,a p i j*G p j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)=
      ∑ j,G p j*(∑ i,a p i j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdrift : (∑ j,energyDrift a b p j*G p j*φ.val p)=
      ∑ j,G p j*(energyDrift a b p j*φ.val p) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  change -u p*deriv (fun t => φ.val (p.1,t)) p.2+
      (∑ i,∑ j,a p i j*G p j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)-
      (∑ j,energyDrift a b p j*G p j*φ.val p)=_
  rw [hsum,hdrift]
  simp only [caloricEquationTest_apply,mul_sub,Finset.sum_sub_distrib]
  ring

theorem caloricEquationTestCLM_apply (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (e : CaloricAmbient D) :
    caloricEquationTestCLM D hD a b hAB φ e=
      ∫ p, -e.1 p*deriv (fun t => φ.val (p.1,t)) p.2+
        (∑ i,∑ j,a p i j*e.2 j p*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)-
        (∑ j,(b p j-∑ i,Parabolic.d (fun x => a (x,p.2) i j) p.1 i)*e.2 j p*φ.val p)
          ∂volume.restrict D := by
  have ht : Integrable (fun p => e.1 p*(caloricTimeTest D φ).val p) (volume.restrict D) :=
    (Lp.memLp e.1).integrable_mul (test_memLp (caloricTimeTest D φ).2)
  have hq : ∀ j, Integrable (fun p => e.2 j p*(caloricEquationTest D hD a b hAB φ j).val p)
      (volume.restrict D) := fun j =>
    (Lp.memLp (e.2 j)).integrable_mul (test_memLp (caloricEquationTest D hD a b hAB φ j).2)
  simp only [caloricEquationTestCLM,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  change -caloricTestPair D (caloricTimeTest D φ) e.1+
    (∑ j,caloricTestPair D (caloricEquationTest D hD a b hAB φ j) (e.2 j))=_
  rw [caloricTestPair_apply]
  simp_rw [caloricTestPair_apply]
  symm
  calc
    _ = ∫ p, -(e.1 p*(caloricTimeTest D φ).val p)+
        ∑ j,e.2 j p*(caloricEquationTest D hD a b hAB φ j).val p ∂volume.restrict D := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => caloricEquation_integrand_eq D hD a b hAB φ
        (e.1 : Point d → ℝ) (fun q j => e.2 j q) p)
    _ = (∫ p, -(e.1 p*(caloricTimeTest D φ).val p) ∂volume.restrict D)+
        (∫ p, ∑ j,e.2 j p*(caloricEquationTest D hD a b hAB φ j).val p ∂volume.restrict D) :=
      integral_add ht.neg (integrable_finsetSum Finset.univ (fun j _ => hq j))
    _ = _ := congrArg₂ (fun x y : ℝ => x+y)
      (integral_neg (fun p => e.1 p*(caloricTimeTest D φ).val p))
      (integral_finsetSum Finset.univ (fun j _ => hq j))

theorem caloricSpace_weakGradient (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (e : CaloricSpace (O ×ˢ I) hD a b hAB) :
    WeakGradient O I (e.val.1 : Point d → ℝ) (fun p i => e.val.2 i p) := by
  intro φ hφ i
  have h := e.property.1 ⟨φ,hφ⟩ i
  rw [caloricGradientTestCLM_apply] at h
  rw [productVolume_eq_restrict]
  exact eq_neg_of_add_eq_zero_left h

theorem caloricSpace_weakEquation (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (e : CaloricSpace (O ×ˢ I) hD a b hAB) :
    WeakEquation O I a b (fun _ => 0) (e.val.1 : Point d → ℝ) (fun p i => e.val.2 i p) := by
  intro φ hφ
  have h := e.property.2 ⟨φ,hφ⟩
  rw [caloricEquationTestCLM_apply] at h
  rw [productVolume_eq_restrict]
  simpa only [zero_mul,integral_zero] using h

theorem caloricSpace_localEnergy (O : Set (Space d)) (I : Set ℝ) (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (e : CaloricSpace (O ×ˢ I) hD a b hAB) :
    LocalEnergy O I (e.val.1 : Point d → ℝ) (fun p i => e.val.2 i p) := by
  refine ⟨caloricSpace_weakGradient O I hD a b hAB e,?_⟩
  intro V c r _hV _hVc hVO hcr
  have hsub : V ×ˢ Ioo c r ⊆ O ×ˢ I := fun p hp => ⟨hVO (subset_closure hp.1),hcr ⟨hp.2.1.le,hp.2.2.le⟩⟩
  rw [productVolume_eq_restrict]
  exact ⟨(Lp.memLp e.val.1).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => (Lp.memLp (e.val.2 i)).mono_measure (Measure.restrict_mono hsub le_rfl)⟩

end Yau.Proofs.F03Aux
