import Yau.Proofs.F03CaloricCompactJet

/-! Exact compact-test adjoints of every local caloric directional jet. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def caloricJetSourceTestCLM (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (w : List (Point d)) (φ : testFunctionSpace D) : CaloricSpace D hD a b hAB →L[ℝ] ℝ :=
  (-1 : ℝ)^w.length • ((caloricTestPair D
    ⟨directionalWordDerivative φ.val w.reverse,test_directionalWordDerivative φ.2 w.reverse⟩).comp
      ((caloricValueCLM D).comp (caloricSubmodule D hD a b hAB).subtypeL))

theorem caloricJetSourceTestCLM_apply (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (w : List (Point d)) (φ : testFunctionSpace D) (e : CaloricSpace D hD a b hAB) :
    caloricJetSourceTestCLM D hD a b hAB w φ e=
      (-1 : ℝ)^w.length*(∫ p, e.val.1 p*directionalWordDerivative φ.val w.reverse p ∂volume.restrict D) := by
  change (-1 : ℝ)^w.length*caloricTestPair D
    ⟨directionalWordDerivative φ.val w.reverse,test_directionalWordDerivative φ.2 w.reverse⟩ e.val.1=_
  rw [caloricTestPair_apply]

theorem caloricCompactJet_test
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Point d))]
    (hKm : MeasurableSet K) (hKD : K ⊆ O ×ˢ Ioo l r) (w : List (Point d))
    (φ : Point d → ℝ) (hφ : Test (O ×ˢ Ioo l r) φ) (hφK : tsupport φ ⊆ K)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    compactTestFunctional K (volume.comap ((↑) : K → Point d))
      (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
      (caloricCompactJet hd O l r lam upper hO hlr a b hAB hEll K hKD w e)=
        caloricJetSourceTestCLM (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB w ⟨φ,hφ⟩ e := by
  let R := caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e
  have hs := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e
  have hJK : ContinuousOn (directionalWordDerivative R w) K :=
    (directionalWordDerivative_contDiffOn (hO.prod isOpen_Ioo) hs.1 w).continuousOn.mono hKD
  change compactTestFunctional K (volume.comap ((↑) : K → Point d))
    (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
    (compactContinuousRestriction K (directionalWordDerivative R w) hJK)=_
  rw [compactTestFunctional_restrict_apply (volume : Measure (Point d)) K hKm φ
    (directionalWordDerivative R w) hφ.1.continuous.continuousOn hJK,caloricJetSourceTestCLM_apply]
  have hLeft : (∫ p in K, directionalWordDerivative R w p*φ p)=
      ∫ p, directionalWordDerivative R w p*φ p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hφK h)),mul_zero]
  rw [hLeft,directionalWordDerivative_test_integral (hO.prod isOpen_Ioo) hs.1 w hφ,
    ← integral_mul_test_eq (test_directionalWordDerivative hφ w.reverse) R]
  congr 1
  apply integral_congr_ae
  filter_upwards [hs.2.1] with p hp
  exact congrArg (fun v : ℝ => v*directionalWordDerivative φ w.reverse p) hp.symm

end Yau.Proofs.F03Aux
