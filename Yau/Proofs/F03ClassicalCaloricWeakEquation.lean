import Yau.Proofs.F03ClassicalCaloricOperator
import Yau.Proofs.F03ClassicalDivergenceWeak

/-! Actual smooth classical solutions give BOTH literal native weak inputs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem classicalCaloricGradient_weakEquation (O : Set (Space d)) (I : Set ℝ)
    (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    (hClass : ∀ p ∈ O ×ˢ I, linearOp (O ×ˢ I) a b v p=0) :
    WeakEquation O I a b (fun _ => 0) v (classicalCaloricGradient v) := by
  let P := energyFlux a (classicalCaloricGradient v)
  let R : Point d → ℝ := fun p => ∑ j,energyDrift a b p j*classicalCaloricGradient v p j
  have hG (j : RIdx d) : ContDiffOn ℝ ∞ (fun p => classicalCaloricGradient v p j) (O ×ˢ I) :=
    (hv.fderiv_of_isOpen hD (by simp)).clm_apply contDiffOn_const
  have hP : ∀ i, ContDiffOn ℝ ∞ (fun p => P p i) (O ×ˢ I) := by
    intro i
    change ContDiffOn ℝ ∞ (fun p => ∑ j,a p i j*classicalCaloricGradient v p j) (O ×ˢ I)
    apply ContDiffOn.sum
    intro j _
    exact ((matrixEntryCLM i j).contDiff.comp_contDiffOn hAB.1).mul (hG j)
  have hR : ContDiffOn ℝ ∞ R (O ×ˢ I) := by
    apply ContDiffOn.sum
    intro j _
    exact (energyDrift_smooth hD hAB j).mul (hG j)
  have hDiv : WeakDivergenceEvolution O I v P R := by
    apply local_classical_divergence_weak O I hD v P R hv hP hR.continuousOn
    intro p hp
    exact (classicalCaloric_operator_divergence hD a b hAB v hv p hp).trans (hClass p hp)
  intro φ hφ
  have h := hDiv φ hφ
  simpa only [P,R,energyFlux,energyDrift,Finset.sum_mul,zero_mul,integral_zero] using h

theorem classicalCaloricGradient_weak_energy (O : Set (Space d)) (I : Set ℝ)
    (hD : IsOpen (O ×ˢ I))
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients (O ×ˢ I) a b)
    (v : Point d → ℝ) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    (hClass : ∀ p ∈ O ×ˢ I, linearOp (O ×ˢ I) a b v p=0) :
    LocalEnergy O I v (classicalCaloricGradient v) ∧
      WeakEquation O I a b (fun _ => 0) v (classicalCaloricGradient v) :=
  ⟨classicalCaloricGradient_localEnergy O I hD v hv,
    classicalCaloricGradient_weakEquation O I hD a b hAB v hv hClass⟩

end Yau.Proofs.F03Aux
