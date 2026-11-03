import Yau.Proofs.F03CaloricCompactJetTesting
import Yau.Proofs.F03CompactTestSeparation
import Yau.Proofs.F03ClosedGraphTests

/-! Compact-test closed graph gives actual fixed-space word-jet bounds. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem caloricCompactJet_continuous
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Point d))]
    (hKc : IsCompact K) (hreg : K=closure (interior K)) (hKD : K ⊆ O ×ˢ Ioo l r) (w : List (Point d)) :
    Continuous (caloricCompactJet hd O l r lam upper hO hlr a b hAB hEll K hKD w) := by
  let ι := {φ : Point d → ℝ // Test (interior K) φ}
  let hTest : ∀ φ : ι, Test (O ×ˢ Ioo l r) φ.val := fun φ =>
    ⟨φ.property.1,φ.property.2.1,φ.property.2.2.trans (interior_subset.trans hKD)⟩
  let A : ι → C(K,ℝ) →L[ℝ] ℝ := fun φ => compactTestFunctional K
    (volume.comap ((↑) : K → Point d))
      (compactContinuousRestriction K φ.val φ.property.1.continuous.continuousOn)
  let B : ι → CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB →L[ℝ] ℝ := fun φ =>
    caloricJetSourceTestCLM (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB w ⟨φ.val,hTest φ⟩
  apply linearMap_continuous_of_tests (caloricCompactJet hd O l r lam upper hO hlr a b hAB hEll K hKD w) A B
  · intro q hq
    apply compactTestFunctional_separates K hKc hreg q
    intro φ hφ
    exact hq ⟨φ,hφ⟩
  · intro φ e
    exact caloricCompactJet_test hd O l r lam upper hO hlr a b hAB hEll K hKc.measurableSet hKD w
      φ.val (hTest φ) (φ.property.2.2.trans interior_subset) e

theorem caloricRepresentative_compact_word_bound
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Point d))]
    (hKc : IsCompact K) (hreg : K=closure (interior K)) (hKD : K ⊆ O ×ˢ Ioo l r) (w : List (Point d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB,
      ∀ p ∈ K, |directionalWordDerivative (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) w p| ≤
        C*‖e‖ := by
  let L : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB →L[ℝ] C(K,ℝ) :=
    ⟨caloricCompactJet hd O l r lam upper hO hlr a b hAB hEll K hKD w,
      caloricCompactJet_continuous hd O l r lam upper hO hlr a b hAB hEll K hKc hreg hKD w⟩
  refine ⟨max 1 ‖L‖,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro e p hp
  have hv := (L e).norm_coe_le_norm (⟨p,hp⟩ : K)
  change |directionalWordDerivative (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) w p| ≤ ‖L e‖ at hv
  exact hv.trans ((L.le_opNorm e).trans (mul_le_mul_of_nonneg_right (le_max_right 1 ‖L‖) (norm_nonneg e)))

end Yau.Proofs.F03Aux
