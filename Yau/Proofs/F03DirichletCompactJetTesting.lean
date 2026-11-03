import Yau.Proofs.F03DirichletCompactJet
import Yau.Proofs.F03DirichletCompactTesting

/-! Genuine bounded source tests for every finite actual directional heat jet. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletCompactHeatJet_test (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget a) (hOΩ : chartInv a '' O ⊆ Ω)
    {l r : ℝ} (hl : 0 < l)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Parabolic.Point n))]
    (hKm : MeasurableSet K)
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (w : List (Parabolic.Point n)) {φ : Parabolic.Point n → ℝ}
    (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) (hφK : tsupport φ ⊆ K)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    compactTestFunctional K (volume.comap ((↑) : K → Parabolic.Point n))
      (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
      (dirichletCompactHeatJet g hK μ hμ Ω hΩ a K hKQ w f) =
    (-1 : ℝ)^w.length * dirichletChartTestOperator g μ hμ Ω hΩ.measurableSet a
      (subset_closure.trans hOt)
      (scalarChart_densityInverseTest g a (subset_closure.trans hOt)
        (test_directionalWordDerivative hφ w.reverse)) f := by
  let F := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f
  let D := {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)
  have hD : IsOpen D := (dirichletChartInterior_open Ω hΩ a).prod isOpen_Ioi
  have hFD : ContDiffOn ℝ ∞ F D := dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a f
  have hFK : ContinuousOn F K := hFD.continuousOn.mono hKQ
  have hJK : ContinuousOn (directionalWordDerivative F w) K :=
    (directionalWordDerivative_contDiffOn hD hFD w).continuousOn.mono hKQ
  change compactTestFunctional K (volume.comap ((↑) : K → Parabolic.Point n))
    (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
    (compactContinuousRestriction K (directionalWordDerivative F w) hJK) = _
  rw [compactTestFunctional_restrict_apply (volume : Measure (Parabolic.Point n)) K hKm
    φ (directionalWordDerivative F w) hφ.1.continuous.continuousOn hJK]
  have hφw := test_directionalWordDerivative hφ w.reverse
  have hφwK : tsupport (directionalWordDerivative φ w.reverse) ⊆ K :=
    (directionalWordDerivative_tsupport_subset φ w.reverse).trans hφK
  have hB := dirichletCompactHeatValue_test g hK μ hμ Ω hΩ a hO hOc hOt hOΩ hl K
    hKm hKQ hφw hφwK f
  change compactTestFunctional K (volume.comap ((↑) : K → Parabolic.Point n))
    (compactContinuousRestriction K (directionalWordDerivative φ w.reverse) hφw.1.continuous.continuousOn)
    (compactContinuousRestriction K F hFK) = _ at hB
  rw [compactTestFunctional_restrict_apply (volume : Measure (Parabolic.Point n)) K hKm
    (directionalWordDerivative φ w.reverse) F hφw.1.continuous.continuousOn hFK] at hB
  have hFQ : ContDiffOn ℝ ∞ F (O ×ˢ Set.Ioo l r) := hFD.mono (by
    intro p hp
    exact ⟨⟨(subset_closure.trans hOt) hp.1,hOΩ ⟨p.1,hp.1,rfl⟩⟩,hl.trans hp.2.1⟩)
  have hLeft : (∫ p in K, directionalWordDerivative F w p * φ p) =
      ∫ p, directionalWordDerivative F w p * φ p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφK hs)),mul_zero]
  have hRight : (∫ p in K, F p * directionalWordDerivative φ w.reverse p) =
      ∫ p, F p * directionalWordDerivative φ w.reverse p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφwK hs)),mul_zero]
  rw [hLeft,directionalWordDerivative_test_integral (hO.prod isOpen_Ioo) hFQ w hφ,← hRight,hB]

end Yau.Proofs.F03Aux
