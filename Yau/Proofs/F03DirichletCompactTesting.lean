import Yau.Proofs.F03DirichletCompactValue
import Yau.Proofs.F03DirichletClassicalPairing

/-! The actual compact value map tested by genuine bounded source functionals. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Each genuine compact test of the actual compact value map equals the
already constructed bounded heat-test operator on every source. -/
theorem dirichletCompactHeatValue_test (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget a) (hOΩ : chartInv a '' O ⊆ Ω)
    {l r : ℝ} (hl : 0 < l)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Parabolic.Point n))]
    (hKm : MeasurableSet K)
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ)
    (hφK : tsupport φ ⊆ K) (f : Lp ℝ 2 (μ.restrict Ω)) :
    compactTestFunctional K (volume.comap ((↑) : K → Parabolic.Point n))
      (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
      (dirichletCompactHeatValue g hK μ hμ Ω hΩ a K hKQ f) =
    dirichletChartTestOperator g μ hμ Ω hΩ.measurableSet a (subset_closure.trans hOt)
      (scalarChart_densityInverseTest g a (subset_closure.trans hOt) hφ) f := by
  let F : Parabolic.Point n → ℝ :=
    fun p => dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.1) p.2
  have hFK : ContinuousOn F K :=
    (dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f a).continuousOn.mono hKQ
  change compactTestFunctional K (volume.comap ((↑) : K → Parabolic.Point n))
    (compactContinuousRestriction K φ hφ.1.continuous.continuousOn)
    (compactContinuousRestriction K F hFK) = _
  rw [compactTestFunctional_restrict_apply (volume : Measure (Parabolic.Point n)) K hKm
    φ F hφ.1.continuous.continuousOn hFK]
  symm
  rw [dirichletClassicalHeat_testOperator g hK μ hμ Ω hΩ a hO hOc hOt hl hφ f]
  let Q := O ×ˢ Set.Ioo l r
  have hFQ : ContinuousOn F Q := (dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f a).continuousOn.mono (by
    intro p hp
    exact ⟨⟨(subset_closure.trans hOt) hp.1,hOΩ ⟨p.1,hp.1,rfl⟩⟩,hl.trans hp.2.1⟩)
  have hPc : Continuous (fun p : Parabolic.Point n => φ p * F p) :=
    continuous_mul_of_continuousAt_tsupport hφ.1.continuous (fun p hp =>
      hFQ.continuousAt ((hO.prod isOpen_Ioo).mem_nhds (hφ.2.2 hp)))
  have hPi : Integrable (fun p : Parabolic.Point n => φ p * F p)
      (volume : Measure (Parabolic.Point n)) :=
    hPc.integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hi : Integrable (fun p : Parabolic.Point n => F p * φ p) := by
    convert hPi using 1
    funext p
    ring
  have hProd : Integrable (fun p : Parabolic.Point n => F p * φ p)
      ((volume.restrict O).prod (volume.restrict (Set.Ioo l r))) := by
    change Integrable (fun p : Parabolic.Point n => F p * φ p)
      (Parabolic.productVolume O (Set.Ioo l r))
    rw [LeafProofs.L16Aux.productVolume_eq_restrict]
    exact hi.restrict
  change (∫ t in Set.Ioo l r, ∫ z in O, F (z,t) * φ (z,t)) = ∫ p in K, F p * φ p
  rw [← integral_prod_symm _ hProd]
  change (∫ p, F p * φ p ∂Parabolic.productVolume O (Set.Ioo l r)) = _
  rw [LeafProofs.L16Aux.productVolume_eq_restrict]
  have hQInt : (∫ p in Q, F p * φ p) = ∫ p, F p * φ p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφ.2.2 hs)),mul_zero]
  have hKInt : (∫ p in K, F p * φ p) = ∫ p, F p * φ p := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hp (hφK hs)),mul_zero]
  rw [hQInt,hKInt]

end Yau.Proofs.F03Aux
