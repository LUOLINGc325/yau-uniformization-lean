import Yau.LeafProofs.L23LocalDistanceSupportEnergyContact

/-! The exact genuine energy majorant data consumed by the remaining variation estimates. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem endpointVariation_energy_majorant
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (q y : M.Carrier) (t : ℝ) (ht : t ∈ I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (γ : ℝ → M.Carrier)
    (δ : ℝ) (hδ : 0 < δ) (hγ1 : γ 1 = y)
    (hzero : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (hend : ∀ v ∈ e.source, A 0 v = q ∧ A 1 v = e v)
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq (h t) γ u = inducedDistance (h t) q y ^ 2) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Set.Ioo (-δ) (1+δ)) →
    ContDiffAt ℝ 2 (fun p : ComplexVector n × ℝ =>
      fieldPathEnergy (h p.2) (fun u => A u (e.symm (chartInv y p.1)))) (chartPt y y,t) ∧
    fieldPathEnergy (h t) (fun u => A u (e.symm y)) = inducedDistance (h t) q y ^ 2 ∧
    ∀ s ∈ I, ∀ z ∈ e.target, inducedDistance (h s) q z ^ 2 ≤
      fieldPathEnergy (h s) (fun u => A u (e.symm z)) := by
  letI := manifold_realSmooth M
  intro hA hinv hγ
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have Hsmooth := endpointVariation_fieldPathEnergy_contDiffOn_two h I hI hh y e A _ isOpen_Ioo hunit hA hinv
  have hU : IsOpen (chartTarget y ∩ (chartInv y) ⁻¹' e.target) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) y).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) y) e.open_target
  have hy : y ∈ e.target := by rw [← he0]; exact e.map_source hzero
  have hinvy : chartInv y (chartPt y y) = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hpoint : (chartPt y y,t) ∈ (chartTarget y ∩ (chartInv y) ⁻¹' e.target) ×ˢ I := by
    refine ⟨⟨mem_extChartAt_target y,?_⟩,ht⟩
    change chartInv y (chartPt y y) ∈ e.target
    rwa [hinvy]
  refine ⟨Hsmooth.contDiffAt ((hU.prod hI).mem_nhds hpoint),?_,?_⟩
  · have H := endpointVariation_fieldPathEnergy_contact (h t) γ e A δ hδ hzero
      (he0.trans hγ1.symm) hA0 _ hspeed hA hγ
    simpa only [hγ1] using H
  · intro s hs z hz
    exact endpointVariation_inducedDistance_sq_le_energy (h s) (metricFamilySmooth_slice h hh hs)
      q e A δ hδ hend hA z hz

end Yau.LeafProofs.L23Aux
