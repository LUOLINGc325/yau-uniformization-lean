import Yau.LeafProofs.L23LocalDistanceSupportEnergyLaplacianTraceJets

/-! Both actual endpoint energies have the C2 germs required for the physical trace identity. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem endpointVariation_staticEnergy_contDiffAt_two
    (h : HermitianField M) (hh : MetricSmooth h) (y : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    ContDiffAt ℝ 2 (fun v => fieldPathEnergy h (fun u => A u v)) 0 ∧
    ContDiffAt ℝ 2 (inChart y (fun z => fieldPathEnergy h (fun u => A u (e.symm z)))) (chartPt y y) := by
  letI := manifold_realSmooth M
  intro hA hinv
  let J := Set.Ioo (-δ) (1+δ)
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by intro u hu; constructor <;> linarith [hu.1,hu.2]
  have Hfam : MetricFamilySmooth (fun _ : ℝ => h) Set.univ := by
    intro c i j
    exact (hh c i j).comp contDiffOn_fst (fun p hp => hp.1)
  have Hparam := endpointParameter_fieldPathEnergy_contDiffOn_two (fun _ : ℝ => h) Set.univ isOpen_univ Hfam
    e A J isOpen_Ioo hunit hA
  have HparameterPoint : ((0 : ComplexVector n),(0 : ℝ)) ∈ e.source ×ˢ (Set.univ : Set ℝ) := ⟨h0,Set.mem_univ _⟩
  have HparamAt := Hparam.contDiffAt ((e.open_source.prod isOpen_univ).mem_nhds HparameterPoint)
  have HEu : ContDiffAt ℝ 2 (fun v => fieldPathEnergy h (fun u => A u v)) 0 :=
    HparamAt.comp (f := fun v : ComplexVector n => (v,(0 : ℝ)))
      (g := fun p : ComplexVector n × ℝ => fieldPathEnergy h (fun u => A u p.1)) 0
      (show ContDiffAt ℝ 2 (fun v : ComplexVector n => (v,(0 : ℝ))) 0 from
      contDiffAt_id.prodMk contDiffAt_const)
  have Hphysical := endpointVariation_fieldPathEnergy_contDiffOn_two (fun _ : ℝ => h) Set.univ isOpen_univ Hfam
    y e A J isOpen_Ioo hunit hA hinv
  have hU : IsOpen (chartTarget y ∩ (chartInv y) ⁻¹' e.target) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) y).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) y) e.open_target
  have hy : y ∈ e.target := by rw [← he0]; exact e.map_source h0
  have hinvy : chartInv y (chartPt y y) = y := (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hpoint : (chartPt y y,(0 : ℝ)) ∈ (chartTarget y ∩ (chartInv y) ⁻¹' e.target) ×ˢ (Set.univ : Set ℝ) := by
    refine ⟨⟨mem_extChartAt_target _,?_⟩,Set.mem_univ _⟩
    change chartInv y (chartPt y y) ∈ e.target
    rwa [hinvy]
  have HphysicalAt := Hphysical.contDiffAt ((hU.prod isOpen_univ).mem_nhds hpoint)
  refine ⟨HEu,?_⟩
  exact HphysicalAt.comp (f := fun z : ComplexVector n => (z,(0 : ℝ)))
    (g := fun p : ComplexVector n × ℝ => fieldPathEnergy h (fun u => A u (e.symm (chartInv y p.1)))) (chartPt y y)
    (show ContDiffAt ℝ 2 (fun z : ComplexVector n => (z,(0 : ℝ))) (chartPt y y) from
      contDiffAt_id.prodMk contDiffAt_const)

end Yau.LeafProofs.L23Aux
