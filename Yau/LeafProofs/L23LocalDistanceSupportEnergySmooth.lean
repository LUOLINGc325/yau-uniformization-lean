import Yau.LeafProofs.L23LocalDistanceSupportEnergyDensity
import Yau.LeafProofs.L23DistanceEnergyIntegral

/-! The original physical path energy is jointly C2 in the endpoint parameter and metric time. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem familyPathEnergy_contDiffOn_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry F) (U ×ˢ J) →
    ContDiffOn ℝ 2 (fun p : E × ℝ => fieldPathEnergy (h p.2) (F p.1)) (U ×ˢ I) := by
  letI := manifold_realSmooth M
  intro hF
  exact contDiffOn_unitIntegral (hU.prod hI) hJ hunit 2
    (familyPathEnergyDensity_contDiffOn_two h I hI hh F U J hU hJ hF)

theorem endpointVariation_chart_family_contMDiffOn_three
    (y : M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ComplexVector n × ℝ => A p.2 (e.symm (chartInv y p.1)))
      ((chartTarget y ∩ (chartInv y) ⁻¹' e.target) ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hA hinv
  let U := chartTarget y ∩ (chartInv y) ⁻¹' e.target
  have HInv : ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3
      (fun v => e.symm (chartInv y v)) U :=
    hinv.comp ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) (n := 3) y).mono (fun v hv => hv.1))
      (fun v hv => hv.2)
  have HF : ContDiffOn ℝ 3 (fun p : ComplexVector n × ℝ => (p.2,e.symm (chartInv y p.1))) (U ×ˢ J) :=
    contDiffOn_snd.prodMk (HInv.contDiffOn.comp contDiffOn_fst (fun p hp => hp.1))
  have HM : ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ComplexVector n × ℝ => (p.2,e.symm (chartInv y p.1))) (U ×ˢ J) :=
    HF.fst.contMDiffOn.prodMk HF.snd.contMDiffOn
  exact hA.comp HM (fun p hp => ⟨hp.2,e.map_target hp.1.2⟩)

theorem endpointParameter_fieldPathEnergy_contDiffOn_two
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ e.source) →
    ContDiffOn ℝ 2 (fun p : ComplexVector n × ℝ => fieldPathEnergy (h p.2) (fun u => A u p.1))
      (e.source ×ˢ I) := by
  letI := manifold_realSmooth M
  intro hA
  have HM : ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ComplexVector n × ℝ => (p.2,p.1)) (e.source ×ˢ J) :=
    (contDiffOn_snd.contMDiffOn).prodMk (contDiffOn_fst.contMDiffOn)
  have HF : ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ComplexVector n × ℝ => A p.2 p.1) (e.source ×ˢ J) :=
    hA.comp HM (fun p hp => ⟨hp.2,hp.1⟩)
  exact familyPathEnergy_contDiffOn_two h I hI hh (fun v u => A u v) e.source J e.open_source hJ hunit HF

theorem endpointVariation_fieldPathEnergy_contDiffOn_two
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (y : M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    ContDiffOn ℝ 2 (fun p : ComplexVector n × ℝ =>
      fieldPathEnergy (h p.2) (fun u => A u (e.symm (chartInv y p.1))))
      ((chartTarget y ∩ (chartInv y) ⁻¹' e.target) ×ˢ I) := by
  letI := manifold_realSmooth M
  intro hA hinv
  have hU : IsOpen (chartTarget y ∩ (chartInv y) ⁻¹' e.target) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) y).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) y) e.open_target
  exact familyPathEnergy_contDiffOn_two h I hI hh
    (fun v u => A u (e.symm (chartInv y v))) _ J hU hJ hunit
    (endpointVariation_chart_family_contMDiffOn_three y e A J hA hinv)

end Yau.LeafProofs.L23Aux
