import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientDensity

/-! Genuine first density variations integrate to the first derivative of the original path energy. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

def staticPathEnergyDensity (h : HermitianField M) (A : ℝ → ComplexVector n → M.Carrier)
    (p : ComplexVector n × ℝ) : ℝ := fieldPathSpeed h (fun u => A u p.1) p.2 ^ 2

theorem staticPathEnergyDensity_contDiffOn_two
    (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (U : Set (ComplexVector n)) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContDiffOn ℝ 2 (staticPathEnergyDensity h A) (U ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hA
  have Hfam : MetricFamilySmooth (fun _ : ℝ => h) Set.univ := by
    intro c i j
    exact (hh c i j).comp contDiffOn_fst (fun p hp => hp.1)
  have HM : ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ComplexVector n × ℝ => (p.2,p.1)) (U ×ˢ J) :=
    contDiffOn_snd.contMDiffOn.prodMk contDiffOn_fst.contMDiffOn
  have HF : ContMDiffOn 𝓘(ℝ, ComplexVector n × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ComplexVector n × ℝ => A p.2 p.1) (U ×ˢ J) := hA.comp HM (fun p hp => ⟨hp.2,hp.1⟩)
  have HD := familyPathEnergyDensity_contDiffOn_two (fun _ : ℝ => h) Set.univ isOpen_univ Hfam
    (fun v u => A u v) U J hU hJ HF
  have Hembed : ContDiffOn ℝ 2 (fun p : ComplexVector n × ℝ => ((p.1,(0 : ℝ)),p.2)) (U ×ˢ J) :=
    (contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd
  exact HD.comp Hembed (fun p hp => ⟨⟨hp.1,Set.mem_univ _⟩,hp.2⟩)

theorem fieldPathEnergy_hasDerivAt_of_constant_density_firstVariation
    (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (U : Set (ComplexVector n)) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (h0 : (0 : ComplexVector n) ∈ U)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (w : ComplexVector n) (C : ℝ)
    (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u ^ 2) C 0) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    HasDerivAt (fun r : ℝ => fieldPathEnergy h (fun u => A u (r • w))) C 0 := by
  letI := manifold_realSmooth M
  intro hA
  let F := staticPathEnergyDensity h A
  have HF : ContDiffOn ℝ 2 F (U ×ˢ J) := staticPathEnergyDensity_contDiffOn_two h hh A U J hU hJ hA
  have HIntegral := hasFDerivAt_unitIntegral hU hJ hunit (HF.of_le (by norm_num)) h0
  have Hregular : ContinuousOn (fun u => parameterDerivative F (0,u)) (Set.Icc (0 : ℝ) 1) :=
    (parameterDerivative_contDiffOn hU hJ 1 HF).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨h0,hunit hu⟩)
  have HInt : IntegrableOn (fun u => parameterDerivative F (0,u)) (Set.Icc (0 : ℝ) 1) := Hregular.integrableOn_Icc
  have Hvalue (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : parameterDerivative F (0,u) w = C := by
    have Hp : (0,u) ∈ U ×ˢ J := ⟨h0,hunit hu⟩
    have Hdiff : DifferentiableAt ℝ F (0,u) :=
      (HF.contDiffAt ((hU.prod hJ).mem_nhds Hp)).differentiableAt (by norm_num)
    have HFD := parameterDerivative_hasFDerivAt F (p := (0,u)) Hdiff
    have HFD0 : HasFDerivAt (fun v => F (v,u)) (parameterDerivative F (0,u)) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using HFD
    have HL : HasDerivAt (fun r : ℝ => r • w) w 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have HDirection : HasDerivAt (fun r : ℝ => F (r • w,u)) (parameterDerivative F (0,u) w) 0 := by
      convert! HFD0.comp_hasDerivAt 0 HL using 1
    have Hgiven : HasDerivAt (fun r : ℝ => F (r • w,u)) C 0 := hD u hu
    exact HDirection.unique Hgiven
  have Hcoef : (∫ u in Set.Icc (0 : ℝ) 1, parameterDerivative F (0,u)) w = C := by
    rw [ContinuousLinearMap.integral_apply HInt]
    have HE : (∫ u in Set.Icc (0 : ℝ) 1, parameterDerivative F (0,u) w) = ∫ u in Set.Icc (0 : ℝ) 1, C := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact Hvalue u hu
    simpa [integral_const,Measure.real] using HE
  have HF0 : HasFDerivAt (fun v => ∫ u in Set.Icc (0 : ℝ) 1, F (v,u))
      (∫ u in Set.Icc (0 : ℝ) 1, parameterDerivative F (0,u)) ((0 : ℝ) • w) := by
    simpa only [zero_smul] using HIntegral
  have HL : HasDerivAt (fun r : ℝ => r • w) w 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have H := HF0.comp_hasDerivAt 0 HL
  rw [Hcoef] at H
  exact H

end Yau.LeafProofs.L23Aux
