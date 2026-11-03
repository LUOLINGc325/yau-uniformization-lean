import Yau.LeafProofs.L23DistanceEnergyActualVariation
import Yau.LeafProofs.L23DistanceEnergyDirections

/-! The actual manifold ray energy is twice differentiable by compact density integration. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem parameterDirection_eq_deriv {F : ℝ × ℝ → ℝ} {r u : ℝ}
    (hF : DifferentiableAt ℝ F (r,u)) :
    parameterDirection F 1 (r,u)=deriv (fun s => F (s,u)) r := by
  exact (parameterDerivative_hasFDerivAt F (p := (r,u)) hF).hasDerivAt.deriv.symm

theorem parameterDirection_second_eq_deriv {F : ℝ × ℝ → ℝ} {r u : ℝ}
    (hF : ContDiffAt ℝ 2 F (r,u)) :
    parameterDirection (parameterDirection F 1) 1 (r,u)=deriv (deriv (fun s => F (s,u))) r := by
  have heq : parameterDirection F 1=mapDirection F (1,0) := by
    funext p
    rfl
  have heq₂ : parameterDirection (parameterDirection F 1) 1 (r,u)=
      mapDirection (mapDirection F (1,0)) (1,0) (r,u) := by
    rw [heq]
    rfl
  rw [heq₂]
  exact mapDirection_fst_second_eq_deriv F hF

theorem rayEnergyDensity_contDiffOn_two (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (hJ : IsOpen J) (hU : IsOpen U) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => fieldPathSpeed h (fun s => A s (p.1 • w)) p.2^2)
      (((fun r : ℝ => r • w) ⁻¹' U) ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hA
  let V := (fun r : ℝ => r • w) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have HM : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ℝ × ℝ => (p.2,p.1 • w)) (V ×ˢ J) :=
    contDiffOn_snd.contMDiffOn.prodMk ((contDiffOn_fst.smul contDiffOn_const).contMDiffOn)
  have HF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ℝ => A p.2 (p.1 • w)) (V ×ˢ J) :=
    hA.comp HM (fun _ hp => ⟨hp.2,hp.1⟩)
  have hStatic : MetricFamilySmooth (fun _ : ℝ => h) Set.univ := by
    intro c i j
    exact (hh c i j).comp contDiffOn_fst (fun _ hp => hp.1)
  have HD := familyPathEnergyDensity_contDiffOn_two (fun _ : ℝ => h) Set.univ isOpen_univ
    hStatic (fun r s => A s (r • w)) V J hV hJ HF
  exact HD.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
    (fun _ hp => ⟨⟨hp.1,Set.mem_univ (0 : ℝ)⟩,hp.2⟩)

theorem rayEnergy_secondDeriv_eq_integral (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (hJ : IsOpen J) (hU : IsOpen U) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ComplexVector n)∈U) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathEnergy h (fun u => A u (r • w)))) 0=
      ∫ u in Set.Icc (0 : ℝ) 1,
        deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)) 0 := by
  letI := manifold_realSmooth M
  intro hA
  let V := (fun r : ℝ => r • w) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have h0 : (0 : ℝ)∈V := by simpa only [V,Set.mem_preimage,zero_smul] using hzero
  let F : ℝ × ℝ → ℝ := fun p => fieldPathSpeed h (fun s => A s (p.1 • w)) p.2^2
  have HF : ContDiffOn ℝ 2 F (V ×ˢ J) := rayEnergyDensity_contDiffOn_two h hh A J U hJ hU w hA
  have H := unitIntegral_secondDirection hV hJ hunit HF h0 1 1
  change deriv (deriv (fun r : ℝ => fieldPathEnergy h (fun u => A u (r • w)))) 0=
    ∫ u in Set.Icc (0 : ℝ) 1, parameterDirection (parameterDirection F 1) 1 (0,u) at H
  rw [H]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact parameterDirection_second_eq_deriv (HF.contDiffAt ((hV.prod hJ).mem_nhds ⟨h0,hunit hu⟩))

theorem rayEnergy_secondDensity_integrableOn (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (hJ : IsOpen J) (hU : IsOpen U) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ComplexVector n)∈U) (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    IntegrableOn (fun u => deriv (deriv (fun r : ℝ => fieldPathSpeed h
      (fun s => A s (r • w)) u^2)) 0) (Set.Icc (0 : ℝ) 1) := by
  letI := manifold_realSmooth M
  intro hA
  let V := (fun r : ℝ => r • w) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have h0 : (0 : ℝ)∈V := by simpa only [V,Set.mem_preimage,zero_smul] using hzero
  let F : ℝ × ℝ → ℝ := fun p => fieldPathSpeed h (fun s => A s (p.1 • w)) p.2^2
  have HF : ContDiffOn ℝ 2 F (V ×ˢ J) := rayEnergyDensity_contDiffOn_two h hh A J U hJ hU w hA
  have HD := parameterDirection_contDiffOn hV hJ 0 (parameterDirection_contDiffOn hV hJ 1 HF 1) 1
  have HC : ContinuousOn (fun u => parameterDirection (parameterDirection F 1) 1 (0,u))
      (Set.Icc (0 : ℝ) 1) := HD.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨h0,hunit hu⟩)
  have HE : ContinuousOn (fun u => deriv (deriv (fun r : ℝ => fieldPathSpeed h
      (fun s => A s (r • w)) u^2)) 0) (Set.Icc (0 : ℝ) 1) := by
    apply HC.congr
    intro u hu
    exact (parameterDirection_second_eq_deriv (HF.contDiffAt
      ((hV.prod hJ).mem_nhds ⟨h0,hunit hu⟩))).symm
  exact HE.integrableOn_Icc

end Yau.LeafProofs.L23Aux
