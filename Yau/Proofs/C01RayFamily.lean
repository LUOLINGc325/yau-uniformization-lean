import Yau.Proofs.C01WeightedVariation
import Yau.Proofs.C01StaticEnergyDensity
import Yau.Proofs.C01PathEnergyCongruence

/-! Actual rays in a genuine local path variation have the required
regularity and nonnegative energy Hessian when their endpoints are fixed. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

def rayParameterDomain (U : Set (ComplexVector n)) (w : ComplexVector n) : Set ℝ :=
  (fun r : ℝ => r • w) ⁻¹' U

theorem rayParameterDomain_isOpen (U : Set (ComplexVector n)) (hU : IsOpen U)
    (w : ComplexVector n) : IsOpen (rayParameterDomain U w) :=
  hU.preimage (continuous_id.smul continuous_const)

theorem rayParameterDomain_zero_mem (U : Set (ComplexVector n)) (hzero : (0 : ComplexVector n) ∈ U)
    (w : ComplexVector n) : (0 : ℝ) ∈ rayParameterDomain U w := by
  simpa only [rayParameterDomain, Set.mem_preimage, zero_smul] using hzero

theorem rayFamily_contMDiffOn
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (w : ComplexVector n) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ℝ => A p.2 (p.1 • w)) (rayParameterDomain U w ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hA
  have harg : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (p.2, p.1 • w))
      (rayParameterDomain U w ×ˢ J) :=
    contDiffOn_snd.prodMk (contDiffOn_fst.smul contDiffOn_const)
  exact hA.comp (harg.fst.contMDiffOn.prodMk harg.snd.contMDiffOn)
    (fun p hp => ⟨hp.2, hp.1⟩)

theorem actualEnergy_secondVariation_nonneg_on_open_unit
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : ℝ → ℝ → M.Carrier) (U J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hzero : (0 : ℝ) ∈ U) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J)
    (q y : M.Carrier) (hends : ∀ r ∈ U, F r 0 = q ∧ F r 1 = y)
    (hE : actualPathEnergy k (F 0) = inducedDistance k q y ^ 2) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ J) →
    0 ≤ deriv (deriv (fun r => actualPathEnergy k (F r))) 0 := by
  letI := manifold_realSmooth M
  intro hF
  have hreg : ContDiffAt ℝ 2 (fun r => actualPathEnergy k (F r)) 0 :=
    (staticPathEnergy_contDiffOn_two k hk F U J hU hJ hunit hF).contDiffAt (hU.mem_nhds hzero)
  apply second_derivative_nonneg_of_localMin _ hreg
  filter_upwards [hU.mem_nhds hzero] with r hr
  have harg : ContDiffOn ℝ 3 (fun u : ℝ => (r, u)) J := contDiffOn_const.prodMk contDiffOn_id
  have hSlice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (F r) J :=
    (hF.comp harg.contMDiffOn (fun u hu => ⟨hr, hu⟩)).of_le (by norm_num)
  have H := distance_sq_le_actualPathEnergy_on_open_unit k hk (F r) J hJ hunit hSlice
  rw [hE]
  rwa [(hends r hr).1, (hends r hr).2] at H

end Yau.NodeProofs.C01Aux
