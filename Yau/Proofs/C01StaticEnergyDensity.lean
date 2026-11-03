import Yau.Proofs.C01EnergyMinimum
import Yau.Proofs.C01SecondDensityContinuity

/-! The actual static path-family density is C2 jointly, and its
actual energy Hessian is the integral of its actual slice Hessians. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def staticPathEnergyDensity {E : Type*} (k : HermitianField M)
    (F : E → ℝ → M.Carrier) (p : E × ℝ) : ℝ := actualPathSpeed k (F p.1) p.2 ^ 2

theorem staticPathEnergyDensity_contDiffOn_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ J) →
    ContDiffOn ℝ 2 (staticPathEnergyDensity k F) (U ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hF
  have H := familyActualPathEnergyDensity_contDiffOn_two (fun _ : ℝ => k) Set.univ isOpen_univ
    (metricFamilySmooth_constant k hk Set.univ) F U J hU hJ hF
  have harg : ContDiffOn ℝ 2 (fun p : E × ℝ => ((p.1, (0 : ℝ)), p.2)) (U ×ˢ J) :=
    (contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd
  exact H.comp harg (fun p hp => ⟨⟨hp.1, Set.mem_univ _⟩, hp.2⟩)

theorem actualPathEnergy_second_derivative_eq_integral
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : ℝ → ℝ → M.Carrier) (U J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (a : ℝ) (ha : a ∈ U) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ J) →
    deriv (deriv (fun r => actualPathEnergy k (F r))) a =
      ∫ u in Set.Icc (0 : ℝ) 1, deriv (deriv (fun r => actualPathSpeed k (F r) u ^ 2)) a := by
  letI := manifold_realSmooth M
  intro hF
  exact scalar_unitIntegral_second_derivative (staticPathEnergyDensity k F) U J hU hJ hunit
    (staticPathEnergyDensity_contDiffOn_two k hk F U J hU hJ hF) a ha

end Yau.NodeProofs.C01Aux
