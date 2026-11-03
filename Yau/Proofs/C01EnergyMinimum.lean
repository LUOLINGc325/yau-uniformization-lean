import Yau.Proofs.C01FamilyPathEnergy
import Yau.Proofs.C01SecondVariationSign

/-! An actual fixed-endpoint minimizing path gives a genuine local
minimum of its actual energy, and hence nonnegative second variation. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_constant
    (k : HermitianField M) (hk : MetricSmooth k) (I : Set ℝ) :
    MetricFamilySmooth (fun _ : ℝ => k) I := by
  intro c i j
  exact (hk c i j).comp contDiffOn_fst (fun p hp => hp.1)

theorem staticPathEnergy_contDiffOn_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ J) →
    ContDiffOn ℝ 2 (fun v => actualPathEnergy k (F v)) U := by
  letI := manifold_realSmooth M
  intro hF
  have H := familyActualPathEnergy_contDiffOn_two (fun _ : ℝ => k) Set.univ isOpen_univ
    (metricFamilySmooth_constant k hk Set.univ) F U J hU hJ hunit hF
  have harg : ContDiffOn ℝ 2 (fun v : E => (v, (0 : ℝ))) U :=
    contDiffOn_id.prodMk contDiffOn_const
  exact H.comp harg (fun v hv => ⟨hv, Set.mem_univ _⟩)

theorem actualEnergy_secondVariation_nonneg
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : ℝ → ℝ → M.Carrier) (U : Set ℝ) (hU : IsOpen U) (hzero : (0 : ℝ) ∈ U)
    (q y : M.Carrier)
    (hends : ∀ r ∈ U, F r 0 = q ∧ F r 1 = y)
    (hE : actualPathEnergy k (F 0) = inducedDistance k q y ^ 2) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (U ×ˢ Set.univ) →
    0 ≤ deriv (deriv (fun r => actualPathEnergy k (F r))) 0 := by
  letI := manifold_realSmooth M
  intro hF
  have hreg : ContDiffAt ℝ 2 (fun r => actualPathEnergy k (F r)) 0 :=
    (staticPathEnergy_contDiffOn_two k hk F U Set.univ hU isOpen_univ
      (Set.subset_univ _) hF).contDiffAt (hU.mem_nhds hzero)
  apply second_derivative_nonneg_of_localMin _ hreg
  filter_upwards [hU.mem_nhds hzero] with r hr
  have harg : ContDiff ℝ 3 (fun u : ℝ => (r, u)) := contDiff_const.prodMk contDiff_id
  have hSlice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 (F r) Set.univ :=
    hF.comp harg.contMDiff.contMDiffOn (fun u _ => ⟨hr, Set.mem_univ _⟩)
  have hpath : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (F r) :=
    (contMDiffOn_univ.mp hSlice).of_le (by norm_num)
  rw [hE]
  have H := distance_sq_le_actualPathEnergy k hk (F r) hpath
  rwa [(hends r hr).1, (hends r hr).2] at H

end Yau.NodeProofs.C01Aux
