import Yau.Proofs.C01FamilyPathEnergyDensity
import Yau.Proofs.C01VariationSaturation

/-! Actual path energy depends only on the path germs along the unit
interval. Smooth saturation therefore preserves the exact energy. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem actualPathSpeed_sq_congr_eventuallyEq
    (k : HermitianField M) (γ β : ℝ → M.Carrier) (t : ℝ) (heq : γ =ᶠ[𝓝 t] β) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    actualPathSpeed k γ t ^ 2 = actualPathSpeed k β t ^ 2 := by
  letI := manifold_realSmooth M
  intro hγ hβ
  let c := γ t
  have hγc : γ t ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hβc : β t ∈ (chartAt (ComplexVector n) c).source := by rw [← heq.self_of_nhds]; exact hγc
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (γ t) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1)
      (x := c) (x' := γ t) hγc) using 1
  have HD := ((HC.comp t hγ).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have HDβ := HD.congr_of_eventuallyEq ((heq.fun_comp (chartPt c)).symm)
  rw [actualPathSpeed_sq_eq_chartDerivative k γ c t hγc _ (hγ.mdifferentiableAt (by norm_num)) HD,
    actualPathSpeed_sq_eq_chartDerivative k β c t hβc _ (hβ.mdifferentiableAt (by norm_num)) HDβ,
    heq.self_of_nhds]

theorem actualPathEnergy_congr_unit_germs
    (k : HermitianField M) (γ β : ℝ → M.Carrier)
    (heq : ∀ u ∈ Set.Icc (0 : ℝ) 1, γ =ᶠ[𝓝 u] β) :
    letI := manifold_realSmooth M
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u) →
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β u) →
    actualPathEnergy k γ = actualPathEnergy k β := by
  letI := manifold_realSmooth M
  intro hγ hβ
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact actualPathSpeed_sq_congr_eventuallyEq k γ β u (heq u hu) (hγ u hu) (hβ u hu)

theorem distance_sq_le_actualPathEnergy_on_open_unit
    (k : HermitianField M) (hk : MetricSmooth k) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ J →
    inducedDistance k (γ 0) (γ 1) ^ 2 ≤ actualPathEnergy k γ := by
  letI := manifold_realSmooth M
  intro hγ
  obtain ⟨χ, hχ, hmap, heq⟩ := exists_smooth_saturation_into_open_unit J hJ hunit
  let β := fun u => γ (χ u)
  have hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β :=
    contMDiffOn_univ.mp (hγ.comp ((hχ.of_le (by simp)).contMDiff.contMDiffOn) hmap)
  have hnear (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : γ =ᶠ[𝓝 u] β := by
    filter_upwards [heq u hu] with v hv
    change γ v = γ (χ v)
    rw [hv]
    rfl
  have HE : actualPathEnergy k γ = actualPathEnergy k β :=
    actualPathEnergy_congr_unit_germs k γ β hnear
      (fun u hu => (hγ u (hunit hu)).contMDiffAt (hJ.mem_nhds (hunit hu)))
      (fun u _ => hβ u)
  have H := distance_sq_le_actualPathEnergy k hk β hβ
  have hβ0 : β 0 = γ 0 := (hnear 0 (by norm_num)).self_of_nhds.symm
  have hβ1 : β 1 = γ 1 := (hnear 1 (by norm_num)).self_of_nhds.symm
  rwa [hβ0, hβ1, ← HE] at H

end Yau.NodeProofs.C01Aux
