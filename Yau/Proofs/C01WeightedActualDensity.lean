import Yau.Proofs.C01WeightedChartVariation
import Yau.Proofs.C01VariationChartDensity

/-! The actual manifold path-energy density has the computed weighted second variation in actual coordinates. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem weighted_actual_density_second_derivative
    (k : HermitianField M) (hk : MetricSmooth k)
    (F : ℝ → ℝ → M.Carrier) (γ : ℝ → M.Carrier)
    (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J) (hzero : (0 : ℝ) ∈ I)
    (hbase : ∀ s ∈ J, F 0 s = γ s)
    (φ : ℝ → ℝ) (b u : ℝ) (hu : u ∈ J) (c : M.Carrier)
    (hc : γ u ∈ (chartAt (ComplexVector n) c).source)
    (P : ℝ → ComplexVector n) (hφ : HasDerivAt φ b u)
    (hFirst : ∀ᶠ s in 𝓝 u,
      HasDerivAt (fun r : ℝ => chartPt c (F r s)) (φ s • P s) 0)
    (hSecond : ∀ᶠ s in 𝓝 u,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (F r s)))
        (-chartChristoffelBilin k c (chartPt c (γ s)) (φ s • P s) (φ s • P s)) 0)
    (hParallel : HasDerivAt P
      (-chartChristoffelBilin k c (chartPt c (γ u))
        (deriv (fun s => chartPt c (γ s)) u) (P u)) u) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (I ×ˢ J) →
    deriv (deriv (fun r => actualPathSpeed k (F r) u ^ 2)) 0 =
      2 * realMetricInChart k c (chartPt c (γ u)) (b • P u) (b • P u) +
      2 * realMetricInChart k c (chartPt c (γ u)) (deriv (fun s => chartPt c (γ s)) u)
        (connectionCurvature (chartChristoffelBilin k c) (chartPt c (γ u))
          (φ u • P u) (deriv (fun s => chartPt c (γ s)) u) (φ u • P u)) := by
  letI := manifold_realSmooth M
  intro hF
  let Z : ℝ × ℝ → ComplexVector n := fun p => chartPt c (F p.1 p.2)
  have hc0 : F 0 u ∈ (chartAt (ComplexVector n) c).source := by rw [hbase u hu]; exact hc
  have hZ : ContDiffAt ℝ 3 Z (0, u) :=
    pathFamily_chart_contDiffAt F I J hI hJ 0 u hzero hu c hc0 hF
  have hZ0 : Z (0, u) = chartPt c (γ u) := congrArg (chartPt c) (hbase u hu)
  have hz : Z (0, u) ∈ chartTarget c := by
    rw [hZ0]
    exact (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  have hnearZ : ∀ᶠ s in 𝓝 u, ContDiffAt ℝ 2 Z (0, s) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      ((hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).eventually (by norm_num))
  have hJEq : (fun s => mapDirection Z (1, 0) (0, s)) =ᶠ[𝓝 u] (fun s => φ s • P s) := by
    filter_upwards [hFirst, hnearZ] with s hs hsZ
    exact (mapDirection_fst_eq_deriv Z (hsZ.differentiableAt (by norm_num))).trans hs.deriv
  have hγEq : (fun s => Z (0, s)) =ᶠ[𝓝 u] (fun s => chartPt c (γ s)) := by
    filter_upwards [hJ.mem_nhds hu] with s hs
    exact congrArg (chartPt c) (hbase s hs)
  have hT : mapDirection Z (0, 1) (0, u) = deriv (fun s => chartPt c (γ s)) u := by
    rw [mapDirection_snd_eq_deriv Z (hZ.differentiableAt (by norm_num)), hγEq.deriv_eq]
  have hP : HasDerivAt P
      (-chartChristoffelBilin k c (Z (0, u)) (mapDirection Z (0, 1) (0, u)) (P u)) u := by
    rw [hZ0, hT]
    exact hParallel
  have hRadial : ∀ᶠ s in 𝓝 u, deriv (deriv (fun r => Z (r, s))) 0 =
      -chartChristoffelBilin k c (Z (0, s)) (mapDirection Z (1, 0) (0, s))
        (mapDirection Z (1, 0) (0, s)) := by
    filter_upwards [hSecond, hJEq, hJ.mem_nhds hu] with s hs hsJ hsI
    rw [hsJ]
    simpa only [Z, hbase s hsI] using hs.deriv
  have hVar := weighted_chart_energy_second_derivative k hk c Z u hz hZ P φ b hP hφ hJEq hRadial
  have heq := actualFamilyDensity_chart_eventuallyEq k F I J hI hJ 0 u hzero hu c hc0 hF
  have heqR : (fun r => actualPathSpeed k (F r) u ^ 2) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => realMetricInChart k c (Z (r, u))
        (mapDirection Z (0, 1) (r, u)) (mapDirection Z (0, 1) (r, u))) :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds heq
  rw [heqR.deriv.deriv_eq]
  simpa only [hZ0, hT] using hVar

end Yau.NodeProofs.C01Aux
