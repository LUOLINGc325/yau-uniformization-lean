import Yau.Proofs.C01FamilyPathEnergyDensity

/-! The genuine energy density of an actual two-parameter path family
agrees locally with its fixed-chart metric and actual spatial derivative. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pathFamily_chart_contDiffAt
    (F : ℝ → ℝ → M.Carrier) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (r u : ℝ) (hr : r ∈ I) (hu : u ∈ J) (c : M.Carrier)
    (hc : F r u ∈ (chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (I ×ˢ J) →
    ContDiffAt ℝ 3 (fun p : ℝ × ℝ => chartPt c (F p.1 p.2)) (r, u) := by
  letI := manifold_realSmooth M
  intro hF
  have hAt := (hF (r, u) ⟨hr, hu⟩).contMDiffAt ((hI.prod hJ).mem_nhds ⟨hr, hu⟩)
  have hC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3
      (chartPt c) (F r u) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3)
      (x := c) (x' := F r u) hc) using 1
  exact (hC.comp (r, u) hAt).contDiffAt

theorem actualFamilyDensity_chart_eventuallyEq
    (k : HermitianField M) (F : ℝ → ℝ → M.Carrier)
    (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (r u : ℝ) (hr : r ∈ I) (hu : u ∈ J) (c : M.Carrier)
    (hc : F r u ∈ (chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry F) (I ×ˢ J) →
    let Z : ℝ × ℝ → ComplexVector n := fun p => chartPt c (F p.1 p.2)
    (fun p : ℝ × ℝ => actualPathSpeed k (F p.1) p.2 ^ 2) =ᶠ[𝓝 (r, u)]
      (fun p => realMetricInChart k c (Z p) (fderiv ℝ Z p (0, 1)) (fderiv ℝ Z p (0, 1))) := by
  letI := manifold_realSmooth M
  intro hF
  let Z : ℝ × ℝ → ComplexVector n := fun p => chartPt c (F p.1 p.2)
  have hAt := (hF (r, u) ⟨hr, hu⟩).contMDiffAt ((hI.prod hJ).mem_nhds ⟨hr, hu⟩)
  have hsrc : ∀ᶠ p : ℝ × ℝ in 𝓝 (r, u),
      F p.1 p.2 ∈ (chartAt (ComplexVector n) c).source :=
    hAt.continuousAt.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
  filter_upwards [hsrc, (hI.prod hJ).mem_nhds ⟨hr, hu⟩] with p hp hdom
  have hFp := (hF p hdom).contMDiffAt ((hI.prod hJ).mem_nhds hdom)
  have harg : ContDiffAt ℝ 3 (fun s : ℝ => (p.1, s)) p.2 :=
    contDiffAt_const.prodMk contDiffAt_id
  have hFiber : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (F p.1) p.2 :=
    (hFp.comp p.2 harg.contMDiffAt).mdifferentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)
  have hZ := pathFamily_chart_contDiffAt F I J hI hJ p.1 p.2 hdom.1 hdom.2 c hp hF
  have HD := (hZ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact actualPathSpeed_sq_eq_chartDerivative k (F p.1) c p.2 hp _ hFiber HD

end Yau.NodeProofs.C01Aux
