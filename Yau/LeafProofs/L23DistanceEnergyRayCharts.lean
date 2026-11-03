import Yau.LeafProofs.L23DistanceEnergyParameterJets
import Yau.LeafProofs.L23LocalDistanceSupportEnergyDensity

/-! The actual manifold path-family density equals its fixed-chart expression locally. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {n : ℕ} {M : ComplexManifold n}

theorem rayVariation_contMDiffAt (A : ℝ → ComplexVector n → M.Carrier)
    (J : Set ℝ) (U : Set (ComplexVector n)) (hJ : IsOpen J) (hU : IsOpen U)
    (w : ComplexVector n) (r u : ℝ) (hu : u∈J) (hr : r • w∈U) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ℝ => A p.2 (p.1 • w)) (r,u) := by
  letI := manifold_realSmooth M
  intro hA
  have hAA := (hA (u,r • w) ⟨hu,hr⟩).contMDiffAt ((hJ.prod hU).mem_nhds ⟨hu,hr⟩)
  have hm : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => (p.2,p.1 • w)) (r,u) :=
    contDiffAt_snd.prodMk (contDiffAt_fst.smul contDiffAt_const)
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ℝ × ℝ => (p.2,p.1 • w)) (r,u) :=
    hm.fst.contMDiffAt.prodMk hm.snd.contMDiffAt
  exact hAA.comp (r,u) hmap

theorem rayVariation_chart_contDiffAt (A : ℝ → ComplexVector n → M.Carrier)
    (J : Set ℝ) (U : Set (ComplexVector n)) (hJ : IsOpen J) (hU : IsOpen U)
    (w : ComplexVector n) (r u : ℝ) (hu : u∈J) (hr : r • w∈U)
    (c : M.Carrier) (hc : A u (r • w)∈(chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ContDiffAt ℝ 3 (fun p : ℝ × ℝ => chartPt c (A p.2 (p.1 • w))) (r,u) := by
  letI := manifold_realSmooth M
  intro hA
  have hAc := rayVariation_contMDiffAt A J U hJ hU w r u hu hr hA
  have hC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt c) (A u (r • w)) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3)
      (x := c) (x' := A u (r • w)) hc) using 1
  exact (hC.comp (r,u) hAc).contDiffAt

theorem rayEnergyDensity_chart_eventuallyEq (h : HermitianField M)
    (A : ℝ → ComplexVector n → M.Carrier)
    (J : Set ℝ) (U : Set (ComplexVector n)) (hJ : IsOpen J) (hU : IsOpen U)
    (w : ComplexVector n) (u : ℝ) (hu : u∈J) (hzero : (0 : ComplexVector n)∈U)
    (c : M.Carrier) (hc : A u 0∈(chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    (fun p : ℝ × ℝ => fieldPathSpeed h (fun s => A s (p.1 • w)) p.2^2)=ᶠ[𝓝 (0,u)]
      (fun p => realMetricInChart h c (chartPt c (A p.2 (p.1 • w)))
        (mapDirection (fun q : ℝ × ℝ => chartPt c (A q.2 (q.1 • w))) (0,1) p)
        (mapDirection (fun q : ℝ × ℝ => chartPt c (A q.2 (q.1 • w))) (0,1) p)) := by
  letI := manifold_realSmooth M
  intro hA
  have hzero' : (0 : ℝ) • w∈U := by simpa only [zero_smul] using hzero
  have hcont := (rayVariation_contMDiffAt A J U hJ hU w 0 u hu hzero' hA).continuousAt
  have hsrc : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,u), A p.2 (p.1 • w)∈(chartAt (ComplexVector n) c).source := by
    apply hcont.preimage_mem_nhds
    simpa only [zero_smul] using (chartAt (ComplexVector n) c).open_source.mem_nhds hc
  have hdom : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,u), (p.2,p.1 • w)∈J ×ˢ U :=
    (continuousAt_snd.prodMk (continuousAt_fst.smul continuousAt_const)).preimage_mem_nhds
      ((hJ.prod hU).mem_nhds ⟨hu,hzero'⟩)
  filter_upwards [hsrc,hdom] with p hp hs
  have hAA := (hA (p.2,p.1 • w) hs).contMDiffAt ((hJ.prod hU).mem_nhds hs)
  have hm : ContDiffAt ℝ 3 (fun s : ℝ => (s,p.1 • w)) p.2 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun s : ℝ => (s,p.1 • w)) p.2 := hm.fst.contMDiffAt.prodMk hm.snd.contMDiffAt
  have hFiber : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (fun s => A s (p.1 • w)) p.2 :=
    (hAA.comp p.2 hmap).mdifferentiableAt (by norm_num : (3 : ℕ∞ω)≠0)
  have hZ := rayVariation_chart_contDiffAt A J U hJ hU w p.1 p.2 hs.1 hs.2 c hp hA
  have hD := (hZ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact fieldPathSpeed_sq_eq_chartDerivative h _ c p.2 hp _ hFiber hD

end Yau.LeafProofs.L23Aux
