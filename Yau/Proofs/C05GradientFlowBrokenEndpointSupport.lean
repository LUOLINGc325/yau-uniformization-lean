import Yau.Proofs.C05GradientFlowEndpointEnergy
import Yau.Proofs.C05GradientFlowEndpointBranches
import Yau.Proofs.C05GradientFlowEnergySupport

/-! A fixed geodesic and genuine short endpoint branches give a differentiable energy support. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

theorem exists_broken_endpoint_energy_support (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (α β : ℝ → M.Carrier) (t : ℝ) (v w : ComplexVector n)
    (hα0 : α t = p.proj) (hβ0 : β t = (realGeodesicFlow g p 1).proj) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 α t →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    HasDerivAt (fun s => chartPt p.proj (α s)) v t →
    HasDerivAt (fun s => chartPt (realGeodesicFlow g p 1).proj (β s)) w t →
    ∃ E : ℝ → ℝ,
      E t = realTangentEnergy g.form p / 2 ∧
      HasDerivAt E
        (-realChartMomentum g p.proj p v +
          realChartMomentum g (realGeodesicFlow g p 1).proj (realGeodesicFlow g p 1) w) t ∧
      ∀ᶠ s in 𝓝 t, inducedDistance g.form (α s) (β s) ^ 2 ≤ 2 * E s := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hα hβ hv hw
  obtain ⟨s, d, hs, hd, hsd, U₀, U₁, hU₀, hU₁, hpU₀, hqU₁,
    P₀, P₁, hP₀, hP₁, hP₀p, hP₁q, hends₀, hends₁⟩ :=
    exists_geodesic_two_short_endpoint_branches g p
  let e := 1 - s - d
  have he : 0 < e := by dsimp [e]; linarith
  have hT : s + e + d = 1 := by dsimp [e]; ring
  let m := realGeodesicFlow g p s
  let q := realGeodesicFlow g p (1 - d)
  let y := (realGeodesicFlow g p 1).proj
  have hmiddle : realGeodesicFlow g m e = q := by
    dsimp only [m, q]
    rw [← realGeodesicFlow_add]
    congr 1
    dsimp [e]
    ring
  have hterminal : realGeodesicFlow g q d = realGeodesicFlow g p 1 := by
    dsimp only [q]
    rw [← realGeodesicFlow_add]
    congr 1
    ring
  let E₀ := fun u => realSegmentEnergy g s (P₀ (α u, m.proj))
  let E₁ := fun u => realSegmentEnergy g d (P₁ (q.proj, β u))
  let E := fun u => E₀ u + realSegmentEnergy g e m + E₁ u
  have hPt₀ : P₀ (α t, m.proj) = p := by rw [hα0]; exact hP₀p
  have hPt₁ : P₁ (q.proj, β t) = q := by rw [hβ0]; exact hP₁q
  have ht₀ : (α t, m.proj) ∈ U₀ := by rw [hα0]; exact hpU₀
  have ht₁ : (q.proj, β t) ∈ U₁ := by rw [hβ0]; exact hqU₁
  have hD₀ := endpointBranchEnergy_hasDerivAt g s U₀ hU₀ P₀ α (fun _ => m.proj)
    t p.proj m.proj v 0 ht₀ (by rw [hα0]; exact mem_chart_source _ _)
    (mem_chart_source _ _) hP₀ hends₀ hα contMDiffAt_const hv (hasDerivAt_const _ _)
  have hD₁ := endpointBranchEnergy_hasDerivAt g d U₁ hU₁ P₁ (fun _ => q.proj) β
    t q.proj y 0 w ht₁ (mem_chart_source _ _)
    (by rw [hβ0]; exact mem_chart_source _ _) hP₁ hends₁ contMDiffAt_const hβ
      (hasDerivAt_const _ _) hw
  rw [hPt₀] at hD₀
  rw [hPt₁, hterminal] at hD₁
  simp only [map_zero, neg_zero, add_zero, zero_add] at hD₀ hD₁
  refine ⟨E, ?_, (hD₀.add_const _).add hD₁, ?_⟩
  · dsimp only [E, E₀, E₁]
    rw [hPt₀, hPt₁]
    dsimp only [realSegmentEnergy, m, q]
    rw [realGeodesicFlow_energy, realGeodesicFlow_energy]
    have H := congrArg (fun T : ℝ => T * realTangentEnergy g.form p / 2) hT
    nlinarith only [H]
  · have hnear₀ : ∀ᶠ u in 𝓝 t, (α u, m.proj) ∈ U₀ :=
      (hα.continuousAt.prodMk continuousAt_const).eventually (hU₀.mem_nhds ht₀)
    have hnear₁ : ∀ᶠ u in 𝓝 t, (q.proj, β u) ∈ U₁ :=
      (continuousAt_const.prodMk hβ.continuousAt).eventually (hU₁.mem_nhds ht₁)
    filter_upwards [hnear₀, hnear₁] with u hu₀ hu₁
    have h₀ := hends₀ (α u, m.proj) hu₀
    have h₁ := hends₁ (q.proj, β u) hu₁
    have H := distance_sq_le_twice_broken_energy g (P₀ (α u, m.proj)) m
      (P₁ (q.proj, β u)) hs he hd hT h₀.2
        (by rw [hmiddle]; exact h₁.1.symm)
    rw [h₀.1, h₁.2] at H
    exact H

end Yau.Proofs.C05GradientFlowAux
