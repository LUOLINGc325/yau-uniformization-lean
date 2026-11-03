import Yau.Proofs.F01GlobalPotentialCompactness

/-! Inside the spatial interior, closed-cylinder within-jets agree with
open-spatial-cylinder jets at every closed time face. Uniform convergence
of the actual jets therefore passes to the open chart core. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iterated_jet_cylinder_restriction
    {U S : Set E} {I : Set ℝ} (hU : IsOpen U) (hUS : U ⊆ S)
    (f : E × ℝ → F) (k : ℕ) {p : E × ℝ} (hp : p ∈ U ×ˢ I) :
    iteratedFDerivWithin ℝ k f (S ×ˢ I) p = iteratedFDerivWithin ℝ k f (U ×ˢ I) p := by
  have hset : (S ×ˢ I) =ᶠ[𝓝 p] (U ×ˢ I) := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp.1] with q hq
    apply propext
    exact ⟨fun h => ⟨hq, h.2⟩, fun h => ⟨hUS h.1, h.2⟩⟩
  exact iteratedFDerivWithin_congr_set hset k

theorem uniform_jets_on_open_cylinder_core
    {U S : Set E} {I : Set ℝ} (hU : IsOpen U) (hUS : U ⊆ S)
    (f : ℕ → E × ℝ → F) (g : E × ℝ → F) (k : ℕ)
    (hconv : TendstoUniformlyOn (fun m p => iteratedFDerivWithin ℝ k (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ k g (S ×ˢ I)) atTop (S ×ˢ I)) :
    TendstoUniformlyOn (fun m p => iteratedFDerivWithin ℝ k (f m) (U ×ˢ I) p)
      (iteratedFDerivWithin ℝ k g (U ×ˢ I)) atTop (U ×ˢ I) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) ε hε] with m hm
  intro p hp
  have h := hm p ⟨hUS hp.1, hp.2⟩
  rwa [iterated_jet_cylinder_restriction hU hUS g k hp,
    iterated_jet_cylinder_restriction hU hUS (f m) k hp] at h

end Yau.NodeProofs.F01Aux
