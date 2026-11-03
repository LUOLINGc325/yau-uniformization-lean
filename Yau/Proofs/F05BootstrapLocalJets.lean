import Yau.Proofs.F05BootstrapDefinitions

/-! On an open buffered spatial neighborhood, changing the artificial
outer spatial set preserves the computed one-sided jets on the physical set. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_local_domain_jets {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hV : IsOpen V)
    (hVX : H ∩ V ⊆ X) {v : Point n → ℝ} (hv : F05RelC2 X I v)
    {z : Point n} (hz : z ∈ (H ∩ V) ×ˢ I) :
    F05RelD H v z = F05RelD X v z ∧ F05RelDD H v z = F05RelDD X v z := by
  have hNear (x : Space n) (hx : x ∈ H ∩ V) : X ∈ 𝓝[H] x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx.2)] with y hyH hyV
    exact hVX ⟨hyH,hyV⟩
  have hD (p : Point n) (hp : p ∈ (H ∩ V) ×ˢ I) : F05RelD H v p = F05RelD X v p :=
    fderivWithin_of_mem_nhdsWithin (hNear p.1 hp.1) (hH p.1 hp.1.1)
      ((hv.2.2.2.2.1 p.2 hp.2 p.1 (hVX hp.1)).differentiableWithinAt (by norm_num))
  refine ⟨hD z hz,?_⟩
  have hFirstNear : (fun x => F05RelD H v (x,z.2)) =ᶠ[𝓝[H] z.1]
      (fun x => F05RelD X v (x,z.2)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hz.1.2)] with x hxH hxV
    exact hD (x,z.2) ⟨⟨hxH,hxV⟩,hz.2⟩
  rw [F05RelDD,hFirstNear.fderivWithin_eq (hD z hz)]
  exact fderivWithin_of_mem_nhdsWithin (hNear z.1 hz.1) (hH z.1 hz.1.1)
    (((hv.2.2.2.2.1 z.2 hz.2).fderivWithin hX (m := 1)
      (by norm_num)).differentiableOn (by norm_num) z.1 (hVX hz.1))

end Yau.Proofs.F05Aux
