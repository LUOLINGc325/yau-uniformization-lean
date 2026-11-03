import Yau.Proofs.D02LeviCharts

/-! Smooth nonnegative intrinsic Levi forms pull back through the actual
holomorphic map on its open domain. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem smoothLevi_holomorphicPullback {m n : ℕ} {M : ComplexManifold n}
    {D : Set (ComplexVector m)} (hD : IsOpen D)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    (f : ComplexVector m → M.Carrier)
    (hf : ContMDiffOn (ComplexModel m) (ComplexModel n) ∞ f D)
    (z : ComplexVector m) (hz : z ∈ D) :
    ContDiffAt ℝ 2 (fun w => u (f w)) z ∧
      ∀ v, 0 ≤ L22Aux.complexLeviQuadratic (fun w => u (f w)) z v := by
  let y := f z
  let T : ComplexVector m → ComplexVector n := fun w => chartPt y (f w)
  have hfc := hf.contMDiffAt (hD.mem_nhds hz)
  have hTc : ContMDiffAt (ComplexModel m) (ComplexModel n) ∞ T z :=
    (contMDiffAt_extChartAt (I := ComplexModel n) (n := ∞) (x := y)).comp z hfc
  have hT : ContDiffAt ℂ 2 T z := hTc.contDiffAt.of_le (by simp)
  have hTy : T z = chartPt y y := rfl
  have hc : ContDiffAt ℝ 2 (inChart y u) (chartPt y y) :=
    ((hu y).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds
      (mem_extChartAt_target y))).of_le (by simp)
  have hcT : ContDiffAt ℝ 2 (inChart y u) (T z) := hTy.symm ▸ hc
  have hsrc : ∀ᶠ w in 𝓝 z, f w ∈ (extChartAt (ComplexModel n) y).source :=
    hfc.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have he : (fun w => u (f w)) =ᶠ[𝓝 z] ((inChart y u) ∘ T) := by
    filter_upwards [hsrc] with w hw
    exact (congrArg u ((extChartAt (ComplexModel n) y).left_inv hw)).symm
  refine ⟨(hcT.comp z (hT.restrict_scalars ℝ)).congr_of_eventuallyEq he, ?_⟩
  intro v
  have hQ : L22Aux.complexLeviQuadratic (fun w => u (f w)) z v =
      L22Aux.complexLeviQuadratic (inChart y u) (chartPt y y) (fderiv ℂ T z v) := by
    calc
      _ = L22Aux.complexLeviQuadratic ((inChart y u) ∘ T) z v := by
        unfold L22Aux.complexLeviQuadratic
        rw [he.fderiv.fderiv_eq]
      _ = _ := by rw [L22Aux.complexLeviQuadratic_comp hT hcT, hTy]
  rw [hQ]
  exact (L22Aux.leviC_posSemidef_iff hc).mp (hL y) _

end Yau.NodeProofs.D02Aux
