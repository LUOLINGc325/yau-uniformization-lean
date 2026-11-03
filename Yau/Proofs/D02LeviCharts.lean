import Yau.Proofs.D02ImmersionLevi

/-! Intrinsic Levi positivity transports to every point of every valid
fixed chart by the actual holomorphic chart transition. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem inChart_recenter_eventuallyEq (f : M.Carrier → ℝ) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    inChart x f =ᶠ[𝓝 z] (inChart (chartInv x z) f) ∘
      (fun w => chartPt (chartInv x z) (chartInv x w)) := by
  let y := chartInv x z
  have hI : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ w in 𝓝 z, chartInv x w ∈ (extChartAt (ComplexModel n) y).source :=
    hI.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  filter_upwards [hs] with w hw
  change f (chartInv x w) = f (chartInv y (chartPt y (chartInv x w)))
  exact (congrArg f ((extChartAt (ComplexModel n) y).left_inv hw)).symm

theorem smoothFn_leviQuadratic_nonneg_in_chart {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (hL : ∀ y, (levi f y).PosSemidef) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (v : ComplexVector n) :
    0 ≤ L22Aux.complexLeviQuadratic (inChart x f) z v := by
  let y := chartInv x z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt y (chartInv x w)
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have hT : ContDiffAt ℂ 2 T z := (L18Aux.chartTransition_contDiffAt x y hz hy).of_le (by simp)
  have hTz : T z = chartPt y y := rfl
  have hc : ContDiffAt ℝ 2 (inChart y f) (chartPt y y) :=
    ((hf y).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds
      (mem_extChartAt_target y))).of_le (by simp)
  have hcT : ContDiffAt ℝ 2 (inChart y f) (T z) := hTz.symm ▸ hc
  have hpos := (L22Aux.leviC_posSemidef_iff hc).mp (hL y)
  have he := inChart_recenter_eventuallyEq f x hz
  have hQ : L22Aux.complexLeviQuadratic (inChart x f) z v =
      L22Aux.complexLeviQuadratic (inChart y f) (chartPt y y) (fderiv ℂ T z v) := by
    calc
      _ = L22Aux.complexLeviQuadratic ((inChart y f) ∘ T) z v := by
        unfold L22Aux.complexLeviQuadratic
        rw [he.fderiv.fderiv_eq]
      _ = _ := by rw [L22Aux.complexLeviQuadratic_comp hT hcT, hTz]
  rw [hQ]
  exact hpos _

theorem smoothFn_leviC_posSemidef_in_chart {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (hL : ∀ y, (levi f y).PosSemidef) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) : (leviC (inChart x f) z).PosSemidef := by
  have hc : ContDiffAt ℝ 2 (inChart x f) z :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  exact (L22Aux.leviC_posSemidef_iff hc).mpr fun v =>
    smoothFn_leviQuadratic_nonneg_in_chart hf hL x hz v

end Yau.NodeProofs.D02Aux
