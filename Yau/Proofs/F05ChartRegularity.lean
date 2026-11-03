import Yau.Proofs.F05LocalLaplacian

/-! Local C2 regularity transfers between actual holomorphic charts, so the
scalar operator calculator applies to locally C2 solutions. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_inChart_center_C2 (x : M.Carrier) (f : M.Carrier → ℝ)
    {z : Space n} (hz : z ∈ chartTarget x) (hf : ContDiffAt ℝ 2 (inChart x f) z) :
    ContDiffAt ℝ 2 (inChart (chartInv x z) f)
      (chartPt (chartInv x z) (chartInv x z)) := by
  let a := chartInv x z
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  let T : Space n → Space n := fun w => e.symm (chartInv a w)
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt (I := ComplexModel n) (x := x))
  have ha : a ∈ e.target := by
    have hm := (extChartAt (ComplexModel n) x).map_target hz
    simpa [a,e,chartInv,ComplexModel] using hm
  have hcenter : chartInv a (chartPt a a) = a :=
    (extChartAt (ComplexModel n) a).left_inv (mem_extChartAt_source a)
  have hmem : chartPt a a ∈ inverseChartDomain e a :=
    ⟨mem_extChartAt_target a,by change chartInv a (chartPt a a) ∈ e.target; rwa [hcenter]⟩
  have hU := (inverseChartDomain_isOpen e a).mem_nhds hmem
  have hT : ContDiffAt ℝ 2 T (chartPt a a) :=
    ((inverseChart_real_contDiffOn e he a).contDiffAt hU).of_le (by simp)
  have hPoint : T (chartPt a a) = z := by
    change e.symm (chartInv a (chartPt a a)) = z
    rw [hcenter]
    change (chartAt (Space n) x) (chartInv x z) = z
    simpa [chartInv,ComplexModel] using (extChartAt (ComplexModel n) x).right_inv hz
  have hComp : ContDiffAt ℝ 2 ((inChart x f) ∘ T) (chartPt a a) := by
    apply ContDiffAt.comp _ _ hT
    rwa [hPoint]
  apply hComp.congr_of_eventuallyEq
  filter_upwards [hU] with w hw
  have hx : chartInv a w ∈ (extChartAt (ComplexModel n) x).source := by
    have hh := hw.2
    simpa [e,ComplexModel] using hh
  change f (chartInv a w) = f (chartInv x ((chartAt (Space n) x) (chartInv a w)))
  apply congrArg f
  symm
  change chartInv x (chartPt x (chartInv a w)) = chartInv a w
  exact (extChartAt (ComplexModel n) x).left_inv hx

theorem F05_laplacian_chart_C2 (h : HermitianField M) (x : M.Carrier)
    (f : M.Carrier → ℝ) {z : Space n} (hz : z ∈ chartTarget x)
    (hf : ContDiffAt ℝ 2 (inChart x f) z) :
    laplacian h f (chartInv x z) =
      ∑ a, ∑ b, baseA h x z a b *
        fderiv ℝ (fderiv ℝ (inChart x f)) z (realVec a) (realVec b) :=
  F05_laplacian_local_chart h x f hz (F05_inChart_center_C2 x f hz hf)

end Yau.Proofs.F05Aux
