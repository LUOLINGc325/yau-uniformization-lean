import Yau.Proofs.V03CotangentSmooth

/-! A genuine topology and charted space for the induced cotangent atlas.
The wrapper prevents the raw pair representation's product topology from
being mistaken for the cotangent topology. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

structure NativeCotangentPoint (M : ComplexManifold n) where
  val : CotangentPoint M

@[ext] theorem NativeCotangentPoint.ext {y y' : NativeCotangentPoint M}
    (h : y.val = y'.val) : y = y' := by
  cases y
  cases y'
  cases h
  rfl

def nativeCotangentChart (x : M.Carrier) :
    PartialEquiv (NativeCotangentPoint M) (CotangentCoord n) where
  toFun y := cotangentChart x y.val
  invFun z := ⟨cotangentChartInv x z⟩
  source := {y | y.val ∈ cotangentSource x}
  target := cotangentTarget x
  map_source' _ hy := cotangentChart_mapsTo x hy
  map_target' _ hz := cotangentChartInv_mapsTo x hz
  left_inv' _ hy := NativeCotangentPoint.ext (cotangentChart_left_inv x hy)
  right_inv' _ hz := cotangentChart_right_inv x hz

theorem isOpen_cotangentChartOverlap (x x' : M.Carrier) :
    IsOpen {z : CotangentCoord n | z ∈ cotangentTarget x ∧
      chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv x) z.1 :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) x).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz.1.1)
  have htarget : ∀ᶠ w in 𝓝 z, w ∈ cotangentTarget x :=
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds hz.1
  have hsource : ∀ᶠ w in 𝓝 z,
      chartInv x w.1 ∈ (extChartAt (ComplexModel n) x').source :=
    (hi.continuousAt.comp continuousAt_fst).eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x').mem_nhds hz.2)
  filter_upwards [htarget, hsource] with w hw hw'
  exact ⟨hw, hw'⟩

def nativeCotangentCore (M : ComplexManifold n) :
    ChartedSpaceCore (CotangentCoord n) (NativeCotangentPoint M) where
  atlas := Set.range nativeCotangentChart
  chartAt y := nativeCotangentChart y.val.1
  mem_chart_source y := mem_extChartAt_source y.val.1
  chart_mem_atlas y := ⟨y.val.1, rfl⟩
  open_source e e' he he' := by
    obtain ⟨x, rfl⟩ := he
    obtain ⟨x', rfl⟩ := he'
    exact isOpen_cotangentChartOverlap x x'
  continuousOn_toFun e e' he he' := by
    obtain ⟨x, rfl⟩ := he
    obtain ⟨x', rfl⟩ := he'
    intro z hz
    exact (cotangentChartTransition_contDiffAt x x' hz.1 hz.2).continuousAt.continuousWithinAt

instance nativeCotangentTopologicalSpace (M : ComplexManifold n) :
    TopologicalSpace (NativeCotangentPoint M) :=
  (nativeCotangentCore M).toTopologicalSpace

instance nativeCotangentChartedSpace (M : ComplexManifold n) :
    ChartedSpace (CotangentCoord n) (NativeCotangentPoint M) :=
  (nativeCotangentCore M).toChartedSpace

theorem nativeCotangent_chartAt_apply (y y' : NativeCotangentPoint M) :
    chartAt (CotangentCoord n) y y' = cotangentChart y.val.1 y'.val := rfl

theorem nativeCotangent_chartAt_symm_apply (y : NativeCotangentPoint M)
    (z : CotangentCoord n) :
    ((chartAt (CotangentCoord n) y).symm z).val = cotangentChartInv y.val.1 z := rfl

end Yau.Blueprint.V03Proof
