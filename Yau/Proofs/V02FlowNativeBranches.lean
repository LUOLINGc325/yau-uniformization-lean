import Yau.Proofs.V02FlowNativeCharts
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Coordinate solutions decode into actual native integral curves and joint maps. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

def nativeChartFlow (x : M.Carrier) (φ : ℂ × CotangentCoord n → CotangentCoord n)
    (p : ℂ × NativeCotangentPoint M) : NativeCotangentPoint M :=
  ⟨cotangentChartInv x (φ (p.1, cotangentChart x p.2.val))⟩

theorem nativeChartFlow_zero (x : M.Carrier)
    {φ : ℂ × CotangentCoord n → CotangentCoord n} (hzero : ∀ u, φ (0, u) = u)
    {y : NativeCotangentPoint M} (hy : y.val ∈ cotangentSource x) :
    nativeChartFlow x φ (0, y) = y := by
  apply NativeCotangentPoint.ext
  exact (congrArg (cotangentChartInv x) (hzero _)).trans (cotangentChart_left_inv x hy)

theorem nativeChartFlow_integralCurve (x : M.Carrier)
    {Z : CotangentPoint M → CotangentIndex n → ℂ}
    {φ : ℂ × CotangentCoord n → CotangentCoord n} {D : Set ℂ}
    (hD : IsOpen D) (y : NativeCotangentPoint M)
    (himage : ∀ t ∈ D, φ (t, cotangentChart x y.val) ∈ cotangentTarget x)
    (hode : ∀ t ∈ D, HasDerivAt (fun z => φ (z, cotangentChart x y.val))
      (cotangentChartField Z x (φ (t, cotangentChart x y.val))) t) :
    NativeFieldIntegralCurve Z (fun t => nativeChartFlow x φ (t, y)) D := by
  let γ := fun t => nativeChartFlow x φ (t, y)
  have hcontφ : ContinuousOn (fun t => φ (t, cotangentChart x y.val)) D :=
    fun t ht => (hode t ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn γ D :=
    (nativeCotangentChartHomeomorph x).continuousOn_symm.comp hcontφ himage
  refine ⟨hc, fun t ht x' hx' => ?_⟩
  have hsource : (γ t).val ∈ cotangentSource x := cotangentChartInv_mapsTo x (himage t ht)
  apply nativeCurve_coordinate_hasDerivAt_transport (hc.continuousAt (hD.mem_nhds ht))
    x x' hsource hx'
  have heq : (fun z => cotangentChart x (γ z).val) =ᶠ[𝓝 t]
      (fun z => φ (z, cotangentChart x y.val)) := by
    filter_upwards [hD.mem_nhds ht] with z hz
    exact cotangentChart_right_inv x (himage z hz)
  have hat := hode t ht
  rw [← cotangentChart_right_inv x (himage t ht)] at hat
  exact hat.congr_of_eventuallyEq heq

theorem nativeChartFlow_contMDiffOn (x : M.Carrier)
    {a : CotangentCoord n} {d R : ℝ} {φ : ℂ × CotangentCoord n → CotangentCoord n}
    (hball : ball a d ⊆ cotangentTarget x)
    (hφ : ContDiffOn ℂ ∞ φ (ball (0 : ℂ) R ×ˢ ball a d))
    (himage : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball a d, φ p ∈ cotangentTarget x) :
    ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n)) 𝓘(ℂ, CotangentCoord n) ∞
      (nativeChartFlow x φ) (ball (0 : ℂ) R ×ˢ nativeCotangentChartBall x a d) := by
  let S := ball (0 : ℂ) R ×ˢ nativeCotangentChartBall x a d
  have hsource : ∀ p ∈ S, p.2.val ∈ cotangentSource x :=
    fun p hp => ((nativeCotangentChartBall_mem_iff hball).mp hp.2).1
  have hcoord : ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n))
      𝓘(ℂ, CotangentCoord n) ∞
      (fun p : ℂ × NativeCotangentPoint M => cotangentChart x p.2.val) S :=
    (nativeCotangentChart_contMDiffOn x).comp contMDiffOn_snd hsource
  have hpair : ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n))
      𝓘(ℂ, ℂ × CotangentCoord n) ∞
      (fun p : ℂ × NativeCotangentPoint M => (p.1, cotangentChart x p.2.val)) S := by
    apply (contMDiffOn_prod_module_iff _).mpr
    exact ⟨contMDiffOn_fst, hcoord⟩
  have hmap : ∀ p ∈ S, (p.1, cotangentChart x p.2.val) ∈ ball (0 : ℂ) R ×ˢ ball a d :=
    fun p hp => ⟨hp.1, ((nativeCotangentChartBall_mem_iff hball).mp hp.2).2⟩
  exact (nativeCotangentChartInv_contMDiffOn x).comp
    (hφ.contMDiffOn.comp hpair hmap) (fun p hp => himage _ (hmap p hp))

end Yau.Blueprint.V02FlowProof
