import Yau.Proofs.V02NativeFirstField
import Yau.Proofs.V02NativeCenter
import Yau.Proofs.V02SliceAdmissibility
import Yau.Proofs.V02OriginalOuter

/-! The literal actual native spray, using the actual holomorphic Cramer
coefficients and original wall outer function, realizes the original field. -/

open scoped Manifold Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q b : ℕ} {X : KahlerManifold n}

theorem realizesFirstField_of_native_spray
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R r C : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hr : 0 < r) (hC : 0 ≤ C)
    (hrR : r ≤ R / (2 * (C + 1)))
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun u => (cotangentTransition (chartInv x u.1) x (cotangentChartInv x u) *ᵥ
        Z k (cotangentChartInv x u)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    (hfirst : ∀ y ∈ U, ∀ k : Fin b,
      fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val)
        0 (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val))
    {Kc : Set (CotangentCoord n × ℝ)}
    (hTube : ∀ p ∈ Kc, ∀ τ ∈ closedBall (0 : Fin b → ℂ) R,
      InCotangentTimeChart d.chart
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), τ)).val p.2
        (interior (centerCylinder d)))
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (α : ℂ → ℂ)
    (hF : AdmissibleVariationDisc d j F)
    (hcenter : InCotangentTimeChart d.chart (F.f 0) F.s Kc)
    (hfU : ∀ ζ ∈ closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (F.f ζ) ∈ U)
    (hE : NormalizedDiscFrame d.G F.f E) (hl : HolomorphicColumn l)
    (hα : ContDiffOn ℂ ∞ α (closedBall 0 1))
    (hα1 : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖α ζ‖ ≤ 1)
    (hαD : boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ)) ≤ 1)
    (hcC : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k,
      ‖spanningFirstCoefficients d.G Z F.f E l α ζ k‖ ≤ C)
    (hboundary : ∀ z ∈ ball (0 : ℂ) r, ∀ θ,
      nativeSprayFamily Ψ F.f (outerCandidate (logTrace d j F.f) a)
        (spanningFirstCoefficients d.G Z F.f E l α) z (circlePoint θ) ∈ boundaryRegion d j) :
    RealizesFirstField d j a F E l (outerCandidate (logTrace d j F.f) a) α
      (nativeSprayFamily Ψ F.f (outerCandidate (logTrace d j F.f) a)
        (spanningFirstCoefficients d.G Z F.f E l α)) r := by
  obtain ⟨hh, hhphase, hhcenter, hhmod, hhsup⟩ := original_outer_properties hd hF a
  have hc (k : Fin b) := spanningFirstCoefficients_contDiffOn hd.2.2.2.2.1
    hZ hspan hE.1 hl hα k
  have hFam := nativeSprayFamily_holomorphicDiscFamily hR hr hC hrR hzero hΨ
    F hF.1 hfU hh hhsup hc hcC
  refine ⟨hFam, ?_, ?_, hh, hα, hhphase, hhcenter, hhmod, hα1, hαD⟩
  · intro z hz
    have hcen := nativeSprayFamily_center hR hC hTube hcenter hhsup hcC
      ((ball_subset_ball hrR) hz)
    exact slice_admissible_of_center_boundary hd hF (hFam.cotangentDisc hz)
      ⟨hcen.1, interior_subset hcen.2⟩ (hboundary z hz)
  · intro ζ hζ
    exact nativeSprayFamily_spanning_first_field hU hR hzero hΨ hd.2.2.2.2.1
      hZ hspan hfirst hF.1 hfU E l (outerCandidate (logTrace d j F.f) a) α hζ

end Yau.Blueprint.V02Proof
