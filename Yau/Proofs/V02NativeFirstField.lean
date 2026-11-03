import Yau.Proofs.V02NativeFamily

/-! The actual Cramer coefficients reconstruct the literal centered first
field of the original realization, including at every disc boundary point. -/

open scoped Manifold Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n q b : ℕ} {M : ComplexManifold n}

theorem nativeSprayFamily_spanning_first_field
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {U : Set (NativeCotangentPoint M)} {R : ℝ} (hU : IsOpen U) (hR : 0 < R)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    (hfirst : ∀ y ∈ U, ∀ k : Fin b,
      fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val)
        0 (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val))
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    (hfU : ∀ ζ ∈ closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (f ζ) ∈ U)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) 1) :
    fderiv ℂ (fun z => cotangentChart (f ζ).1
      (nativeSprayFamily Ψ f h (spanningFirstCoefficients G Z f E l α) z ζ)) 0 1 =
        cotangentVectorOfCoords ((α ζ * h ζ) • (E ζ *ᵥ l ζ)) := by
  classical
  let c := spanningFirstCoefficients G Z f E l α
  let v : Fin b → ℂ := h ζ • c ζ
  have hline := nativeSpray_first_field_line hU hR hzero hΨ Z hfirst
    (NativeCotangentPoint.mk (f ζ)) (hfU ζ hζ) v
  have hv : fieldMatrix Z (f ζ) *ᵥ v = (α ζ * h ζ) • (E ζ *ᵥ l ζ) := by
    dsimp only [v, c]
    rw [Matrix.mulVec_smul, spanningFirstCoefficients_field hG hZ hspan hf E l α hζ,
      smul_smul]
    congr 1
    ring
  rw [hv] at hline
  have htimes (z : ℂ) : (fun k => z * h ζ * c ζ k) = z • v := by
    funext k
    simp only [v, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hd : HasDerivAt (fun z => cotangentChart (f ζ).1
      (nativeSprayFamily Ψ f h c z ζ))
        (cotangentVectorOfCoords ((α ζ * h ζ) • (E ζ *ᵥ l ζ))) 0 := by
    simpa only [nativeSprayFamily, htimes] using hline
  rw [fderiv_apply_one_eq_deriv]
  exact hd.deriv

theorem nativeSprayFamily_image
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {K Kplus : Set (CotangentPoint M)} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (himage : ∀ y : NativeCotangentPoint M, y.val ∈ K →
      ∀ τ ∈ closedBall (0 : Fin b → ℂ) (R / 2), (Ψ (y, τ)).val ∈ Kplus)
    {f : ℂ → CotangentPoint M} (hfK : ∀ ζ ∈ closedBall (0 : ℂ) 1, f ζ ∈ K)
    {h : ℂ → ℂ} (hh : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1)
    {c : ℂ → Fin b → ℂ} (hc : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ζ k‖ ≤ C)
    {z ζ : ℂ} (hz : z ∈ ball (0 : ℂ) ((R / 2) / (2 * (C + 1))))
    (hζ : ζ ∈ closedBall (0 : ℂ) 1) : nativeSprayFamily Ψ f h c z ζ ∈ Kplus := by
  have hτ : (fun k => z * h ζ * c ζ k) ∈ ball (0 : Fin b → ℂ) (R / 2) :=
    nativeSprayFamily_parameter_bound (R := R / 2) (C := C) (h := h) (c := c)
      (p := (z, ζ)) (half_pos hR) hC hh hc ⟨hz, hζ⟩
  exact himage (NativeCotangentPoint.mk (f ζ)) (hfK ζ hζ) _ (ball_subset_closedBall hτ)

theorem nativeSprayFamily_holomorphicDiscFamily
    {X : KahlerManifold n}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hC : 0 ≤ C) (hrR : r ≤ R / (2 * (C + 1)))
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    (F : VariationDisc X) (hf : CotangentDisc F.f)
    (hfU : ∀ ζ ∈ closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (F.f ζ) ∈ U)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (closedBall (0 : ℂ) 1))
    (hh1 : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1)
    {c : ℂ → Fin b → ℂ} (hc : ∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (closedBall (0 : ℂ) 1))
    (hcC : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ζ k‖ ≤ C) :
    HolomorphicDiscFamily F (nativeSprayFamily Ψ F.f h c) r :=
  ⟨hr, nativeSprayFamily_zero Ψ hzero F.f h c,
    nativeSprayFamily_holomorphic hΨ hf hfU hh hc (fun p hp =>
      nativeSprayFamily_parameter_bound (h := h) (c := c) (p := p) hR hC hh1 hcC
        ⟨(ball_subset_ball hrR) hp.1, hp.2⟩)⟩

end Yau.Blueprint.V02Proof
