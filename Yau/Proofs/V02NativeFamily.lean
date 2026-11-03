import Yau.Proofs.V02FlowFields
import Yau.Proofs.V02CramerField

/-! The actual compact native spray composes with the original closed disc
and scalar time coefficients to give a genuinely joint holomorphic family. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n b : ℕ} {M : ComplexManifold n}

def nativeSprayFamily
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (f : ℂ → CotangentPoint M) (h : ℂ → ℂ) (c : ℂ → Fin b → ℂ)
    (z ζ : ℂ) : CotangentPoint M :=
  (Ψ (NativeCotangentPoint.mk (f ζ), fun k => z * h ζ * c ζ k)).val

theorem nativeSprayFamily_zero
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (f : ℂ → CotangentPoint M) (h : ℂ → ℂ) (c : ℂ → Fin b → ℂ) :
    nativeSprayFamily Ψ f h c 0 = f := by
  funext ζ
  simpa only [nativeSprayFamily, zero_mul, Pi.zero_def] using
    congrArg NativeCotangentPoint.val (hzero (NativeCotangentPoint.mk (f ζ)))

theorem continuousLinearMap_fin_basis_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : (Fin b → ℂ) →L[ℂ] E) (v : Fin b → ℂ) :
    D v = ∑ k, v k • D (Pi.single k 1) := by
  classical
  have hv : v = ∑ k, v k • Pi.single k (1 : ℂ) := by
    have he (k : Fin b) : v k • Pi.single k (1 : ℂ) = Pi.single k (v k) := by
      rw [← Pi.single_smul]
      simp
    simp_rw [he]
    ext i
    simp
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

theorem nativeSpray_first_field_line
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {U : Set (NativeCotangentPoint M)} {R : ℝ} (hU : IsOpen U) (hR : 0 < R)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (hfirst : ∀ y ∈ U, ∀ k : Fin b,
      fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val)
        0 (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val))
    (y : NativeCotangentPoint M) (hy : y ∈ U) (v : Fin b → ℂ) :
    HasDerivAt (fun z : ℂ => cotangentChart y.val.1 (Ψ (y, z • v)).val)
      (cotangentVectorOfCoords (fieldMatrix Z y.val *ᵥ v)) 0 := by
  classical
  have hpair : ContMDiff 𝓘(ℂ, Fin b → ℂ)
      ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ)) ∞
      (fun τ : Fin b → ℂ => (y, τ)) := contMDiff_const.prodMk contMDiff_id
  have hslice := (hΨ.contMDiffAt ((hU.prod Metric.isOpen_ball).mem_nhds
    (show (y, 0) ∈ U ×ˢ Metric.ball (0 : Fin b → ℂ) R from
      ⟨hy, Metric.mem_ball_self hR⟩))).comp 0 hpair.contMDiffAt
  have hc := (contMDiffAt_iff_target.mp hslice).2
  change ContMDiffAt 𝓘(ℂ, Fin b → ℂ) 𝓘(ℂ, CotangentCoord n) ∞
    (fun τ => cotangentChart (Ψ (y, 0)).val.1 (Ψ (y, τ)).val) 0 at hc
  rw [hzero] at hc
  have hd := hc.contDiffAt.differentiableAt (by simp)
  let D := fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val) 0
  have hD : D v = cotangentVectorOfCoords (fieldMatrix Z y.val *ᵥ v) := by
    rw [continuousLinearMap_fin_basis_sum]
    simp_rw [show ∀ k, D (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val) from hfirst y hy]
    have hs : (∑ k, v k • Z k y.val) = fieldMatrix Z y.val *ᵥ v := by
      ext i
      simp [fieldMatrix, Matrix.mulVec, dotProduct, mul_comm]
    rw [← hs]
    change _ = (cotangentVectorOfCoordsLinear (n := n)) (∑ k, v k • Z k y.val)
    simp only [map_sum, map_smul]
    rfl
  have hline := hd.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v) (by simp)
  have hline' : HasDerivAt (fun z : ℂ => cotangentChart y.val.1 (Ψ (y, z • v)).val) (D v) 0 := by
    simpa only [Function.comp_def, id_eq, one_smul] using hline
  rw [hD] at hline'
  exact hline'

theorem nativeSprayFamily_holomorphic
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {U : Set (NativeCotangentPoint M)} {R r : ℝ}
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    (hfU : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (f ζ) ∈ U)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall (0 : ℂ) 1))
    {c : ℂ → Fin b → ℂ}
    (hc : ∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1))
    (hparam : ∀ p ∈ Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1,
      (fun k => p.1 * h p.2 * c p.2 k) ∈ Metric.ball (0 : Fin b → ℂ) R) :
    CotangentHolomorphicOn (fun p : ℂ × ℂ => nativeSprayFamily Ψ f h c p.1 p.2)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) := by
  let S := Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1
  have hsnd : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) ∞ (Prod.snd : ℂ × ℂ → ℂ) S :=
    (contDiff_snd : ContDiff ℂ ∞ (Prod.snd : ℂ × ℂ → ℂ)).contMDiff.contMDiffOn
  have hFn : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CotangentCoord n) ∞
      (fun p : ℂ × ℂ => NativeCotangentPoint.mk (f p.2)) S :=
    (cotangentDisc_native_contMDiffOn hf).comp hsnd (fun p hp => hp.2)
  have hτ : ContDiffOn ℂ ∞ (fun p : ℂ × ℂ => fun k => p.1 * h p.2 * c p.2 k) S := by
    apply contDiffOn_pi.mpr
    intro k
    exact (contDiffOn_fst.mul (hh.comp contDiffOn_snd (fun p hp => hp.2))).mul
      ((hc k).comp contDiffOn_snd (fun p hp => hp.2))
  exact native_contMDiffOn_cotangentHolomorphicOn
    (hΨ.comp (hFn.prodMk hτ.contMDiffOn) (fun p hp => ⟨hfU _ hp.2, hparam p hp⟩))

theorem nativeSprayFamily_parameter_bound
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    {h : ℂ → ℂ} (hh : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1)
    {c : ℂ → Fin b → ℂ} (hc : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∀ k, ‖c ζ k‖ ≤ C)
    {p : ℂ × ℂ} (hp : p ∈ Metric.ball (0 : ℂ) (R / (2 * (C + 1))) ×ˢ
      Metric.closedBall (0 : ℂ) 1) :
    (fun k => p.1 * h p.2 * c p.2 k) ∈ Metric.ball (0 : Fin b → ℂ) R := by
  have hden : 0 < 2 * (C + 1) := by positivity
  have hr : 0 < R / (2 * (C + 1)) := div_pos hR hden
  have hn : ‖(fun k => p.1 * h p.2 * c p.2 k)‖ ≤ ‖p.1‖ * C := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) hC)).mpr
    intro k
    rw [norm_mul, norm_mul]
    have ht := mul_le_mul_of_nonneg_left (hh p.2 hp.2) (norm_nonneg p.1)
    exact (mul_le_mul ht (hc p.2 hp.2 k) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  apply Metric.mem_ball.mpr
  rw [dist_zero_right]
  have hz : ‖p.1‖ < R / (2 * (C + 1)) := by simpa using Metric.mem_ball.mp hp.1
  have hmul : ‖p.1‖ * (2 * (C + 1)) < R := (lt_div_iff₀ hden).mp hz
  exact hn.trans_lt (by nlinarith [norm_nonneg p.1])

end Yau.Blueprint.V02Proof
