import Yau.Proofs.V02AreaTaylorSprayModel

/-! The actual spray pullback kernels have one parameter-jet budget on
all compact initial position and coefficient ranges. No disc is selected yet. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q b : ℕ} {X : KahlerManifold n}

def sprayRadius (R C0 : ℝ) : ℝ := R / (16 * (C0 + 1))

theorem sprayRadius_pos {R C0 : ℝ} (hR : 0 < R) (hC : 0 ≤ C0) : 0 < sprayRadius R C0 :=
  div_pos hR (by positivity)

theorem sprayRadius_lt {R C0 : ℝ} (hR : 0 < R) (hC : 0 ≤ C0) :
    sprayRadius R C0 < R / (2 * (C0 + 1)) := by
  unfold sprayRadius
  apply div_lt_div_of_pos_left hR (by positivity)
  nlinarith

theorem sprayTimes_norm_le (z h : ℂ) (c : ComplexVector b) :
    ‖(fun k : Fin b => z * h * c k)‖ ≤ ‖z‖ * ‖h‖ * ‖c‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le c k) (by positivity)

theorem sprayTimes_mem_half {R C0 : ℝ} (hR : 0 < R) (hC : 0 ≤ C0)
    {z h : ℂ} {c : ComplexVector b}
    (hz : ‖z‖ ≤ 2 * sprayRadius R C0) (hh : ‖h‖ ≤ 1) (hc : ‖c‖ ≤ C0) :
    (fun k : Fin b => z * h * c k) ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2) := by
  have hr := sprayRadius_pos hR hC
  have heq : sprayRadius R C0 * (16 * (C0 + 1)) = R := by
    unfold sprayRadius
    exact div_mul_cancel₀ R (by positivity)
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  calc
    _ ≤ ‖z‖ * ‖h‖ * ‖c‖ := sprayTimes_norm_le z h c
    _ ≤ (2 * sprayRadius R C0) * 1 * C0 :=
      mul_le_mul (mul_le_mul hz hh (norm_nonneg _) (by positivity)) hc (norm_nonneg _) (by positivity)
    _ ≤ R / 2 := by nlinarith

def sprayCompactData (a : CotangentCoord n) (δ r C0 : ℝ) : Set (ℂ × SprayData n b) :=
  Metric.closedBall (0 : ℂ) r ×ˢ
    (Metric.closedBall a δ ×ˢ (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ComplexVector b) C0))

theorem local_spray_kernel_uniform_jet_bound {d : VariationData X q}
    (hG : CotangentImmersion d.G)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (x : Pt X) (a : CotangentCoord n) {δ R C0 : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C0)
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall a δ,
      ∀ τ ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2),
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ sprayCompactData (b := b) a δ (sprayRadius R C0) C0,
      ∀ v : SprayData n b,
        ‖iteratedFDeriv ℝ k (fun z => complexDiagonal (localSpatialKernel d Ψ x (z, p.2)) v) p.1‖ ≤
          C * ‖v‖ ^ 2 := by
  have hK : IsCompact (sprayCompactData (b := b) a δ (sprayRadius R C0) C0) :=
    (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hsub : sprayCompactData (b := b) a δ (sprayRadius R C0) C0 ⊆
      localSpatialDomain Ψ x a δ R := by
    intro p hp
    have hz : ‖p.1‖ ≤ 2 * sprayRadius R C0 := by
      have h := Metric.mem_closedBall.mp hp.1
      rw [dist_zero_right] at h
      linarith [sprayRadius_pos hR hC]
    have hh : ‖p.2.2.1‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp hp.2.2.1
    have hc : ‖p.2.2.2‖ ≤ C0 := by simpa using Metric.mem_closedBall.mp hp.2.2.2
    have htime := sprayTimes_mem_half hR hC hz hh hc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hp.2.1).trans_lt (by linarith))
    · exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp htime).trans_lt (by linarith))
    · exact cotangentChart_mapsTo x (hsource p.2.1 hp.2.1 _ htime)
  exact compact_bilinear_parameter_jet_bound (localSpatialDomain_isOpen x hψ)
    (localSpatialKernel_contDiffOn hG x hψ) hK hsub k

end Yau.Blueprint.V02AreaTaylorProof
