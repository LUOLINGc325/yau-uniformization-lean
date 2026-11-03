import Yau.Proofs.V02WallTaylorChartFactor

/-! An explicit open domain for the actual native-chart derivative integral
retains joint smoothness in every independent auxiliary parameter. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n b : ℕ} {M : ComplexManifold n}

def chartFactorLift (w : (ℂ × ChartFactorAux n b) × (Fin b → ℂ)) :
    CotangentCoord n × (Fin b → ℂ) := (w.1.2.1, w.2)

def chartFactorDomain
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (m : CotangentCoord n → ℝ) (x : M.Carrier) (a : CotangentCoord n) (δ R : ℝ) :
    Set (ℂ × ChartFactorAux n b) :=
  hadamardSegmentDomain
    (chartFactorLift ⁻¹' ((Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R) ∩
      (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x))
    {p | p.2.1 ∈ Metric.ball a (2 * δ)} (fun p => m p.2.1) chartFactorDirection

theorem chartFactorLift_contDiff : ContDiff ℝ ∞ (chartFactorLift (n := n) (b := b)) :=
  ((contDiff_fst.comp contDiff_snd).comp contDiff_fst).prodMk contDiff_snd

theorem chartFactorDirection_contDiff : ContDiff ℝ ∞ (chartFactorDirection (n := n) (b := b)) :=
  contDiff_fst.smul (((contDiff_fst.comp contDiff_snd).comp contDiff_snd).smul
    ((contDiff_snd.comp contDiff_snd).comp contDiff_snd))

theorem isOpen_chartFactorDomain
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {a : CotangentCoord n} {δ R : ℝ}
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x)
      (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {m : CotangentCoord n → ℝ} (hm : ContDiffOn ℝ ∞ m (Metric.ball a (2 * δ))) :
    IsOpen (chartFactorDomain Ψ m x a δ R) := by
  apply isOpen_hadamardSegmentDomain
  · exact (isOpen_sprayScalar_domain (isOpen_ball.prod isOpen_ball) hΨ).preimage
      chartFactorLift_contDiff.continuous
  · exact isOpen_ball.preimage (continuous_fst.comp continuous_snd)
  · exact hm.continuousOn.comp (continuous_fst.comp continuous_snd).continuousOn (fun _ hp => hp)
  · exact chartFactorDirection_contDiff.continuous.continuousOn

theorem chartSprayFactor_contDiffOn
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {a : CotangentCoord n} {δ R : ℝ}
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x)
      (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {B : CotangentPoint M → ℝ}
    (hB : ContDiffOn ℝ ∞ (fun u => B (cotangentChartInv x u)) (cotangentTarget x))
    {m : CotangentCoord n → ℝ} (hm : ContDiffOn ℝ ∞ m (Metric.ball a (2 * δ))) :
    ContDiffOn ℝ ∞ (chartSprayFactor Ψ B m x) (chartFactorDomain Ψ m x a δ R) := by
  apply scaledHadamardFactor_contDiffOn_segmentDomain
  · exact (isOpen_sprayScalar_domain (isOpen_ball.prod isOpen_ball) hΨ).preimage
      chartFactorLift_contDiff.continuous
  · exact (sprayScalar_contDiffOn (isOpen_ball.prod isOpen_ball) hΨ hB).comp
      chartFactorLift_contDiff.contDiffOn (fun _ hp => hp)
  · exact isOpen_ball.preimage (continuous_fst.comp continuous_snd)
  · exact hm.comp ((contDiff_fst.comp contDiff_snd).contDiffOn) (fun _ hp => hp)
  · exact chartFactorDirection_contDiff.contDiffOn

theorem mem_chartFactorDomain_of_time_bound
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {a : CotangentCoord n} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hsource : ∀ u ∈ Metric.closedBall a δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    {m : CotangentCoord n → ℝ} {p : ℂ × ChartFactorAux n b}
    (hu : p.2.1 ∈ Metric.closedBall a δ)
    (hτ : m p.2.1 • chartFactorDirection p ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2)) :
    p ∈ chartFactorDomain Ψ m x a δ R := by
  refine ⟨Metric.closedBall_subset_ball (by linarith) hu, fun s hs => ?_⟩
  apply sprayScalar_domain_contains_closed_buffer hδ hR hsource
  refine ⟨hu, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hτ ⊢
  change ‖s • (m p.2.1 • chartFactorDirection p)‖ ≤ R / 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans (by simpa using hτ)


theorem chartSprayFactor_identity
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {x : M.Carrier} {a : CotangentCoord n} {δ R : ℝ}
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x)
      (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {B : CotangentPoint M → ℝ}
    (hB : ContDiffOn ℝ ∞ (fun u => B (cotangentChartInv x u)) (cotangentTarget x))
    {m : CotangentCoord n → ℝ} {p : ℂ × ChartFactorAux n b}
    (hp : p ∈ chartFactorDomain Ψ m x a δ R) :
    sprayScalar Ψ B x (p.2.1, m p.2.1 • chartFactorDirection p) -
      sprayScalar Ψ B x (p.2.1, 0) = m p.2.1 * chartSprayFactor Ψ B m x p := by
  have hopen := (isOpen_sprayScalar_domain (isOpen_ball.prod isOpen_ball) hΨ).preimage
    chartFactorLift_contDiff.continuous
  have hsmooth := (sprayScalar_contDiffOn (isOpen_ball.prod isOpen_ball) hΨ hB).comp
    chartFactorLift_contDiff.contDiffOn (fun _ hp => hp)
  exact scaledHadamardFactor_identity
    (F := fun w : (ℂ × ChartFactorAux n b) × (Fin b → ℂ) => sprayScalar Ψ B x (chartFactorLift w))
    (m := fun w => m w.2.1) (A := chartFactorDirection) (p := p) hopen hsmooth hp.2

end Yau.Blueprint.V02WallTaylorProof
