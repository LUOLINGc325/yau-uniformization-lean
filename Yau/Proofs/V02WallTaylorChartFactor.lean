import Yau.Proofs.V02WallTaylorSprayScalars
import Yau.Proofs.V02WallTaylorHadamardDomain

/-! Actual native spray differences divided by a smooth vanishing factor,
using the genuine derivative integral on buffered chart data. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof Metric

variable {n b : ℕ} {M : ComplexManifold n}

abbrev ChartFactorAux (n b : ℕ) := CotangentCoord n × (ℂ × (Fin b → ℂ))

def chartFactorDirection (p : ℂ × ChartFactorAux n b) : Fin b → ℂ :=
  p.1 • (p.2.2.1 • p.2.2.2)

def chartSprayFactor
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (B : CotangentPoint M → ℝ) (m : CotangentCoord n → ℝ) (x : M.Carrier)
    (p : ℂ × ChartFactorAux n b) : ℝ :=
  scaledHadamardFactor (fun w : (ℂ × ChartFactorAux n b) × (Fin b → ℂ) =>
    sprayScalar Ψ B x (w.1.2.1, w.2)) (fun w => m w.2.1) chartFactorDirection p

theorem chartSprayFactor_zero
    (Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M)
    (B : CotangentPoint M → ℝ) (m : CotangentCoord n → ℝ) (x : M.Carrier)
    (u : CotangentCoord n) (β : ℂ) (c : Fin b → ℂ) :
    chartSprayFactor Ψ B m x (0, (u, (β, c))) = 0 := by
  exact scaledHadamardFactor_zero (by simp [chartFactorDirection])

theorem norm_chartFactorDirection_le {p : ℂ × ChartFactorAux n b} {C : ℝ} (hC : 0 ≤ C)
    (hβ : ‖p.2.2.1‖ ≤ 1) (hc : ‖p.2.2.2‖ ≤ C) :
    ‖chartFactorDirection p‖ ≤ ‖p.1‖ * C := by
  dsimp [chartFactorDirection]
  rw [norm_smul, norm_smul]
  have hh : ‖p.2.2.1‖ * ‖p.2.2.2‖ ≤ C :=
    (mul_le_mul hβ hc (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)

theorem exists_uniform_chartSprayFactor
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    (hzero : ∀ y, Ψ (y, 0) = y) (x : M.Carrier)
    {a : CotangentCoord n} {δ R C : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hC : 0 ≤ C)
    (hvalid : Metric.ball a (2 * δ) ⊆ cotangentTarget x)
    (hΨ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x)
      (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ u ∈ Metric.closedBall a δ, ∀ τ ∈ Metric.closedBall 0 (R / 2),
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), τ)).val ∈ cotangentSource x)
    {B : CotangentPoint M → ℝ}
    (hB : ContDiffOn ℝ ∞ (fun u => B (cotangentChartInv x u)) (cotangentTarget x))
    {m : CotangentCoord n → ℝ} (hm : ContDiffOn ℝ ∞ m (Metric.ball a (2 * δ)))
    (hmb : ∀ u ∈ Metric.closedBall a δ, m u ∈ Set.Icc 0 1) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C + 1)) ∧
      ∀ z ∈ Metric.ball 0 r, ∀ u ∈ Metric.closedBall a δ,
      ∀ β ∈ Metric.closedBall (0 : ℂ) 1, ∀ c ∈ Metric.closedBall (0 : Fin b → ℂ) C,
      |chartSprayFactor Ψ B m x (z, (u, (β, c)))| < 1 / 2 ∧
      B (Ψ (NativeCotangentPoint.mk (cotangentChartInv x u), m u • (z • (β • c)))).val -
        B (cotangentChartInv x u) = m u * chartSprayFactor Ψ B m x (z, (u, (β, c))) := by
  let S := Metric.ball a (2 * δ) ×ˢ Metric.ball (0 : Fin b → ℂ) R
  let Ω := S ∩ (sprayCoordinate Ψ x) ⁻¹' cotangentTarget x
  have hΩ : IsOpen Ω := isOpen_sprayScalar_domain (isOpen_ball.prod isOpen_ball) hΨ
  have hF : ContDiffOn ℝ ∞ (sprayScalar Ψ B x) Ω :=
    sprayScalar_contDiffOn (isOpen_ball.prod isOpen_ball) hΨ hB
  let H : ((ℂ × ChartFactorAux n b) × (Fin b → ℂ)) → CotangentCoord n × (Fin b → ℂ) :=
    fun w => (w.1.2.1, w.2)
  have hH : ContDiff ℝ ∞ H :=
    ((contDiff_fst.comp contDiff_snd).comp contDiff_fst).prodMk contDiff_snd
  let Ω' := H ⁻¹' Ω
  have hΩ' : IsOpen Ω' := hΩ.preimage hH.continuous
  have hF' : ContDiffOn ℝ ∞ (fun w => sprayScalar Ψ B x (H w)) Ω' :=
    hF.comp hH.contDiffOn (fun _ hp => hp)
  let D : Set (ℂ × ChartFactorAux n b) := {p | p.2.1 ∈ Metric.ball a (2 * δ)}
  have hD : IsOpen D := isOpen_ball.preimage (continuous_fst.comp continuous_snd)
  have hm' : ContDiffOn ℝ ∞ (fun p : ℂ × ChartFactorAux n b => m p.2.1) D :=
    hm.comp (contDiffOn_fst.comp contDiffOn_snd (fun _ _ => Set.mem_univ _)) (fun _ hp => hp)
  have hA : ContDiffOn ℝ ∞ (chartFactorDirection (n := n) (b := b)) D := by
    exact contDiffOn_fst.smul
      (((contDiff_fst.comp contDiff_snd).comp contDiff_snd).contDiffOn.smul
        ((contDiff_snd.comp contDiff_snd).comp contDiff_snd).contDiffOn)
  let K : Set (ChartFactorAux n b) := Metric.closedBall a δ ×ˢ
    (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : Fin b → ℂ) C)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have h0 : ∀ p ∈ K, (0, p) ∈ D ∧ chartFactorDirection (0, p) = 0 ∧ ((0, p), 0) ∈ Ω' := by
    intro p hp
    refine ⟨Metric.closedBall_subset_ball (by linarith) hp.1, by simp [chartFactorDirection], ?_⟩
    exact sprayScalar_domain_contains_closed_buffer hδ hR hsource
      ⟨hp.1, Metric.mem_closedBall_self (by positivity)⟩
  obtain ⟨r, hr, hrR, hbound⟩ := exists_uniform_scaledHadamardFactor hΩ' hF' hD hm' hA hK h0
    (show 0 < R / (2 * (C + 1)) by positivity)
  refine ⟨r, hr, hrR, fun z hz u hu β hβ c hc => ?_⟩
  have hb := hbound z hz (u, (β, c)) ⟨hu, hβ, hc⟩
  have hβ' : ‖β‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hβ
  have hc' : ‖c‖ ≤ C := by simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  have hz' : ‖z‖ < R / (2 * (C + 1)) :=
    (show ‖z‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hz).trans hrR
  have hτ : m u • (z • (β • c)) ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hmb u hu).1]
    have hA' := norm_chartFactorDirection_le (p := (z, (u, (β, c)))) hC hβ' hc'
    change m u * ‖chartFactorDirection (z, (u, (β, c)))‖ ≤ R / 2
    have hh : ‖z‖ * (2 * (C + 1)) < R := (lt_div_iff₀ (by positivity)).mp hz'
    have hmul := mul_le_mul (hmb u hu).2 hA' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [norm_nonneg z]
  refine ⟨hb.2.1, ?_⟩
  have hact := sprayScalar_eq_actual (Ψ := Ψ) B x (p := (u, m u • (z • (β • c)))) (hsource _ hu _ hτ)
  have h0act := sprayScalar_zero hzero B x
    (hvalid (Metric.closedBall_subset_ball (by linarith) hu))
  have heq := hb.2.2
  change sprayScalar Ψ B x (u, m u • (z • (β • c))) - sprayScalar Ψ B x (u, 0) = _ at heq
  rw [hact, h0act] at heq
  exact heq

end Yau.Blueprint.V02WallTaylorProof
