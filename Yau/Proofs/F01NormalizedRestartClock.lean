import Yau.Proofs.F01NormalizedRestartLogData

/-! The actual closed short-time restart equation gives the clock
equation of the normalized right profile, including its initial face. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalized_restart_clock_jet
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (W : M.Carrier → ℝ → ℝ)
    {σ ε r : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius) (hrε : σ ^ 2 * r ≤ ε)
    (T : ℝ) (hW : SmoothSpaceTime W (Icc 0 ε))
    (hpot : ∀ s ∈ Icc 0 ε, ∀ y,
      gMat (h s) y = gMat g y - ((T + s : ℝ) : ℂ) • ricci g y + levi (fun z => W z s) y)
    (hpde : ∀ y s, s ∈ Icc 0 ε → HasDerivWithinAt (W y)
      (flowLogDetRatio g h y s) (Icc 0 ε) s)
    (a : M.Carrier) {x : Space n} (hx : x ∈ ball 0 1) {t : ℝ} (ht : t ∈ Ico 0 r) :
    HasDerivWithinAt
      (fun s => shiftedNativePotential A (absoluteRestartPotential W T) a σ T (x, s))
      (localPotentialClockRHS (shiftedComplexBackground A a σ T)
        (fun p => normalizedPotentialLogSource A a σ p.1)
        (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) (x, t)) (Ico 0 r) t := by
  have hMap : MapsTo (fun s : ℝ => σ ^ 2 * s) (Ico 0 r) (Icc 0 ε) := by
    intro s hs
    exact ⟨mul_nonneg (sq_nonneg σ) hs.1,
      (mul_le_mul_of_nonneg_left hs.2.le (sq_nonneg σ)).trans hrε⟩
  have hAffine : HasDerivWithinAt (fun s : ℝ => σ ^ 2 * s) (σ ^ 2) (Ico 0 r) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (σ ^ 2)).hasDerivWithinAt
  have hScaled := ((hpde (A.chart a (σ • x)) _ (hMap ht)).comp t hAffine hMap).const_mul ((σ ^ 2)⁻¹)
  have hValue := (normalized_restart_log_data hg A h W hσ hσr hrε T hW hpot a (p := (x, t))
    ⟨hx, ht⟩).1
  rw [← hValue]
  have hCurve : (fun s => shiftedNativePotential A (absoluteRestartPotential W T) a σ T (x, s)) =
      (fun s => (σ ^ 2)⁻¹ * W (A.chart a (σ • x)) (σ ^ 2 * s)) :=
    funext (fun s => normalized_restart_profile_eq A W a σ T (x, s))
  rw [hCurve]
  convert hScaled using 1
  · rfl
  · field_simp [pow_ne_zero 2 hσ.ne']

end Yau.NodeProofs.F01Aux
