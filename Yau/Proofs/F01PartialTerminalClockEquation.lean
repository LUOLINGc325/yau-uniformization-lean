import Yau.Proofs.F01ShiftedPointLogData

/-! At every clock strictly before the actual terminal horizon, the
normalized partial flow satisfies its original logdet equation and
has a genuinely positive native matrix. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem partial_terminal_shifted_clock_jet
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {σ Tstar : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hEarly : 0 ≤ Tstar - σ ^ 2 / 4)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Ico 0 Tstar, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s)
    (a : M.Carrier) {x : Space n} (hx : x ∈ ball 0 1) {t : ℝ}
    (ht : t ∈ Ioo (-(1 / 4 : ℝ)) 0) :
    HasDerivAt (fun s => shiftedNativePotential A U a σ Tstar (x, s))
      (localPotentialClockRHS (shiftedComplexBackground A a σ Tstar)
        (fun p => normalizedPotentialLogSource A a σ p.1)
        (shiftedNativePotential A U a σ Tstar) (x, t)) t ∧
    (chartPotentialMatrix (shiftedComplexBackground A a σ Tstar)
      (shiftedNativePotential A U a σ Tstar) (x, t)).PosDef := by
  let s : ℝ := Tstar + σ ^ 2 * t
  let θ : ℝ := (s + Tstar) / 2
  have hs0 : 0 < s := by
    have hh := mul_lt_mul_of_pos_left ht.1 (sq_pos_of_pos hσ)
    dsimp only [s]
    linarith
  have hsT : s < Tstar := by
    dsimp only [s]
    exact add_lt_of_neg_right Tstar (mul_neg_of_pos_of_neg (sq_pos_of_pos hσ) ht.2)
  have hsθ : s < θ := by dsimp only [θ]; linarith
  have hθT : θ < Tstar := by dsimp only [θ]; linarith
  have hθ0 : 0 ≤ θ := (hs0.trans hsθ).le
  have hSub : Icc 0 θ ⊆ Ico 0 Tstar := fun r hr => ⟨hr.1, hr.2.trans_lt hθT⟩
  have hData := shifted_native_point_log_data hg A h U hσ.ne' (hU θ hθ0 hθT)
    (fun r hr y => hpot r (hSub hr) y) a (x, t)
    (spatialDilation_mem_ball hσ hσr hx) ⟨hs0.le, hsθ.le⟩
  refine ⟨?_, hData.2⟩
  have hOld := (hpde θ hθ0 hθT (A.chart a (σ • x)) s ⟨hs0.le, hsθ.le⟩).hasDerivAt
    (mem_of_superset (Ioo_mem_nhds hs0 hsθ) Ioo_subset_Icc_self)
  have hAffine : HasDerivAt (fun r : ℝ => Tstar + σ ^ 2 * r) (σ ^ 2) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (σ ^ 2)).const_add Tstar
  have hScaled := (hOld.comp t hAffine).const_mul ((σ ^ 2)⁻¹)
  have hCurve : (fun r => shiftedNativePotential A U a σ Tstar (x, r)) =
      (fun r => (σ ^ 2)⁻¹ * U (A.chart a (σ • x)) (Tstar + σ ^ 2 * r)) := by
    funext r
    simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
      affineParabolicPoint, add_zero]
  rw [hCurve]
  have hValue : flowLogDetRatio g h (A.chart a (σ • x)) s =
      localPotentialClockRHS (shiftedComplexBackground A a σ Tstar)
        (fun p => normalizedPotentialLogSource A a σ p.1)
        (shiftedNativePotential A U a σ Tstar) (x, t) := by
    simpa only [affineParabolicPoint, add_zero, s] using hData.1
  rw [← hValue]
  convert hScaled using 1
  · rfl
  · field_simp [pow_ne_zero 2 hσ.ne']

end Yau.NodeProofs.F01Aux
