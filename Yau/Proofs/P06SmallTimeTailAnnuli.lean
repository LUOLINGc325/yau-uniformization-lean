import Yau.Proofs.P06CutoffTailAnnuli
import Yau.Proofs.P06SmallTimeTailSeries

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology InnerProductSpace ComplexOrder

namespace Yau.NodeProofs.P06Aux.SmallTimeTail
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Davies CutoffTail
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- The strong Gaussian single-shell estimate, before summing the shells. -/
theorem shell_smallTime_bound_of_annular
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (A : ℝ) (hA : 1 ≤ A)
    (htail : ∀ (r R : ℝ), 0 < r → r < R → ∀ t, 0 < t →
      ∀ f : L2FormHilbert g μ k,
      indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f →
      ‖indicator g μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (hodgeHeatHilbert g μ hμ k t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖)
    (r : ℝ) (hr : 0 < r) (J : ℕ) (hsep : 2 * r ≤ radius J)
    (B : ℝ) (hB : 0 ≤ B) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (D : RealForm M k) (hD : L2RealForm g.form μ D)
    (hb : ∀ x, formNormSq g.form D x ≤ B ^ 2)
    (q : ℕ) (t : ℝ) (ht : 0 < t) (htτ : t ≤ 2 * τ) :
    ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
      (hodgeHeatHilbert g μ hμ k t
        (shell g μ o (J + q) (realizeActualForm g μ D hD)))‖ ≤
      (B * 2 ^ n * Real.sqrt (μ.real (distBall g.form o 1)) * radius J ^ n *
        Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ))) * shellMajorant n A q := by
  have hsepq : 2 * r ≤ radius (J + q) :=
    hsep.trans (radius_mono (Nat.le_add_right J q))
  have he := reverse_annular_tail g μ hμ o A hA htail r (radius (J + q)) t hr
    (by linarith) ht (shell g μ o (J + q) (realizeActualForm g μ D hD))
    (shell_supported_outside g μ o (J + q) _)
  have hnorm := (shell_norm_le_ball g μ o (J + q) (realizeActualForm g μ D hD)).trans
    (indicator_realize_polynomial_bound g hK hRic μ hμ o D hD B hB hb
      (radius (J + q + 1)) (one_le_radius _))
  have hgauss := gaussian_le_split (zero_lt_one.trans_le hA) hτ hτ1 ht htτ
    (one_le_radius J) (one_le_radius q) (by rwa [← radius_add])
  rw [← radius_add] at hgauss
  calc
    _ ≤ Real.exp (-(radius (J + q) - r) ^ 2 / (2 * A ^ 2 * t)) *
        ‖shell g μ o (J + q) (realizeActualForm g μ D hD)‖ := he
    _ ≤ (Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ)) *
        Real.exp (-radius q ^ 2 / (32 * A ^ 2))) *
        (B * radius (J + q + 1) ^ n * Real.sqrt (μ.real (distBall g.form o 1))) :=
      mul_le_mul hgauss hnorm (norm_nonneg _) (by positivity)
    _ = _ := by rw [radius_succ, radius_add, mul_pow, mul_pow]; unfold shellMajorant; ring

/-- GT: a support-independent remote Gaussian bound with its constant chosen
before the datum, the dyadic radius, and the small time. -/
theorem remote_smallTime_bound_of_annular
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (A : ℝ) (hA : 1 ≤ A)
    (htail : ∀ (r R : ℝ), 0 < r → r < R → ∀ t, 0 < t →
      ∀ f : L2FormHilbert g μ k,
      indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r) f = f →
      ‖indicator g μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (hodgeHeatHilbert g μ hμ k t f)‖ ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ), 2 * r ≤ radius J →
      ∀ (B : ℝ), 0 ≤ B → ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (D : RealForm M k) (hD : L2RealForm g.form μ D),
      CompactlySupportedRealForm D → (∀ x, formNormSq g.form D x ≤ B ^ 2) →
      ballProjection g μ o J (realizeActualForm g μ D hD) = 0 →
      ∀ (t : ℝ), 0 < t → t ≤ 2 * τ →
      ‖indicator g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
        (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ D hD))‖ ≤
        C * B * radius J ^ n * Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ)) := by
  let C₀ := 2 ^ n * Real.sqrt (μ.real (distBall g.form o 1))
  let S := ∑' q, shellMajorant n A q
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hS : 0 ≤ S := shellMajorant_tsum_nonneg n A
  refine ⟨C₀ * S + 1, by positivity, ?_⟩
  intro J hsep B hB τ hτ hτ1 D hD hcD hb hzero t ht htτ
  let f := realizeActualForm g μ D hD
  obtain ⟨N, hN, hJN⟩ := (compactlySupported_indicator_eventually_self g μ o D hD hcD).and
    (eventually_ge_atTop J) |>.exists
  change ballProjection g μ o N f = f at hN
  change ballProjection g μ o J f = 0 at hzero
  have hdecomp : (∑ q ∈ Finset.range (N - J), shell g μ o (J + q) f) = f := by
    have hh := sum_shell g μ o f J N hJN
    rw [hN, hzero, sub_zero] at hh
    simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hh
  let P := indicator (k := k) g μ (distBall g.form o r) (L12Aux.measurableSet_distBall g o r)
  let H := hodgeHeatHilbert g μ hμ k t
  let E := Real.exp (-radius J ^ 2 / (32 * A ^ 2 * τ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ radius J ^ n := pow_nonneg (radius_pos J).le n
  have hsum : ∑ q ∈ Finset.range (N - J), shellMajorant n A q ≤ S :=
    (summable_shellMajorant n (zero_lt_one.trans_le hA)).sum_le_tsum _
      (fun q _ => shellMajorant_nonneg n A q)
  calc
    ‖P (H f)‖ = ‖∑ q ∈ Finset.range (N - J), P (H (shell g μ o (J + q) f))‖ := by
      rw [← map_sum, ← map_sum, hdecomp]
    _ ≤ ∑ q ∈ Finset.range (N - J), ‖P (H (shell g μ o (J + q) f))‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.range (N - J),
        (B * C₀ * radius J ^ n * E) * shellMajorant n A q := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [P, H, f, C₀, E, mul_assoc] using
        shell_smallTime_bound_of_annular g hK hRic μ hμ o A hA htail r hr J hsep
          B hB τ hτ hτ1 D hD hb q t ht htτ
    _ = (B * C₀ * radius J ^ n * E) *
        ∑ q ∈ Finset.range (N - J), shellMajorant n A q := by rw [Finset.mul_sum]
    _ ≤ (B * C₀ * radius J ^ n * E) * S :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (C₀ * S + 1) * B * radius J ^ n * E := by
      have hh := mul_nonneg hB (mul_nonneg hR hE)
      nlinarith

end Yau.NodeProofs.P06Aux.SmallTimeTail
