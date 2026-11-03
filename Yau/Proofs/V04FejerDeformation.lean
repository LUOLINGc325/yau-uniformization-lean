import Yau.Proofs.V04FejerEstimates
import Yau.Proofs.V04NegativeLimits

/-! Apply the original deformation estimate to each actual frozen Fejer
column on one common tail. The zero center eliminates the test Hessian;
finite summation retains the same coefficient before both limits. -/

open Filter
open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem fejer_deformation_sequence_upper {d : VariationData X q} {j a P : ℕ}
    {C CE ε E₀ : ℝ} (hC : 0 ≤ C) (hCE : 0 ≤ CE) (hε : 0 < ε)
    (hdef : DeformationEstimateWith d j a C CE)
    (F : ℕ → VariationDisc X) (E : ℕ → ℂ → CotangentMatrix n)
    (hF : MinimizingSequence d j ε F)
    (Kc : Set (CotangentCoord n × ℝ)) (hKc : IsCompact Kc)
    (hKint : Kc ⊆ interior (centerCylinder d))
    (hcenter : ∀ ν, InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc)
    (henergy : ∀ ν, (variationEnergy d j (F ν)).toReal ≤ E₀)
    (hframe : ∀ ν, NormalizedDiscFrame d.G (F ν).f (E ν))
    (hcol : ∀ ν i, HolomorphicColumn (fejerTestColumn d j a (F ν) (E ν) P i) ∧
      fejerTestColumn d j a (F ν) (E ν) P i 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ∑ r, ‖fejerTestColumn d j a (F ν) (E ν) P i z r‖ ^ 2 ≤ C ^ 2) ∧
      boundaryDSq (fun θ => fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ)) ≤
        ENNReal.ofReal (C * (P + 1))) :
    SeqUpperZero (fun ν =>
      -(∑ i, circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ)))) -
        ((2 * n : ℕ) * CE) * ε * (1 + (variationEnergy d j (F ν)).toReal + C * (P + 1))) := by
  let D₀ := Real.sqrt (C * (P + 1))
  have hD₀ : D₀ ^ 2 = C * (P + 1) := Real.sq_sqrt (by positivity)
  have hseq (i : CotangentIndex n) : SeqUpperZero (fun ν =>
      -circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ))) -
      CE * ε * (1 + (variationEnergy d j (F ν)).toReal + C * (P + 1))) := by
    have hs := hdef ε hε E₀ D₀ F E
      (fun ν => fejerTestColumn d j a (F ν) (E ν) P i) hF ⟨Kc, hKc, hKint, hcenter⟩
      (fun ν => ⟨henergy ν, hframe ν, (hcol ν i).1, (hcol ν i).2.2.1,
        by rw [hD₀]; exact (hcol ν i).2.2.2⟩)
    have hsemi (ν : ℕ) :
        (boundaryDSq (fun θ => fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ))).toReal ≤
          C * (P + 1) := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcol ν i).2.2.2
      rwa [ENNReal.toReal_ofReal (by positivity : 0 ≤ C * (P + 1))] at hh
    intro r hr
    filter_upwards [hs r hr] with ν hν
    rw [(hcol ν i).2.1] at hν
    have hz : quadValue (centerTestHessian d (F ν) (E ν)) (0 : CotangentIndex n → ℂ) = 0 := by
      simp [quadValue]
    rw [hz, mul_zero, zero_sub] at hν
    have hp := mul_le_mul_of_nonneg_left (hsemi ν) (mul_nonneg hCE hε.le)
    linarith only [hν, hp]
  have hsum := seqUpperZero_sum _ hseq
  have heq : (fun ν => ∑ i : CotangentIndex n,
      (-circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ))) -
      CE * ε * (1 + (variationEnergy d j (F ν)).toReal + C * (P + 1)))) =
      (fun ν => -(∑ i, circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (fejerTestColumn d j a (F ν) (E ν) P i (circlePoint θ)))) -
        ((2 * n : ℕ) * CE) * ε * (1 + (variationEnergy d j (F ν)).toReal + C * (P + 1))) := by
    funext ν
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, two_mul]
    ring
  rwa [heq] at hsum

end Yau.Blueprint.V04Proof
