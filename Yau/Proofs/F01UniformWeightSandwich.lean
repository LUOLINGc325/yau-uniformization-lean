import Yau.Proofs.F01AsymmetricSandwichConstant
import Yau.Proofs.F01FixedTimeRayleighCap
import Yau.Proofs.F01ComparisonTwoSidedMetric

/-! One bounded actual comparison weight fixes a coarse sandwich and
scalar budget before every existing solution and its preliminary bound. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem uniform_solution_sandwich_from_bounded_weight
    (g : HermitianField M) (o : M.Carrier) (φ : M.Carrier → ℝ)
    {D L Mφ : ℝ} (hD : 0 < D) (hL : 0 < L) (hMφ : 0 ≤ Mφ)
    (hscale : 4 * (n : ℝ) * D ≤ L) (hφ : ∀ x, -Mφ ≤ φ x) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T Cpre : ℝ),
      0 < T → 2 * T ≤ D → MetricFamilySmooth h (Icc 0 T) →
      (∀ x, U x 0 = 0) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s) →
      0 < Cpre →
      (∀ x s, s ∈ Icc 0 T → ((Cpre : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      (∀ x s, s ∈ Icc 0 T → 0 ≤ comparisonFunction D n U (flowLogDetRatio g h) φ x s) →
      (∀ τ, 0 < τ → τ < T → ∀ x s, s ∈ Icc 0 τ →
        ((Real.exp (rayleighPenalty L⁻¹
          (comparisonFunction D n U (flowLogDetRatio g h) φ x s)) : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef ∧
        |flowLogDetRatio g h x t| ≤ A ∧ |U x t| ≤ A * t := by
  let B : ℝ := 4 * D * (Mφ + n) / L
  let A : ℝ := 2 * Mφ + (n : ℝ) * B + n
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨C, hC, hPack⟩ := exists_relative_sandwich_constant (ι := Fin n)
    (a := Real.exp (-(A + (n : ℝ) * B))) (b := Real.exp B) (Real.exp_pos _)
  refine ⟨C, A, hC, hA, ?_⟩
  intro h U T Cpre hT hHalf hh hU0 hpde hCpre hpre hQ hRayleigh
  have hUpper : ∀ x t, t ∈ Icc 0 T → ((Real.exp B : ℂ) • gMat g x - gMat (h t) x).PosSemidef := by
    apply closed_metric_upper_order_of_interior g h hT hh
    intro x t ht
    let τ : ℝ := (t + T) / 2
    have hτ : 0 < τ := by dsimp only [τ]; linarith [ht.1]
    have hτT : τ < T := by dsimp only [τ]; linarith [ht.2]
    have htτ : t ≤ τ := by dsimp only [τ]; linarith [ht.2]
    have hSub : Icc 0 τ ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans hτT.le⟩
    exact fixed_time_rayleigh_cap_from_comparison g h U φ o hτ.le (by linarith) hL hMφ hscale hU0
      (fun y s hs => (hpde y s (hSub hs)).mono hSub) hCpre
      (fun y s hs => hpre y s (hSub hs)) hφ (fun y s hs => hQ y s (hSub hs))
      (hRayleigh τ hτ hτT) x t ⟨ht.1.le, htτ⟩
  have hBoth := two_sided_metric_of_nonnegative_comparison g h U φ hT.le hD hHalf hB hMφ
    hU0 hpde hUpper hφ hQ
  intro x t ht
  have hx := hBoth x t ht
  have hgPos : (gMat g x).PosSemidef :=
    (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hOrders := hPack (gMat g x) (gMat (h t) x) hgPos hx.1 hx.2.1
  exact ⟨hOrders.1, hOrders.2, hx.2.2⟩

end Yau.NodeProofs.F01Aux
