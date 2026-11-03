import Yau.Proofs.F01PenalizedMajorantLevi
import Yau.Proofs.F01ActualGrowthShifts

/-! Actual penalized Ricci-majorant weights. Their shift has the genuine
epsilon-to-the-minus-three growth, while epsilon and level thresholds are
selected before every approximation manifold. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

def penalizedMajorantWeight {A : Type*} (Ξ u : A → ℝ) (c K ε : ℝ) (x : A) : ℝ :=
  Ξ x - ε * u x ^ 2 - majorantGrowthShift c K ε

theorem controlled_penalized_majorant_weights (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c D : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2))) :
    ∃ K ε0 L0 : ℝ, 0 < K ∧ 0 < ε0 ∧ 0 < L0 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      let N := sublevelManifold X.manifold u hu.1 o L ho
      let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
      let φ : N.Carrier → ℝ := fun x => penalizedMajorantWeight Ξ u c K ε x.val
      ∃ Mφ : ℝ, 0 ≤ Mφ ∧ SmoothFn φ ∧ (∀ x, -Mφ ≤ φ x) ∧
        (∀ x, φ x ≤ 0) ∧ ∀ x,
          (gMat α x - (D : ℂ) • ricci α x + (D : ℂ) • levi φ x -
            (((1 / 2 : ℝ) : ℂ)) • gMat α x).PosSemidef := by
  obtain ⟨K, hK, hcontrolled⟩ := hu.2.2.2
  obtain ⟨ε0, L0, hε0, hL0, hweights⟩ :=
    controlled_penalized_majorant_levi X o u hu Ξ hΞ hRic hD
  refine ⟨K, ε0, L0, hK, hε0, hL0, ?_⟩
  intro ε hε hεsmall L hL ho
  dsimp only
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let W : Pt X → ℝ := penalizedMajorantWeight Ξ u c K ε
  have hW : SmoothFn W := fun a =>
    ((hΞ a).sub (contDiffOn_const.mul ((hu.1 a).pow 2))).sub contDiffOn_const
  have hWr : SmoothFn (M := N) (fun x => W x.val) :=
    smoothFn_openRestriction X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) hW
  obtain ⟨b, hb⟩ := (hu.2.1 L).exists_bound_of_continuousOn
    (continuous_of_smoothFn hW).continuousOn
  let Mφ := |b| + 1
  have hMφ : 0 ≤ Mφ := by dsimp only [Mφ]; positivity
  have hlo (x : N.Carrier) : -Mφ ≤ W x.val := by
    have hxb := hb x.val (sublevelManifold_point_level X.manifold u hu.1 o L ho x).le
    have habs : |W x.val| ≤ b := by simpa only [Real.norm_eq_abs] using hxb
    have hneg := neg_abs_le (W x.val)
    have hbabs := le_abs_self b
    dsimp only [Mφ]
    linarith
  refine ⟨Mφ, hMφ, hWr, hlo, ?_, ?_⟩
  · intro x
    have hcompare : 1 + distFrom X.metric.form o x.val ≤ K * u x.val := by
      calc
        _ = K * (K⁻¹ * (1 + distFrom X.metric.form o x.val)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
        _ ≤ K * u x.val := mul_le_mul_of_nonneg_left (hcontrolled x.val).1 hK.le
    exact majorantGrowthShift_controls hc hK hε (X.metric.induced_distance_nonneg o x.val)
      hcompare (hgrowth x.val)
  · intro x
    exact hweights ε hε.le hεsmall L hL ho (majorantGrowthShift c K ε) x

end Yau.NodeProofs.F01Aux
