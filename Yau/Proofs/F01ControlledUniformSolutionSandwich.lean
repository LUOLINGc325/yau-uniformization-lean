import Yau.Proofs.F01UniformWeightSandwich
import Yau.Proofs.F01ControlledMajorantWeight
import Yau.Proofs.F01ControlledComparisonQ

/-! The actual smooth Ricci majorant and controlled exhaustion fix
uniform metric/scalar bounds before every existing solution endpoint
and before its preliminary comparison constant. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_uniform_solution_sandwich (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 < D) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ) (T Cpre : ℝ),
      0 < T → 2 * T ≤ D → 1 ≤ Cpre →
      MetricFamilySmooth h (Icc 0 T) → SmoothSpaceTime U (Icc 0 T) →
      h 0 = α → (∀ x, U x 0 = 0) →
      (∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((Cpre⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((Cpre : ℂ) • gMat α x - gMat (h t) x).PosSemidef ∧
        gMat (h t) x = gMat α x - (t : ℂ) • ricci α x + levi (fun y => U y t) x ∧
        HasDerivWithinAt (U x) (flowLogDetRatio α h x t) (Icc 0 T) t) →
      ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef ∧
        |flowLogDetRatio α h x t| ≤ A ∧ |U x t| ≤ A * t := by
  obtain ⟨Lw, hLw, hWeights⟩ := controlled_bounded_majorant_weights X o u hu Ξ hΞ hRic hD.le
  obtain ⟨Lr, hLr, hRayleigh⟩ := controlled_rayleigh_order X o u hu (by norm_num : (0 : ℝ) < 1 / 2)
  let L0 : ℝ := max Lw (max Lr (max 1 (4 * (n : ℝ) * D)))
  have hL0 : 0 < L0 := hLw.trans_le (le_max_left _ _)
  refine ⟨L0, hL0, ?_⟩
  intro L hLL ho
  dsimp only
  have hLwL : Lw ≤ L := (le_max_left _ _).trans hLL
  have hLrL : Lr ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLL
  have hL1 : 1 ≤ L := ((le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans hLL
  have hScale : 4 * (n : ℝ) * D ≤ L := ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans hLL
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  obtain ⟨φ, Mφ, hMφ, hφ, hφlo, hφhi, hWeight⟩ := hWeights L hLwL ho
  obtain ⟨x0, hx0⟩ := (sublevelComponent_isConnected ho).nonempty
  let oN : N.Carrier := ⟨x0, hx0⟩
  obtain ⟨C, A, hC, hA, hUniform⟩ :=
    uniform_solution_sandwich_from_bounded_weight α oN φ hD hL hMφ hScale hφlo
  refine ⟨C, A, hC, hA, ?_⟩
  intro h U T Cpre hT hHalf hCpre hh hU hh0 hU0 hData
  have hQ := controlled_short_time_comparison_Q X o u hu ho h U T Cpre D (1 / 2)
    hT hCpre hD.le (by norm_num) hh hU hh0 hU0
    (fun x t ht => (hData x t ht).1) (fun x t ht => (hData x t ht).2.1)
    (fun s hs x => (hData x s hs).2.2.1) (fun x s hs => (hData x s hs).2.2.2)
    φ hφ hφhi hWeight
  apply hUniform h U T Cpre hT hHalf hh hU0
    (fun x s hs => (hData x s hs).2.2.2) (zero_lt_one.trans_le hCpre)
    (fun x s hs => (hData x s hs).2.1) (fun x s hs => (hQ.2 x s hs).1)
  intro τ hτ hτT
  exact hRayleigh L hLrL ho h U T τ Cpre D hτ hτT hCpre hD.le hh hU hh0 hU0
    (fun x t ht => (hData x t ht).1) (fun x t ht => (hData x t ht).2.1)
    (fun s hs x => (hData x s hs).2.2.1) (fun x s hs => (hData x s hs).2.2.2)
    φ hφ hφhi hWeight

end Yau.NodeProofs.F01Aux
