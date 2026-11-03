import Yau.Proofs.F01ApproximatingSquareLevi
import Yau.Proofs.F01ControlledMajorantWeight

/-! The actual smooth Ricci majorant admits a square-exhaustion penalty.
The epsilon bound and level threshold precede every realization and shift. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_penalized_majorant_levi (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ ε0 L0 : ℝ, 0 < ε0 ∧ 0 < L0 ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε0 → ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      let N := sublevelManifold X.manifold u hu.1 o L ho
      let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
      ∀ A : ℝ, ∀ x : N.Carrier,
        (gMat α x - (D : ℂ) • ricci α x +
          (D : ℂ) • levi (fun y : N.Carrier => Ξ y.val - ε * u y.val ^ 2 - A) x -
          (((1 / 2 : ℝ) : ℂ)) • gMat α x).PosSemidef := by
  obtain ⟨K, hK, hsquare⟩ := controlled_approximating_square_levi X o u hu
  obtain ⟨G, hG, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  let ε0 := 1 / (4 * (D + 1) * (K + 1))
  let L0 := 4 * D * (n : ℝ) * B + 1
  have hε0 : 0 < ε0 := by dsimp only [ε0]; positivity
  have hL0 : 0 < L0 := by dsimp only [L0]; positivity
  refine ⟨ε0, L0, hε0, hL0, ?_⟩
  intro ε hε hεsmall L hLL0 ho
  dsimp only
  intro A x
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL1 : 1 ≤ L := by
    have hk : 0 ≤ 4 * D * (n : ℝ) * B := by positivity
    dsimp only [L0] at hLL0
    linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have herr : D * (n : ℝ) * (B / L ^ 2) ≤ 1 / 4 := by
    have hlarge : 4 * D * (n : ℝ) * B ≤ L ^ 2 := by
      dsimp only [L0] at hLL0
      nlinarith
    have he : D * (n : ℝ) * (B / L ^ 2) = D * (n : ℝ) * B / L ^ 2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith
  have hpenalty : D * ε * K ≤ 1 / 4 := by
    have hden : 0 < 4 * (D + 1) * (K + 1) := by positivity
    have hsmall := (le_div_iff₀ hden).mp hεsmall
    have hcoef : 4 * D * K ≤ 4 * (D + 1) * (K + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcoef hε
    nlinarith
  have hΞr : SmoothFn (M := N) (fun y => Ξ y.val) :=
    smoothFn_openRestriction X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) hΞ
  have hur : SmoothFn (M := N) (fun y => u y.val) :=
    smoothFn_openRestriction X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) hu.1
  have hu2r : SmoothFn (M := N) (fun y => u y.val ^ 2) := fun a => (hur a).pow 2
  have hεu2 : SmoothFn (M := N) (fun y => ε * u y.val ^ 2) :=
    fun a => contDiffOn_const.mul (hu2r a)
  have hdiff : SmoothFn (M := N) (fun y => Ξ y.val - ε * u y.val ^ 2) :=
    fun a => (hΞr a).sub (hεu2 a)
  have hA : SmoothFn (M := N) (fun _ => A) := fun _ => contDiffOn_const
  have hlevi : levi (fun y : N.Carrier => Ξ y.val - ε * u y.val ^ 2 - A) x =
      levi Ξ x.val - (ε : ℂ) • levi (fun y : N.Carrier => u y.val ^ 2) x := by
    rw [levi_sub_native hdiff hA,
      levi_const_native, sub_zero, levi_sub_native hΞr hεu2,
      levi_const_mul_native hu2r ε]
    exact congrArg
      (fun B : Matrix (Fin n) (Fin n) ℂ => B -
        (ε : ℂ) • levi (fun y : N.Carrier => u y.val ^ 2) x)
      (openRestriction_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) Ξ x)
  have hαpos : (gMat α x).PosDef :=
    LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hremaining : 0 ≤ 1 - 1 / 2 - D * (n : ℝ) * (B / L ^ 2) - D * ε * K := by
    linarith
  have p1 := hαpos.posSemidef.smul (Complex.zero_le_real.mpr hremaining)
  have p2 := ((hbudgets L ho x).2.1).smul
    (Complex.zero_le_real.mpr (mul_nonneg hD hn))
  have p3 := (hRic x.val).smul (Complex.zero_le_real.mpr hD)
  have p4 := (hsquare L ho x).smul (Complex.zero_le_real.mpr (mul_nonneg hD hε))
  rw [approximatingMetric_ricci X.metric.form
    (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) u hu.1 o hL ho x, hlevi]
  convert p3.add (p2.add (p4.add p1)) using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp only [gMat, α]
  push_cast
  ring

end Yau.NodeProofs.F01Aux
