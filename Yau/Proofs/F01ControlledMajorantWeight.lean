import Yau.Proofs.F01ControlledConformalBounds
import Yau.Proofs.F01ApproximatingRicci
import Yau.Proofs.F01LaplacianLinearity

/-! An actual original smooth Ricci majorant becomes a bounded admissible
weight on each compactly contained approximation. The threshold is chosen
before the level; no bound for the majorant is assumed. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_bounded_majorant_weights (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    ∃ (φ : N.Carrier → ℝ) (Mφ : ℝ), 0 ≤ Mφ ∧ SmoothFn φ ∧
      (∀ x, -Mφ ≤ φ x) ∧ (∀ x, φ x ≤ 0) ∧
      ∀ x, (gMat α x - (D : ℂ) • ricci α x + (D : ℂ) • levi φ x -
        (((1 / 2 : ℝ) : ℂ)) • gMat α x).PosSemidef := by
  obtain ⟨A, hA, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  let L0 := 2 * D * (n : ℝ) * B + 1
  have hL0 : 0 < L0 := by dsimp only [L0]; positivity
  refine ⟨L0, hL0, ?_⟩
  intro L hLL0 ho
  dsimp only
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let f := approximatingScalar X.manifold u hu.1 o L ho
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL1 : 1 ≤ L := by
    have hk : 0 ≤ 2 * D * (n : ℝ) * B := by positivity
    dsimp only [L0] at hLL0
    linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have herr : D * (n : ℝ) * (B / L ^ 2) ≤ 1 / 2 := by
    have hlarge : 2 * D * (n : ℝ) * B ≤ L ^ 2 := by
      dsimp only [L0] at hLL0
      nlinarith
    have he : D * (n : ℝ) * (B / L ^ 2) = D * (n : ℝ) * B / L ^ 2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith
  obtain ⟨b, hb⟩ := (hu.2.1 L).exists_bound_of_continuousOn (continuous_of_smoothFn hΞ).continuousOn
  let K := |b| + 1
  let φ : N.Carrier → ℝ := fun x => Ξ x.val - K
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hΞr : SmoothFn (M := N) (fun x => Ξ x.val) := smoothFn_openRestriction X.manifold
    (sublevelOpens X.manifold u hu.1 o L) (sublevelComponent_isConnected ho) hΞ
  have hφ : SmoothFn φ := fun a => (hΞr a).sub contDiffOn_const
  have hbounds (x : N.Carrier) : -K ≤ Ξ x.val ∧ Ξ x.val ≤ K := by
    have hxb := hb x.val (sublevelManifold_point_level X.manifold u hu.1 o L ho x).le
    have hxabs : |Ξ x.val| ≤ b := by simpa only [Real.norm_eq_abs] using hxb
    have hbK : b ≤ K := (le_abs_self b).trans (by dsimp only [K]; linarith)
    exact abs_le.mp (hxabs.trans hbK)
  refine ⟨φ, 2 * K, by positivity, hφ,
    (fun x => by dsimp only [φ]; linarith [(hbounds x).1]),
    (fun x => sub_nonpos.mpr (hbounds x).2), ?_⟩
  intro x
  have hφLevi : levi φ x = levi Ξ x.val := by
    rw [levi_sub_native hΞr (fun _ => contDiffOn_const), levi_const_native, sub_zero]
    exact openRestriction_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) Ξ x
  have hαpos := Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hremaining : 0 ≤ 1 - 1 / 2 - D * (n : ℝ) * (B / L ^ 2) := by linarith
  have p1 := hαpos.posSemidef.smul (Complex.zero_le_real.mpr hremaining)
  have p2 := ((hbudgets L ho x).2.1).smul
    (Complex.zero_le_real.mpr (mul_nonneg hD hn))
  have p3 := (hRic x.val).smul (Complex.zero_le_real.mpr hD)
  rw [approximatingMetric_ricci X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) u hu.1 o hL ho x, hφLevi]
  convert p3.add (p2.add p1) using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp only [gMat, α]
  push_cast
  ring

end Yau.NodeProofs.F01Aux
