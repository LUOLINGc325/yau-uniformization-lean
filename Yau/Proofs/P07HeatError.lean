import Yau.Proofs.P07HeatGaussianScalar

/-! The uniform Lipschitz error of the actual L² heat, obtained from
explicit Gaussian L² data and their proved lower comparison. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L19Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarClassicalHeat_lipschitz_error_at (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (q : Lp ℝ 2 μ) (x : M.Carrier) (q0 K : ℝ) (hK : 0 < K)
    (hq0 : q0 ∈ Icc (0 : ℝ) 1) (hq : ∀ᵐ y ∂μ, q y ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ᵐ y ∂μ, |q y - q0| ≤ K * inducedDistance g.form x y)
    {t : ℝ} (ht : 0 < t) :
    |scalarClassicalHeat hn g hk μ hμ q x t - q0| ≤ ((n : ℝ) + 1) * K * Real.sqrt t := by
  letI := inducedMetricSpace g
  let δ := Real.sqrt t
  have hδ : 0 < δ := Real.sqrt_pos.2 ht
  have hδ2 : δ ^ 2 = t := Real.sq_sqrt ht.le
  let a := K / (4 * δ)
  have ha : 0 < a := div_pos hK (by positivity)
  have hrel : 4 * a * δ = K := by dsimp only [a]; field_simp
  let G := scalarGaussianL2 g hk hRic μ hμ x a ha
  have hG : G =ᵐ[μ] gaussianWeight g x a := by
    filter_upwards [scalarGaussianL2_coe g hk hRic μ hμ x a ha] with y hy
    change G y = Real.exp (-(a * inducedDistance g.form x y ^ 2))
    simpa only [neg_mul] using hy
  have hmajor : ∀ᵐ y ∂μ, |q y - q0| ≤ K * δ + 2 * (1 - G y) := by
    filter_upwards [hq, hLip, hG] with y hy hl hg
    rw [hg]
    simpa only [gaussianWeight, neg_mul] using
      unit_lipschitz_gaussian_majorant hK hδ ha hrel (show 0 ≤ inducedDistance g.form x y from @dist_nonneg M.Carrier (inducedMetricSpace g).toPseudoMetricSpace x y)
        hy hq0 hl
  have hplus : ∀ᵐ y ∂μ, |(q + (2 : ℝ) • G : Lp ℝ 2 μ) y| ≤ q0 + K * δ + 2 := by
    filter_upwards [hq, hmajor, hG, Lp.coeFn_add q ((2 : ℝ) • G), Lp.coeFn_smul (2 : ℝ) G]
      with y hy hm hg hadd hsmul
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul]
    have hg0 : 0 ≤ G y := by rw [hg]; exact (gaussianWeight_pos g x a y).le
    rw [abs_of_nonneg (by linarith [hy.1])]
    linarith [le_abs_self (q y - q0)]
  have hminus : ∀ᵐ y ∂μ, |(-q + (2 : ℝ) • G : Lp ℝ 2 μ) y| ≤ -q0 + K * δ + 2 := by
    filter_upwards [hq, hmajor, hG, Lp.coeFn_add (-q) ((2 : ℝ) • G),
      Lp.coeFn_neg q, Lp.coeFn_smul (2 : ℝ) G]
      with y hy hm hg hadd hneg hsmul
    rw [hadd, Pi.add_apply, hneg, Pi.neg_apply, hsmul, Pi.smul_apply, smul_eq_mul]
    have hg0 : 0 ≤ G y := by rw [hg]; exact (gaussianWeight_pos g x a y).le
    apply abs_le.mpr
    constructor
    · nlinarith [hq0.2, hy.2, mul_pos hK hδ]
    · linarith [neg_abs_le (q y - q0)]
  have hp := scalarClassicalHeat_linf hn g hk μ hμ (q + (2 : ℝ) • G)
    (K := q0 + K * δ + 2) (by nlinarith [hq0.1, mul_pos hK hδ]) hplus x ht
  have hm := scalarClassicalHeat_linf hn g hk μ hμ (-q + (2 : ℝ) • G)
    (K := -q0 + K * δ + 2) (by nlinarith [hq0.2, mul_pos hK hδ]) hminus x ht
  rw [scalarClassicalHeat_add hn g hk μ hμ q ((2 : ℝ) • G) x ht,
    scalarClassicalHeat_smul hn g hk μ hμ 2 G x ht] at hp
  rw [scalarClassicalHeat_add hn g hk μ hμ (-q) ((2 : ℝ) • G) x ht,
    scalarClassicalHeat_neg hn g hk μ hμ q x ht,
    scalarClassicalHeat_smul hn g hk μ hμ 2 G x ht] at hm
  have habs : |scalarClassicalHeat hn g hk μ hμ q x t - q0| ≤
      K * δ + 2 * (1 - scalarClassicalHeat hn g hk μ hμ G x t) := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (scalarClassicalHeat hn g hk μ hμ q x t +
      2 * scalarClassicalHeat hn g hk μ hμ G x t),
      le_abs_self (-scalarClassicalHeat hn g hk μ hμ q x t +
        2 * scalarClassicalHeat hn g hk μ hμ G x t)]
  have hlow := scalarClassicalGaussianHeat_lower hn g hk hRic μ hμ x ha x ht
  have hcenter : gaussianWeight g x a x = 1 := by
    change Real.exp (-(a * dist x x ^ 2)) = 1
    simp
  rw [hcenter, mul_one] at hlow
  have he := Real.add_one_le_exp (-((2 * n : ℕ) * a * t))
  have hlast : K * δ + 2 * ((2 * n : ℕ) * a * t) = ((n : ℝ) + 1) * K * δ := by
    rw [← hδ2, ← hrel]
    push_cast
    ring
  calc
    _ ≤ K * δ + 2 * (1 - scalarClassicalHeat hn g hk μ hμ G x t) := habs
    _ ≤ K * δ + 2 * ((2 * n : ℕ) * a * t) := by linarith
    _ = _ := hlast

/-- A continuous compact datum is used only through its actual L²
realization; its error constant is independent of the evaluation point. -/
theorem scalarClassicalHeat_lipschitz_error (hn : 0 < n) (g : SmoothMetric M)
    (hk : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (q : Lp ℝ 2 μ) (f : M.Carrier → ℝ) (hq : q =ᵐ[μ] f)
    {K : ℝ} (hK : 0 < K) (h01 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |f x - f y| ≤ K * inducedDistance g.form x y)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    |scalarClassicalHeat hn g hk μ hμ q x t - f x| ≤ ((n : ℝ) + 1) * K * Real.sqrt t := by
  apply scalarClassicalHeat_lipschitz_error_at hn g hk hRic μ hμ q x (f x) K hK (h01 x)
  · filter_upwards [hq] with y hy
    rw [hy]
    exact h01 y
  · filter_upwards [hq] with y hy
    rw [hy, abs_sub_comm]
    exact hLip x y
  · exact ht

end Yau.NodeProofs.P07Aux
