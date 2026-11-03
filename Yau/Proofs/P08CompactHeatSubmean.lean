import Yau.Proofs.P08HeatBallBarrier
import Yau.LeafProofs.L19HeatClassicalCore

/-! A finite-ball barrier compares a smooth subharmonic scalar of linear
growth with the actual heat of a genuine compact cutoff of that scalar. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem compact_heat_submean_barrier (hn : 0 < n) (g : SmoothMetric M)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (hv0 : ∀ x, 0 ≤ v x)
    (hvΔ : ∀ x, 0 ≤ laplacian g.form v x) {B A R : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbound : ∀ x, v x ≤ B + A * distFrom g.form o x) (hR : 0 < R) :
    ∃ k : ScalarEnergyDomain g μ hμ, (∀ x, 0 ≤ k x ∧ k x ≤ v x) ∧
      ∀ T : ℝ, 0 < T → v o ≤ scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) o T +
        ((B + A * R + 1) / (1 - Real.exp (-1))) *
          (1 - Real.exp (-(((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * T))) := by
  obtain ⟨χ, hχ, hcχ, hχrange, hχone, _⟩ := exists_smooth_compact_cutoff g o hR
    (show R < R + 1 by linarith)
  let k : ScalarEnergyDomain g μ hμ := ⟨fun x => χ x * v x, smoothFn_mul hχ hv, hcχ.mul_right⟩
  have hk (x : M.Carrier) : 0 ≤ k x ∧ k x ≤ v x :=
    ⟨mul_nonneg (hχrange x).1 (hv0 x), mul_le_of_le_one_left (hv0 x) (hχrange x).2⟩
  refine ⟨k, hk, ?_⟩
  intro T hT
  let U := scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k)
  have hU := scalarClassicalHeat_smooth hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k)
  have hU0 (y : M.Carrier) (s : ℝ) (hs : 0 < s) : 0 ≤ U y s := by
    apply scalarClassicalHeat_nonneg hn g hK μ hμ _ ?_ y hs
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ k] with z hz
    rw [hz]
    exact (hk z).1
  have he : 0 < 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  let K : ℝ := (B + A * R + 1) / (1 - Real.exp (-1))
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hKidentity : K * (1 - Real.exp (-1)) = B + A * R + 1 := by
    dsimp only [K]
    exact div_mul_cancel₀ _ he.ne'
  let F : M.Carrier → ℝ → ℝ := fun y s => (1 / K) * U y s + (-1 / K) * v y + 1
  have hform (y : M.Carrier) (s : ℝ) : F y s = 1 + (U y s - v y) / K := by
    dsimp only [F]
    ring
  have hvtime : SmoothSpaceTime (fun y _s => v y) (Set.Ioi 0) := by
    intro a
    exact (hv a).comp contDiffOn_fst (fun _ hp => hp.1)
  have hF : SmoothSpaceTime F (Set.Ioi 0) := by
    intro a
    exact ((contDiffOn_const.mul (hU a)).add (contDiffOn_const.mul (hvtime a))).add contDiffOn_const
  have hsuper (y : M.Carrier) (s : ℝ) (hs : 0 < s) :
      laplacian g.form (fun z => F z s) y ≤ deriv (F y) s := by
    have hUs := smoothSpaceTime_slice hU hs
    have hlin : SmoothFn (fun z => (1 / K) * U z s + (-1 / K) * v z) :=
      fun a => (contDiffOn_const.mul (hUs a)).add (contDiffOn_const.mul (hv a))
    have hd := (scalarClassicalHeat_hasDerivAt hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) y hs).const_mul (1 / K)
    have hder : deriv (F y) s = (1 / K) * laplacian g.form (fun z => U z s) y := by
      have hFeq : F y = (fun t => (1 / K) * U y t + ((-1 / K) * v y + 1)) := by
        funext t
        dsimp only [F]
        ring
      rw [hFeq]
      exact (hd.add_const ((-1 / K) * v y + 1)).deriv
    rw [hder]
    change laplacian g.form (fun z => ((1 / K) * U z s + (-1 / K) * v z) + 1) y ≤ _
    rw [laplacian_add_const g.form hlin 1 y, laplacian_linear_combination g.form hUs hv]
    have hh := mul_nonpos_of_nonpos_of_nonneg (show -1 / K ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hKpos.le) (hvΔ y)
    linarith
  have hinitial : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, 0 < s → s < δ → ∀ y : M.Carrier,
        inducedDistance g.form o y ≤ R → 1 - η ≤ F y s := by
    intro η hη
    obtain ⟨M₀, hM, hLap⟩ := scalarCompactLaplacian_bounded g μ hμ k
    refine ⟨η * K / (M₀ + 1), by positivity, ?_⟩
    intro s hs hsδ y hy
    have hinit := scalarClassicalHeat_compact_initial_bound hn g hK μ hμ k hM hs hLap y
    have hky : k y = v y := by
      change χ y * v y = v y
      rw [hχone y hy, one_mul]
    rw [hky] at hinit
    have hsmall := (lt_div_iff₀ (show 0 < M₀ + 1 by positivity)).mp hsδ
    rw [hform]
    have hlo := (abs_le.mp hinit).1
    apply le_add_of_sub_left_le
    apply (le_div_iff₀ hKpos).mpr
    dsimp only [U] at *
    nlinarith
  have hboundary (y : M.Carrier) (hy : inducedDistance g.form o y = R)
      (s : ℝ) (hs : 0 < s) :
      Real.exp (-(((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * s)) *
        gaussianWeight g o (1 / R ^ 2) y ≤ F y s := by
    have hdecay : Real.exp (-(((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (by positivity)
    have hG : gaussianWeight g o (1 / R ^ 2) y = Real.exp (-1) := by
      rw [gaussianWeight, hy]
      congr 1
      field_simp
    apply (mul_le_mul_of_nonneg_right hdecay (gaussianWeight_pos g o (1 / R ^ 2) y).le).trans
    rw [one_mul, hG, hform]
    have hboundy := hbound y
    change v y ≤ B + A * inducedDistance g.form o y at hboundy
    rw [hy] at hboundy
    have hh := hU0 y s hs
    have heq : 1 + (U y s - v y) / K = (K + U y s - v y) / K := by field_simp; ring
    rw [heq]
    apply (le_div_iff₀ hKpos).mpr
    nlinarith [hKidentity]
  have hcomp := gaussian_finite_ball_supersolution g hK hRic o
    (by positivity : 0 < 1 / R ^ 2) hR (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    hF hsuper hinitial hboundary o
    (by rw [g.induced_distance_eq_zero.mpr rfl]; exact hR.le) hT
  have hGcenter : gaussianWeight g o (1 / R ^ 2) o = 1 := by
    rw [gaussianWeight, g.induced_distance_eq_zero.mpr rfl]
    simp
  rw [hGcenter, mul_one, hform] at hcomp
  have hh := (le_div_iff₀ hKpos).mp (show
    Real.exp (-(((2 * n : ℕ) : ℝ) * (1 / R ^ 2) / (1 - 1 / 2) * T)) - 1 ≤
      (U o T - v o) / K by linarith)
  change v o ≤ U o T + K * _
  nlinarith

end Yau.NodeProofs.P08Aux
