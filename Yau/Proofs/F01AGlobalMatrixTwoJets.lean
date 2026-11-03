import Yau.Proofs.F01AInitialMatrixJets
import Yau.Proofs.F01NativeBackwardMatrixJets
import Yau.Proofs.F01InverseTensorDilation
import Yau.Proofs.F01ChartGramSmooth

/-! Initial and backward patches overlap. They give one actual finite
global matrix two-jet bound on a fixed closed slab, including both faces. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_global_matrix_two_jet_bound
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T C ρ : ℝ} (hT : 0 < T) (hC : 1 ≤ C) (hρ : 0 < ρ)
    (hρr : 4 * ρ ≤ A.radius) (hρ1 : 4 * ρ ≤ 1) (hρT : (4 * ρ) ^ 2 ≤ T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hh0 : h 0 = g) (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∃ R : ℝ, 0 < R ∧ ∀ x t, t ∈ Icc 0 T → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ k.val (fun z => pullbackMatrix (h t) (A.chart x) z) 0‖ ≤ R := by
  classical
  have hρAr : ρ ≤ A.radius := by linarith [hρ.le]
  have hρOne : ρ ≤ 1 := by linarith [hρ.le]
  obtain ⟨Ki, hKi, hInit⟩ := normalized_initial_matrix_jet_budgets g hg A hC
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨Kb, hKb, hBack⟩ := native_backward_matrix_jet_budgets g hg A hρ hρAr hρOne hT.le hC
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hInitScale : 0 < 2 * ρ := by positivity
  have hBackScale : 0 < ρ * (1 / 4) := by positivity
  choose Ii hIi hInverseInit using fun k : Fin 3 =>
    inverse_spatial_jet_budget (E := Space n) (F := Matrix (Fin n) (Fin n) ℂ) k.val hInitScale.ne'
  choose Ib hIb hInverseBack using fun k : Fin 3 =>
    inverse_spatial_jet_budget (E := Space n) (F := Matrix (Fin n) (Fin n) ℂ) k.val hBackScale.ne'
  let B : Fin 3 → ℝ := fun k => max (Ii k * Ki k.val) (Ib k * Kb k.val)
  have hB (k : Fin 3) : 0 < B k := (mul_pos (hIi k) (hKi k.val)).trans_le (le_max_left _ _)
  have hsum : 0 ≤ ∑ k, B k := Finset.sum_nonneg (fun k _ => (hB k).le)
  refine ⟨1 + ∑ k, B k, by linarith, ?_⟩
  intro x t ht k
  have hR : B k ≤ 1 + ∑ k, B k := by
    have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun l _ => (hB l).le) (Finset.mem_univ k)
    linarith
  have hz : (0 : Space n) ∈ ball 0 A.radius := mem_ball_self A.radius_pos
  have hH : ContDiffOn ℝ ∞ (fun z => pullbackMatrix (h t) (A.chart x) z) (ball 0 A.radius) :=
    matrix_contDiffOn_of_entries (fun i j =>
      (pullbackMatrix_entry_contDiffOn (h t) (metricFamilySmooth_slice hh ht) (A.chart x)
        (A.differentiable x) i j).mono (ball_subset_closedBall.trans (A.closedBall_source x)))
  by_cases hearly : t ≤ 2 * ρ ^ 2
  · let s : ℝ := t / (2 * ρ) ^ 2
    have hs : s ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
      have hd : 0 < (2 * ρ) ^ 2 := sq_pos_of_pos hInitScale
      have h0 : 0 ≤ s := div_nonneg ht.1 hd.le
      have h1 : s ≤ 1 / 2 := (div_le_iff₀ hd).mpr (by nlinarith)
      exact ⟨by linarith, h1⟩
    have hclock : (2 * ρ) ^ 2 * max s 0 = t := by
      rw [max_eq_left (div_nonneg ht.1 (sq_nonneg _))]
      field_simp [hInitScale.ne']
    have hj := hInit k.val h U T (2 * ρ) hInitScale (by nlinarith) (by nlinarith)
      (by nlinarith) hU hh0 hU0 hpot hpde hflow x
    have hScaled := hj.2.1 ((0 : Space n), s) ⟨mem_ball_self (by norm_num), hs⟩
    change ‖iteratedFDeriv ℝ k.val
      (fun z => pullbackMatrix (h ((2 * ρ) ^ 2 * max s 0)) (A.chart x) ((2 * ρ) • z)) 0‖ ≤ Ki k.val at hScaled
    rw [hclock] at hScaled
    have hb := hInverseInit k (ball 0 A.radius) (fun z => pullbackMatrix (h t) (A.chart x) z)
      0 (Ki k.val) isOpen_ball hH (by simpa only [smul_zero] using hz) hScaled
    simp only [smul_zero] at hb
    exact hb.trans ((le_max_left _ _).trans hR)
  · have htLower : ρ ^ 2 ≤ t := by nlinarith [sq_nonneg ρ]
    have hj := hBack k.val h U T t le_rfl htLower ht.2 hU hU0 hpot hpde hflow x
    have hScaled : ‖iteratedFDeriv ℝ k.val
        (fun z => pullbackMatrix (h t) (A.chart x) ((ρ * (1 / 4)) • z)) 0‖ ≤ Kb k.val := by
      simpa only [mul_zero, add_zero] using
        hj.2.1 ((0 : Space n), (0 : ℝ)) ⟨mem_ball_self (by norm_num), by norm_num, le_rfl⟩
    have hb := hInverseBack k (ball 0 A.radius) (fun z => pullbackMatrix (h t) (A.chart x) z)
      0 (Kb k.val) isOpen_ball hH (by simpa only [smul_zero] using hz) hScaled
    simp only [smul_zero] at hb
    exact hb.trans ((le_max_right _ _).trans hR)

end Yau.NodeProofs.F01Aux
