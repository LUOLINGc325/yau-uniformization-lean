import Yau.Proofs.V02RealTaylor

/-! Third parameter jets of the same complete scalar functional, including
its fixed clock constant and its arbitrary real penalty coefficient. -/

open scoped Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof

theorem linear_combination_C3_bound
    {A B L T : ℂ → ℝ} {r MA MB ML MT : ℝ} (ε k : ℝ)
    (hA : ContDiffOn ℝ 3 A (ball 0 r)) (hB : ContDiffOn ℝ 3 B (ball 0 r))
    (hL : ContDiffOn ℝ 3 L (ball 0 r)) (hT : ContDiffOn ℝ 3 T (ball 0 r))
    (hAb : ∀ z ∈ ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 A z‖ ≤ MA)
    (hBb : ∀ z ∈ ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 B z‖ ≤ MB)
    (hLb : ∀ z ∈ ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 L z‖ ≤ ML)
    (hTb : ∀ z ∈ ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 T z‖ ≤ MT) :
    ContDiffOn ℝ 3 (fun z => B z + ε * (A z + k + L z) - T z) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r,
        ‖iteratedFDeriv ℝ 3 (fun w => B w + ε * (A w + k + L w) - T w) z‖ ≤
          MB + |ε| * (MA + ML) + MT := by
  have hs : ContDiffOn ℝ 3 (fun z => A z + k + L z) (ball 0 r) :=
    (hA.add contDiffOn_const).add hL
  refine ⟨(hB.add (contDiffOn_const.mul hs)).sub hT, fun z hz => ?_⟩
  have ha := hA.contDiffAt (isOpen_ball.mem_nhds hz)
  have hb := hB.contDiffAt (isOpen_ball.mem_nhds hz)
  have hl := hL.contDiffAt (isOpen_ball.mem_nhds hz)
  have ht := hT.contDiffAt (isOpen_ball.mem_nhds hz)
  have hk : ContDiffAt ℝ 3 (fun _ : ℂ => k) z := contDiffAt_const
  have hsum : iteratedFDeriv ℝ 3 (fun w => A w + k + L w) z =
      iteratedFDeriv ℝ 3 A z + iteratedFDeriv ℝ 3 L z := by
    have houter := iteratedFDeriv_add_apply (f := fun w : ℂ => A w + k) (g := L)
      (ha.add hk) hl
    have hinner := iteratedFDeriv_add_apply (f := A) (g := fun _ : ℂ => k) ha hk
    simp only [Pi.add_def] at houter hinner
    have hc : iteratedFDeriv ℝ 3 (fun _ : ℂ => k) z = 0 :=
      congrFun (iteratedFDeriv_succ_const (𝕜 := ℝ) (E := ℂ) 2 k) z
    rw [hinner, hc, add_zero] at houter
    exact houter
  have heq : iteratedFDeriv ℝ 3 (fun w => B w + ε * (A w + k + L w) - T w) z =
      iteratedFDeriv ℝ 3 B z +
        ε • (iteratedFDeriv ℝ 3 A z + iteratedFDeriv ℝ 3 L z) -
          iteratedFDeriv ℝ 3 T z := by
    have hsa := hs.contDiffAt (isOpen_ball.mem_nhds hz)
    have hε : ContDiffAt ℝ 3 (fun _ : ℂ => ε) z := contDiffAt_const
    have hmul : iteratedFDeriv ℝ 3 (fun w => ε * (A w + k + L w)) z =
        ε • iteratedFDeriv ℝ 3 (fun w => A w + k + L w) z := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        iteratedFDeriv_const_smul_apply (a := ε) hsa
    have hadd := iteratedFDeriv_add_apply (f := B)
      (g := fun w : ℂ => ε * (A w + k + L w)) hb (hε.mul hsa)
    have hsub := iteratedFDeriv_sub_apply
      (f := fun w : ℂ => B w + ε * (A w + k + L w)) (g := T)
      (hb.add (hε.mul hsa)) ht
    simp only [Pi.add_def] at hadd
    simp only [Pi.sub_def] at hsub
    rw [hadd, hmul, hsum] at hsub
    exact hsub
  rw [heq]
  calc
    _ ≤ ‖iteratedFDeriv ℝ 3 B z +
        ε • (iteratedFDeriv ℝ 3 A z + iteratedFDeriv ℝ 3 L z)‖ +
          ‖iteratedFDeriv ℝ 3 T z‖ := norm_sub_le _ _
    _ ≤ (‖iteratedFDeriv ℝ 3 B z‖ +
        |ε| * (‖iteratedFDeriv ℝ 3 A z‖ + ‖iteratedFDeriv ℝ 3 L z‖)) +
          ‖iteratedFDeriv ℝ 3 T z‖ := by
      have hm : ‖ε • (iteratedFDeriv ℝ 3 A z + iteratedFDeriv ℝ 3 L z)‖ ≤
          |ε| * (‖iteratedFDeriv ℝ 3 A z‖ + ‖iteratedFDeriv ℝ 3 L z‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg ε)
      exact add_le_add ((norm_add_le _ _).trans (add_le_add (le_refl _) hm)) (le_refl _)
    _ ≤ MB + |ε| * (MA + ML) + MT :=
      add_le_add (add_le_add (hBb z hz)
        (mul_le_mul_of_nonneg_left (add_le_add (hAb z hz) (hLb z hz)) (abs_nonneg ε)))
        (hTb z hz)

end Yau.Blueprint.V02Proof
