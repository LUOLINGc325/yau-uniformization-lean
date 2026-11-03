import Yau.Proofs.P03CutoffPoleLevi
import Yau.Proofs.P03CompactLeviCoercivity

open scoped Topology ContDiff Matrix ComplexOrder
open Set Metric

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

/-- One multiple of a genuine strictly psh background absorbs every member
of the cutoff logarithmic regularization sequence. -/
theorem exists_pole_strictifier {n : ℕ} (a : ComplexVector n) (b : ContDiffBump a)
    (c : ℝ) (hc : 0 ≤ c) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (f : ComplexVector n → ℝ) (hf : ContDiffOn ℝ ∞ f O)
    (hpos : ∀ z ∈ O, (leviC f z).PosDef) (hball : closedBall a b.rOut ⊆ O) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ j : ℕ, ∀ z ∈ O, ∀ v,
      complexLeviQuadratic f z v ≤ complexLeviQuadratic
        (fun y => k * f y + cutoffPoleRegularization c b a (poleEpsilon j) y) z v := by
  let K := closedBall a b.rOut \ ball a b.rIn
  have hK : IsCompact K := (isCompact_closedBall a b.rOut).diff isOpen_ball
  have hKO : K ⊆ O := fun _ hz => hball hz.1
  obtain ⟨δ, hδ, hlower⟩ := exists_uniform_levi_lower_bound_on_compact
    hO hf hK hKO (fun z hz => hpos z (hKO hz))
  obtain ⟨C, hC, hbelow⟩ := exists_cutoffPole_uniform_levi_lower a b c hc
  let k := 1 + C / δ
  have hk : 1 ≤ k := by dsimp only [k]; exact le_add_of_nonneg_right (div_nonneg hC hδ.le)
  refine ⟨k, hk, ?_⟩
  intro j z hz v
  have hfz : ContDiffAt ℝ 2 f z := (hf.contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  have hpz : ContDiffAt ℝ 2
      (cutoffPoleRegularization c b a (poleEpsilon j)) z :=
    (cutoffPoleRegularization_contDiff c b b.contDiff a (poleEpsilon_pos j)).contDiffAt.of_le
      (by simp)
  rw [complexLeviQuadratic_add (contDiffAt_const.mul hfz) hpz,
    complexLeviQuadratic_const_mul hfz]
  by_cases hzK : z ∈ K
  · have hmain : C * ‖v‖ ^ 2 ≤ (C / δ) * complexLeviQuadratic f z v := by
      have h := mul_le_mul_of_nonneg_left (hlower z hzK v) (div_nonneg hC hδ.le)
      have he : (C / δ) * (δ * ‖v‖ ^ 2) = C * ‖v‖ ^ 2 := by
        field_simp
      rwa [he] at h
    have herr := hbelow j z v
    dsimp only [k]
    nlinarith
  · have hpole := cutoffPole_complexLevi_nonneg_off_annulus a z v b c hc
      (poleEpsilon_pos j) hzK
    have hbackground : 0 ≤ complexLeviQuadratic f z v :=
      (leviC_posSemidef_iff hfz).mp (hpos z hz).posSemidef v
    have hscale := mul_nonneg (div_nonneg hC hδ.le) hbackground
    dsimp only [k]
    nlinarith

end Yau.NodeProofs.P03Aux
