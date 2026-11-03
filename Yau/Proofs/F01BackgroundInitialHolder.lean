import Yau.Proofs.F01BackgroundRealificationJets
import Yau.Proofs.F01DilatedCoefficientHolder
import Yau.Proofs.F01SpatialDilationLevi

/-! The genuine bounded-geometry chart family supplies the two original
initial-surface Holder inputs, with one budget before all chart centers and
all smaller parabolic spatial scales. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance initialHolderSymNormedSpace (n : ℕ) : NormedSpace ℝ (Sym n) where
  toModule := inferInstance
  norm_smul_le c A := norm_smul_le c (A : Mat n)

local instance initialHolderSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem holderBound_mono_const {V : Type*} [NormedAddCommGroup V]
    {F : Point n → V} {β C D : ℝ} {Q : Set (Point n)}
    (hF : HolderBound β Q F C) (hCD : C ≤ D) : HolderBound β Q F D := by
  refine ⟨hF.1.trans hCD, fun p hp => (hF.2.1 p hp).trans hCD, ?_⟩
  intro p hp q hq
  refine (hF.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hCD ?_)
  unfold holderWeight
  positivity

theorem clampedBackground_spatial_dilation
    (A : Space n → Matrix (Fin n) (Fin n) ℂ) {ρ : ℝ} {p : Point n}
    (hA : ContDiffAt ℝ 2 (fun w => Real.log (A w).det.re) (ρ • p.1)) :
    clampedBackground (fun w => A (ρ • w)) p =
      iota (A (ρ • p.1)) + max p.2 0 • (-(ρ ^ 2) • iota (backgroundRicci A (ρ • p.1))) := by
  rw [clampedBackground, backgroundRicci_spatial_dilation A hA, smul_smul,
    ← Complex.ofReal_mul, iota_sub, iota_real_smul, mul_smul]
  module

theorem bounded_geometry_initial_holder (A : BoundedChartFamily g) {α β : ℝ}
    (hα : α ≤ 1) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ p : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (clampedBackground (fun z => pullbackMatrix g (A.chart p) (ρ • z))) K ∧
      HolderBound α (cylinder (ball (0 : Space n) 1) (-1) 1)
        (backgroundSource (fun z => pullbackMatrix g (A.chart p) (ρ • z))) K := by
  obtain ⟨Kb, hKb, hb⟩ := dilated_affine_holder_budget
    (realified_background_uniform_jets A 1) (realified_backgroundRicci_uniform_jets A 1)
    (realified_background_smooth A) (realified_backgroundRicci_smooth A) hβ
  obtain ⟨Ks, hKs, hs⟩ := dilated_spatial_holder_budget
    (A.backgroundLogDet_uniformJetBounds 1) A.backgroundLogDet_smooth hα
  refine ⟨Kb + Ks, by positivity, ?_⟩
  intro ρ hρ hρr hρ1 p
  have hκ : |-(ρ ^ 2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hmap {x : Space n} (hx : x ∈ ball (0 : Space n) 1) :
      ρ • x ∈ ball (0 : Space n) A.radius := by
    have hx1 : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hx1 hρ).trans_le (by simpa using hρr)
  have hid (q : Point n) (hq : q ∈ cylinder (ball (0 : Space n) 1) (-1) 1) :=
    clampedBackground_spatial_dilation (pullbackMatrix g (A.chart p))
      (((A.backgroundLogDet_smooth p).contDiffAt
        (isOpen_ball.mem_nhds (hmap hq.1))).of_le (by simp))
  have hbg := hb ρ hρ hρr hρ1 (-(ρ ^ 2)) hκ p
  have hsource := holderBound_neg (hs ρ hρ hρr hρ1 p)
  constructor
  · apply holderBound_mono_const (C := Kb) (D := Kb + Ks) ?_ (by linarith)
    refine ⟨hbg.1, ?_, ?_⟩
    · intro q hq
      rw [hid q hq]
      exact hbg.2.1 q hq
    · intro q hq q' hq'
      rw [hid q hq, hid q' hq']
      exact hbg.2.2 q hq q' hq'
  · exact holderBound_mono_const hsource (by linarith)

end Yau.NodeProofs.F01Aux
