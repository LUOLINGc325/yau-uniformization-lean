import Yau.Proofs.F01ACompactLocalSchauder
import Yau.Proofs.F01BackgroundInitialHolder
import Yau.Proofs.F01ScalarSymbolSmooth
import Yau.Proofs.F01ZeroSpatialJetHolder

/-! The original initial-surface coefficients have fixed local Holder
constants on a compact original chart. This supplies the scalar boundary
of the initial Schauder estimate without an approximating chart family. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

local instance compactInitialSymNormedSpace (n : ℕ) : NormedSpace ℝ (Sym n) where
  toModule := inferInstance
  norm_smul_le c A := norm_smul_le c (A : Mat n)

local instance compactInitialSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

theorem iota_comp_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ContDiffOn ℝ ∞ G Ω) : ContDiffOn ℝ ∞ (fun z => iota (G z)) Ω := by
  have harray : ContDiffOn ℝ ∞ (fun z (ij : Fin n × Fin n) => G z ij.1 ij.2) Ω :=
    contDiffOn_pi.mpr (fun ij => (frobeniusComplexEntryCLM ij.1 ij.2).contDiff.comp_contDiffOn hG)
  exact iotaArrayCLM.contDiff.comp_contDiffOn harray

theorem fixed_original_chart_initial_holder_budgets
    (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r α β : ℝ} (hball : closedBall 0 r ⊆ e.source) (hα : α ≤ 1) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 →
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (clampedBackground (fun z => pullbackMatrix g e (ρ • z))) K ∧
      HolderBound α (cylinder (ball (0 : Space n) 1) (-1) 1)
        (backgroundSource (fun z => pullbackMatrix g e (ρ • z))) K := by
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  obtain ⟨hG, hRic, hq⟩ := original_chart_background_smooth g hg e he hei
  obtain ⟨Kb, hKb, hBackground⟩ := fixed_compact_initial_coefficient_budgets e.open_source hball
    (iota_comp_contDiffOn hG) (iota_comp_contDiffOn hRic) hβ
  obtain ⟨Ks, hKs, hSource⟩ := fixed_compact_initial_coefficient_budgets e.open_source hball hq hq hα
  refine ⟨Kb 0 + Ks 0, add_pos (hKb 0) (hKs 0), ?_⟩
  intro ρ hρ hρr hρ1
  have hκ : |-(ρ ^ 2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hbg : HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
      (fun p => iota (G (ρ • p.1)) + max p.2 0 • (-(ρ ^ 2) • iota (backgroundRicci G (ρ • p.1)))) (Kb 0) :=
    holderBound_from_zero_spatial_jet (hBackground 0 ρ hρ hρr hρ1 (-(ρ ^ 2)) hκ)
  have hqs : HolderBound α (cylinder (ball (0 : Space n) 1) (-1) 1)
      (fun p => Real.log (G (ρ • p.1)).det.re) (Ks 0) := by
    apply holderBound_from_zero_spatial_jet
    simpa only [zero_smul, smul_zero, add_zero] using hSource 0 ρ hρ hρr hρ1 0 (by norm_num)
  have hmap {z : Space n} (hz : z ∈ ball 0 1) : ρ • z ∈ e.source :=
    hball (ball_subset_closedBall (spatialDilation_mem_ball hρ hρr hz))
  have hEq (p : Point n) (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
      clampedBackground (fun z => G (ρ • z)) p =
        iota (G (ρ • p.1)) + max p.2 0 • (-(ρ ^ 2) • iota (backgroundRicci G (ρ • p.1))) :=
    clampedBackground_spatial_dilation G
      ((hq.contDiffAt (e.open_source.mem_nhds (hmap hp.1))).of_le (by simp))
  constructor
  · apply holderBound_mono_const (C := Kb 0) (D := Kb 0 + Ks 0) ?_ (by linarith [hKs 0])
    apply holderBound_congr_on_native hbg
    exact fun p hp => (hEq p hp).symm
  · exact holderBound_mono_const (holderBound_neg hqs) (by linarith [hKb 0])

end Yau.NodeProofs.F01Aux
