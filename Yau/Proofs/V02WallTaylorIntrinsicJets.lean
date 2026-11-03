import Yau.Proofs.V02WallTaylorParameterJets
import Mathlib.Analysis.Complex.Basic

/-! Joint chart smoothness gives local regularity of the actual parameter
operator jet with every independent auxiliary variable retained. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {Y V P F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def intrinsicParameterJet (B : Y → ℂ × P → F) (m : ℕ) (y : Y) (p : ℂ × P) :
    ℂ [×m]→L[ℝ] F := iteratedFDeriv ℝ m (fun z => B y (z, p.2)) p.1

theorem intrinsicParameterJet_contDiffOn_chart
    {B : Y → ℂ × P → F} {inv : V → Y} {Ω : Set (ℂ × (V × P))} (hΩ : IsOpen Ω)
    (hB : ContDiffOn ℝ ∞ (fun w : ℂ × (V × P) => B (inv w.2.1) (w.1, w.2.2)) Ω)
    (m : ℕ) :
    ContDiffOn ℝ ∞ (fun w : V × (ℂ × P) => intrinsicParameterJet B m (inv w.1) w.2)
      ((fun w : V × (ℂ × P) => (w.2.1, (w.1, w.2.2))) ⁻¹' Ω) := by
  have hT : ContDiff ℝ ∞ (fun w : V × (ℂ × P) => (w.2.1, (w.1, w.2.2))) :=
    (contDiff_fst.comp contDiff_snd).prodMk (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  have hh := (parameterJet_contDiffOn hΩ hB m).comp hT.contDiffOn (fun _ hp => hp)
  apply hh.congr
  intro w hw
  exact (parameterJet_eq_iteratedFDeriv hΩ hB m hw).symm

theorem intrinsicParameterJet_contDiffAt_chart
    {B : Y → ℂ × P → F} {inv : V → Y} {Ω : Set (ℂ × (V × P))} (hΩ : IsOpen Ω)
    (hB : ContDiffOn ℝ ∞ (fun w : ℂ × (V × P) => B (inv w.2.1) (w.1, w.2.2)) Ω)
    (m : ℕ) {u : V} {z : ℂ} {p : P} (hp : (z, (u, p)) ∈ Ω) :
    ContDiffAt ℝ 1 (fun w : V × (ℂ × P) => intrinsicParameterJet B m (inv w.1) w.2)
      (u, (z, p)) := by
  have hT : Continuous (fun w : V × (ℂ × P) => (w.2.1, (w.1, w.2.2))) :=
    (continuous_fst.comp continuous_snd).prodMk (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact ((intrinsicParameterJet_contDiffOn_chart hΩ hB m).contDiffAt
    ((hΩ.preimage hT).mem_nhds hp)).of_le (by simp)

end Yau.Blueprint.V02WallTaylorProof
