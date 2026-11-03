import Yau.Proofs.V02AreaTaylorQuadratic
import Yau.Proofs.V03TwoFormPullback

/-! The complex diagonal of a genuine real bilinear pullback is quadratic
in the original disc velocity. Its actual parameter jets are uniformly bounded
on compact position ranges before any input disc is selected. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau.Blueprint.V03Proof

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

def complexDiagonal (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : ℝ :=
  (1 / 2 : ℝ) * (B v (Complex.I • v) - B (Complex.I • v) v)

theorem complexDiagonal_eq_twoForm (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    complexDiagonal B v = bilinearTwoForm B ![v, Complex.I • v] :=
  (bilinearTwoForm_apply B v (Complex.I • v)).symm

theorem complexDiagonal_real_smul (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (t : ℝ) :
    complexDiagonal B (t • v) = t ^ 2 * complexDiagonal B v := by
  have hI : Complex.I • (t • v) = t • (Complex.I • v) := smul_comm _ _ _
  simp only [complexDiagonal, hI, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem complexDiagonal_joint_contDiffOn {O : Set (ℂ × D)}
    {B : ℂ × D → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiffOn ℝ ∞ B O) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (D × E) => complexDiagonal (B (p.1, p.2.1)) p.2.2)
      {p | (p.1, p.2.1) ∈ O} := by
  have hpos : ContDiff ℝ ∞ (fun p : ℂ × (D × E) => (p.1, p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hcoef := hB.comp hpos.contDiffOn (fun p hp => hp)
  have hv : ContDiffOn ℝ ∞ (fun p : ℂ × (D × E) => p.2.2)
      {p | (p.1, p.2.1) ∈ O} := (contDiff_snd.comp contDiff_snd).contDiffOn
  have hIv := (contDiffOn_const (c := Complex.I)).smul hv
  exact contDiffOn_const.mul
    (((hcoef.clm_apply hv).clm_apply hIv).sub ((hcoef.clm_apply hIv).clm_apply hv))

theorem compact_bilinear_parameter_jet_bound {O : Set (ℂ × D)} (hO : IsOpen O)
    {B : ℂ × D → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiffOn ℝ ∞ B O)
    {K : Set (ℂ × D)} (hK : IsCompact K) (hKO : K ⊆ O) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v : E,
      ‖iteratedFDeriv ℝ k (fun z => complexDiagonal (B (z, p.2)) v) p.1‖ ≤
        C * ‖v‖ ^ 2 := by
  exact compact_quadratic_parameter_jet_bound hO (complexDiagonal_joint_contDiffOn hB)
    (fun p _ v t => complexDiagonal_real_smul (B p) v t) hK hKO k

end Yau.Blueprint.V02AreaTaylorProof
