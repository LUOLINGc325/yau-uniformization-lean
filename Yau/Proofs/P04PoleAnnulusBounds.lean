import Yau.Proofs.P04JointLeviContinuity
import Yau.Proofs.P04CompactQuadraticBounds

noncomputable section
open Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

def poleAnnulus (z₀ : ComplexVector n) (ρ : ℝ) : Set (ComplexVector n) :=
  Metric.closedBall z₀ (2*ρ) \ Metric.ball z₀ (ρ/2)

theorem poleAnnulus_isCompact (z₀ : ComplexVector n) (ρ : ℝ) :
    IsCompact (poleAnnulus z₀ ρ) :=
  (isCompact_closedBall z₀ (2*ρ)).diff Metric.isOpen_ball

theorem poleAnnulus_ne_center (z₀ : ComplexVector n) {ρ : ℝ} (hρ : 0 < ρ)
    {z : ComplexVector n} (hz : z ∈ poleAnnulus z₀ ρ) : z ≠ z₀ := by
  intro heq
  apply hz.2
  simpa only [heq] using Metric.mem_ball_self (half_pos hρ)

/-- The genuine regularized pole Hessians have one compact-annulus bound
for every epsilon down to zero. -/
theorem regularizedPoleModel_uniform_annulus_bound {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (z₀ : ComplexVector n) (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ z ∈ poleAnnulus z₀ ρ,
      ∀ v : ComplexVector n,
        |matrixQuadratic (leviC (regularizedPoleModel χ z₀ c ε) z) v| ≤ C*‖v‖^2 := by
  let K : Set (ℝ × ComplexVector n) := Icc (0 : ℝ) ρ ×ˢ poleAnnulus z₀ ρ
  have hK : IsCompact K := isCompact_Icc.prod (poleAnnulus_isCompact z₀ ρ)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : Set (ℝ × ComplexVector n) := {p | p.2 ≠ z₀}
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hF : ContDiffOn ℝ ∞
      (fun p : ℝ × ComplexVector n => regularizedPoleModel χ z₀ c p.1 p.2) U := by
    intro p hp
    exact (regularizedPoleModel_joint_off_center hχ z₀ c p hp).contDiffWithinAt
  have hKU : K ⊆ U := fun p hp => poleAnnulus_ne_center z₀ hρ hp.2
  let A : K → Matrix (Fin n) (Fin n) ℂ :=
    fun p => leviC (regularizedPoleModel χ z₀ c p.1.1) p.1.2
  have hA : Continuous A :=
    continuousOn_iff_continuous_restrict.mp ((joint_leviC_continuousOn hU hF).mono hKU)
  obtain ⟨C,hC,hbound⟩ := compact_matrix_uniform_quadratic_bound A hA
  exact ⟨C,hC,fun ε hε z hz v => hbound ⟨(ε,z),hε,hz⟩ v⟩

end Yau.Proofs.P04Aux
