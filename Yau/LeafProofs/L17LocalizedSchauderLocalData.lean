import Yau.LeafProofs.L17LocalizedSchauderCompositionBounds
import Yau.LeafProofs.L17SchauderSpaceNorm

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def localScaledDistance (ρ : ℝ) {T : ℝ} (q r : ComplexVector n × Time T) : ℝ :=
  (‖q.1-r.1‖+Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|)/ρ

def unitParabolicDistance (ρ : ℝ) {T : ℝ} (q r : ComplexVector n × Time T) : ℝ :=
  ‖q.1-r.1‖+Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|/ρ

/-- Only local continuity, actual spatial and closed-time derivatives,
and the true initial value are included in the local input data. -/
def LocalTrueJets (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ) : Prop :=
  (∀ p, ContinuousOn (v p) (ball 0 (2*P.radius) ×ˢ Set.univ) ∧
    ContinuousOn (D p) (ball 0 (2*P.radius) ×ˢ Set.univ) ∧
    ContinuousOn (H p) (ball 0 (2*P.radius) ×ˢ Set.univ) ∧
    ContinuousOn (b p) (ball 0 (2*P.radius) ×ˢ Set.univ)) ∧
  (∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → ∀ t : Time T,
    HasFDerivAt (fun w => v p (w,t)) (D p (z,t)) z ∧
    HasFDerivAt (fun w => D p (w,t)) (H p (z,t)) z) ∧
  (∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → ∀ t : Time T,
    HasDerivWithinAt (fun τ => v p (z,projIcc (0 : ℝ) T hT τ)) (b p (z,t)) (Icc (0 : ℝ) T) (t : ℝ)) ∧
  ∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → v p (z,⟨0,⟨le_rfl,hT⟩⟩) = 0

/-- The four literal local Gaussian jet inequalities and their scaled
two-point inequalities; this contains no global estimate or membership. -/
def LocalScaledJetBounds (P : UniformChartPartition g) (T gamma F : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ) : Prop :=
  (∀ p q, q.1 ∈ ball (0 : ComplexVector n) (2*P.radius) →
    |v p q| ≤ P.radius^2*F ∧ ‖D p q‖ ≤ P.radius*F ∧ ‖H p q‖ ≤ F ∧ |b p q| ≤ F) ∧
  ∀ p q r, q.1 ∈ ball (0 : ComplexVector n) (2*P.radius) → r.1 ∈ ball 0 (2*P.radius) →
    |v p q-v p r| ≤ P.radius^2*F*(localScaledDistance P.radius q r)^gamma ∧
    ‖D p q-D p r‖ ≤ P.radius*F*(localScaledDistance P.radius q r)^gamma ∧
    ‖H p q-H p r‖ ≤ F*(localScaledDistance P.radius q r)^gamma ∧
    |b p q-b p r| ≤ F*(localScaledDistance P.radius q r)^gamma

theorem localTrueJets_spatial_contDiffOn_two (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (h : LocalTrueJets P T hT v D H b) (p : P.centers) (t : Time T) :
    ContDiffOn ℝ 2 (fun z => v p (z,t)) (ball (0 : ComplexVector n) (2*P.radius)) := by
  apply contDiffOn_two_of_true_jets isOpen_ball _ (fun z => D p (z,t)) (fun z => H p (z,t))
    (fun z hz => (h.2.1 p z hz t).1) (fun z hz => (h.2.1 p z hz t).2)
  exact ((h.1 p).2.2.1).comp (continuous_id.prodMk continuous_const).continuousOn
    (fun z hz => ⟨hz,mem_univ _⟩)

theorem radius_smul_mem_ball_two (P : UniformChartPartition g) {z : ComplexVector n}
    (hz : z ∈ ball 0 2) : P.radius • z ∈ ball (0 : ComplexVector n) (2*P.radius) := by
  apply mem_ball.mpr
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
  have hn : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
  exact (mul_lt_mul_of_pos_left hn P.radius_pos).trans_eq (mul_comm _ _)

theorem localScaledDistance_radius_eq {ρ : ℝ} (hρ : 0 < ρ) {T : ℝ}
    (z w : ComplexVector n) (t s : Time T) :
    localScaledDistance ρ (ρ • z,t) (ρ • w,s) = unitParabolicDistance ρ (z,t) (w,s) := by
  dsimp only [localScaledDistance,unitParabolicDistance]
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
  field_simp [hρ.ne']

end Yau.LeafProofs.L17LocalizedSchauderAux
