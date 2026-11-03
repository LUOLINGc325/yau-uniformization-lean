import Yau.LeafProofs.L17LocalizedSchauderLocalData

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
  (v : P.centers → ComplexVector n × Time T → ℝ)
  (D : P.centers → ComplexVector n × Time T → D1 n)
  (H : P.centers → ComplexVector n × Time T → D2 n)
  (b : P.centers → ComplexVector n × Time T → ℝ)
  (h : LocalTrueJets P T hT v D H b)

include h

theorem localUnitValue_hasFDerivAt (p : P.centers) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 2) :
    HasFDerivAt (unitValue P.radius (fun w => v p (w,t)))
      (unitFirstJet P.radius (fun w => D p (w,t)) z) z :=
  unitValue_hasFDerivAt P.radius_pos (fun w => v p (w,t)) (fun w => D p (w,t)) z
    (h.2.1 p (P.radius • z) (radius_smul_mem_ball_two P hz) t).1

theorem localUnitFirstJet_hasFDerivAt (p : P.centers) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 2) :
    HasFDerivAt (unitFirstJet P.radius (fun w => D p (w,t))) (H p (P.radius • z,t)) z :=
  unitFirstJet_hasFDerivAt P.radius_pos (fun w => D p (w,t)) (fun w => H p (w,t)) z
    (h.2.1 p (P.radius • z) (radius_smul_mem_ball_two P hz) t).2

theorem localUnitValue_contDiffOn_two (p : P.centers) (t : Time T) :
    ContDiffOn ℝ 2 (unitValue P.radius (fun w => v p (w,t))) (ball (0 : ComplexVector n) 2) := by
  have hScale : ContDiff ℝ 2 (fun z : ComplexVector n => P.radius • z) :=
    (P.radius • ContinuousLinearMap.id ℝ (ComplexVector n)).contDiff
  exact ((localTrueJets_spatial_contDiffOn_two P T hT v D H b h p t).comp hScale.contDiffOn
    (fun z hz => radius_smul_mem_ball_two P hz)).const_smul ((P.radius^2)⁻¹)

theorem localUnitValue_two_jet_norm_le {gamma F : ℝ}
    (hbounds : LocalScaledJetBounds P T gamma F v D H b)
    (p : P.centers) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 2) :
    ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (unitValue P.radius (fun w => v p (w,t))) z‖ ≤ F := by
  have hLocal := hbounds.1 p (P.radius • z,t) (radius_smul_mem_ball_two P hz)
  apply norm_iteratedFDeriv_le_two_of_true_jets isOpen_ball
    (unitValue P.radius (fun w => v p (w,t)))
    (unitFirstJet P.radius (fun w => D p (w,t))) (fun w => H p (P.radius • w,t))
    (fun w hw => localUnitValue_hasFDerivAt P T hT v D H b h p t hw)
    (fun w hw => localUnitFirstJet_hasFDerivAt P T hT v D H b h p t hw) hz
  · apply unitValue_norm_le P.radius_pos
    simpa only [Real.norm_eq_abs] using hLocal.1
  · exact unitFirstJet_norm_le P.radius_pos _ _ hLocal.2.1
  · exact hLocal.2.2.1

theorem localUnitValue_two_jet_sub_norm_le {gamma F : ℝ}
    (hbounds : LocalScaledJetBounds P T gamma F v D H b)
    (p : P.centers) (t s : Time T) {z w : ComplexVector n} (hz : z ∈ ball 0 2) (hw : w ∈ ball 0 2) :
    ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (unitValue P.radius (fun y => v p (y,t))) z-
        iteratedFDeriv ℝ j (unitValue P.radius (fun y => v p (y,s))) w‖ ≤
          F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  have hLocal := hbounds.2 p (P.radius • z,t) (P.radius • w,s)
    (radius_smul_mem_ball_two P hz) (radius_smul_mem_ball_two P hw)
  apply norm_iteratedFDeriv_sub_le_two_of_true_jets isOpen_ball
    (unitValue P.radius (fun y => v p (y,t))) (unitValue P.radius (fun y => v p (y,s)))
    (unitFirstJet P.radius (fun y => D p (y,t))) (unitFirstJet P.radius (fun y => D p (y,s)))
    (fun y => H p (P.radius • y,t)) (fun y => H p (P.radius • y,s))
    (fun y hy => localUnitValue_hasFDerivAt P T hT v D H b h p t hy)
    (fun y hy => localUnitFirstJet_hasFDerivAt P T hT v D H b h p t hy)
    (fun y hy => localUnitValue_hasFDerivAt P T hT v D H b h p s hy)
    (fun y hy => localUnitFirstJet_hasFDerivAt P T hT v D H b h p s hy) hz hw
  · apply unitValue_sub_norm_le P.radius_pos
    simpa only [Real.norm_eq_abs,mul_assoc,localScaledDistance_radius_eq P.radius_pos] using hLocal.1
  · apply unitFirstJet_sub_norm_le P.radius_pos
    simpa only [mul_assoc,localScaledDistance_radius_eq P.radius_pos] using hLocal.2.1
  · simpa only [localScaledDistance_radius_eq P.radius_pos] using hLocal.2.2.1

end Yau.LeafProofs.L17LocalizedSchauderAux
