import Yau.LeafProofs.L05PerturbationGeometry
import Yau.LeafProofs.L05PucciHarnackDomains

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perturbCoreABPRadius (tau : ℝ) : ℝ := 1/2-tau

def perturbCoreABPTime (tau : ℝ) : ℝ := (1/2:ℝ)^2-tau^2

theorem perturb_core_abp_geometry {tau : ℝ} (ht : 0 < tau) (hb : tau ≤ 1/8) :
    0 < perturbCoreABPRadius tau ∧ 0 < perturbCoreABPTime tau ∧ perturbCoreABPTime tau ≤ 1 ∧
      1 ≤ perturbCoreABPTime tau/(perturbCoreABPRadius tau)^2 ∧
      perturbCoreABPTime tau/(perturbCoreABPRadius tau)^2 ≤ 2 := by
  have hs := perturb_core_aspect ht hb
  refine ⟨hs.1,hs.2.1,?_,hs.2.2.1,hs.2.2.2⟩
  dsimp only [perturbCoreABPTime]
  nlinarith only [sq_nonneg tau]

theorem perturb_core_abp_closed_eq {n : ℕ} (tau : ℝ) :
    perturbCore (n := n) tau=harnackClosed (0 : Space n) (perturbCoreABPRadius tau)
      (-perturbCoreABPTime tau) (perturbCoreABPTime tau) := by
  have hInit : -perturbCoreABPTime tau=-(1/2:ℝ)^2+tau^2 := by unfold perturbCoreABPTime; ring
  simp only [perturbCore,harnackClosed,neg_add_cancel]
  rw [hInit]
  rfl

theorem perturb_core_abp_open_eq {n : ℕ} (tau : ℝ) :
    perturbCoreOpen (n := n) tau=harnackOpen (0 : Space n) (perturbCoreABPRadius tau)
      (-perturbCoreABPTime tau) (perturbCoreABPTime tau) := by
  have hInit : -perturbCoreABPTime tau=-(1/2:ℝ)^2+tau^2 := by unfold perturbCoreABPTime; ring
  simp only [perturbCoreOpen,harnackOpen,neg_add_cancel]
  rw [hInit]
  rfl

theorem perturb_core_abp_boundary_eq {n : ℕ} (tau : ℝ) :
    perturbCoreBoundary (n := n) tau=harnackBoundary (0 : Space n) (perturbCoreABPRadius tau)
      (-perturbCoreABPTime tau) (perturbCoreABPTime tau) := by
  have hInit : -perturbCoreABPTime tau=-(1/2:ℝ)^2+tau^2 := by unfold perturbCoreABPTime; ring
  simp only [perturbCoreBoundary,harnackBoundary,neg_add_cancel]
  rw [hInit]
  rfl

end Yau.LeafProofs.L05Aux
