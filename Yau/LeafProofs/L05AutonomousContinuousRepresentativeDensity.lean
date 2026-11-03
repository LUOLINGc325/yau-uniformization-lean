import Yau.LeafProofs.L05AutonomousDifferences
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem continuousRepresentative_autoOpen_closure {n : ℕ} (c : Space n)
    {R T : ℝ} (hR : 0<R) : closure (autoOpen c R T)=autoClosed c R T := by
  rw [autoOpen,closure_prod_eq,closure_ball c hR.ne',closure_Ioo (by nlinarith [sq_pos_of_pos hR])]
  rfl

theorem auto_full_measure_cylinder_closure {n : ℕ} (c : Space n)
    {R T : ℝ} (hR : 0<R) {S : Set (Point n)}
    (hS : S⊆autoOpen c R T)
    (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S) :
    closure S=autoClosed c R T := by
  have hAE : ∀ᵐ p ∂(volume : Measure (Point n)), p∈autoOpen c R T → p∈S :=
    (ae_restrict_iff' (autoOpen_isOpen c R T).measurableSet).mp hFull
  have hd : Dense {p : Point n | p∈autoOpen c R T → p∈S} :=
    MeasureTheory.Measure.dense_of_ae (μ := volume) hAE
  have hInside : autoOpen c R T⊆closure S :=
    (hd.open_subset_closure_inter (autoOpen_isOpen c R T)).trans
      (closure_mono (by intro p hp; exact hp.2 hp.1))
  have heq : closure S=closure (autoOpen c R T) :=
    (closure_mono hS).antisymm (closure_minimal hInside isClosed_closure)
  rw [heq,continuousRepresentative_autoOpen_closure c hR]

end Yau.LeafProofs.L05AutonomousAux
