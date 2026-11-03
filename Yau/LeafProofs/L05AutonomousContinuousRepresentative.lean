import Yau.LeafProofs.L05AutonomousContinuousRepresentativeDensity
import Yau.LeafProofs.L05AutonomousContinuousRepresentativeExtension

noncomputable section
open Set Filter MeasureTheory
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_full_measure_cylinder_holder_representative
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (c : Space n) {R T : ℝ} (hR : 0<R) {S : Set (Point n)}
    (hS : S⊆autoOpen c R T)
    (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S)
    {eta C B : ℝ} (heta : 0<eta) (hC : 0≤C) (hB : 0≤B)
    (H : Point n → E) (hBound : ∀ p∈S, ‖H p‖≤B)
    (hHolder : ∀ p∈S, ∀ q∈S, ‖H p-H q‖≤C*holderWeight eta p q) :
    ∃ Hbar : Point n → E, ContinuousOn Hbar (autoClosed c R T) ∧ EqOn Hbar H S ∧
      (∀ p∈autoClosed c R T, ‖Hbar p‖≤B) ∧
      (∀ p∈autoClosed c R T, ∀ q∈autoClosed c R T,
        ‖Hbar p-Hbar q‖≤C*holderWeight eta p q) := by
  have heq := auto_full_measure_cylinder_closure c hR hS hFull
  apply auto_dense_holder_representative
    (hS.trans (by intro p hp; exact ⟨Metric.ball_subset_closedBall hp.1,⟨hp.2.1.le,hp.2.2.le⟩⟩))
    heq.ge heta hC hB H hBound hHolder

end Yau.LeafProofs.L05AutonomousAux
