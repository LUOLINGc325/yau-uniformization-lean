import Yau.Proofs.F01PotentialFiniteClockJet
import Yau.Proofs.F01FiniteJetParabolicBootstrap
import Yau.Proofs.F01SlabSpatialTensorRegularity

/-! The original logdet potential equation bootstraps from its actual
continuous spatial tensor tower and actual tensor clock equations.
No mixed derivatives occur among the hypotheses. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem joint_smooth_of_potential_tensor_clock_equations
    (f b : Point n → ℝ) (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    {O : Set (Space n)} {I : Set ℝ} (hO : IsOpen O) (hI : IsOpen I)
    (hS : ContDiffOn ℝ ∞ S (O ×ˢ I)) (hb : ContDiffOn ℝ ∞ b (O ×ˢ I))
    (hSlices : ∀ t ∈ I, ContDiffOn ℝ ∞ (fun z => f (z, t)) O)
    (hContinuous : ∀ k, ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (O ×ˢ I))
    (hPos : ∀ p ∈ O ×ˢ I, 0 < (S p + leviC (fun z => f (z, p.2)) p.1).det.re)
    (hClock : ∀ k p, p ∈ O ×ˢ I → HasDerivAt
      (fun t => iteratedFDeriv ℝ k (fun z => f (z, t)) p.1)
      (iteratedFDeriv ℝ k (fun z =>
        Real.log (S (z, p.2) + leviC (fun y => f (y, p.2)) z).det.re + b (z, p.2)) p.1) p.2) :
    ContDiffOn ℝ ∞ f (O ×ˢ I) ∧ ∀ k, ContDiffOn ℝ ∞
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (O ×ˢ I) := by
  have hSslice (t : ℝ) (ht : t ∈ I) : ContDiffOn ℝ ∞ (fun z => S (z, t)) O :=
    hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hbslice (t : ℝ) (ht : t ∈ I) : ContDiffOn ℝ ∞ (fun z => b (z, t)) O :=
    hb.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  apply joint_smooth_of_actual_finite_jet_clock_equations f (hO.prod hI)
    (fun k => potentialFiniteClockDomain k S (O ×ˢ I))
    (fun k => potentialFiniteClockJet k S b)
  · intro k
    exact potentialFiniteClockJet_contDiffOn k S b (O ×ˢ I)
      (fun j => slab_spatial_tensor_smooth hO hI.uniqueDiffOn hS j.val)
      (slab_spatial_tensor_smooth hO hI.uniqueDiffOn hb k)
  · intro k p hp
    refine ⟨hp, ?_⟩
    rw [potentialFiniteMatrixJet_native k S (fun z => f (z, p.2)) p hO hp.1
      (hSslice p.2 hp.2) (hSlices p.2 hp.2)]
    exact hPos p hp
  · intro p hp
    exact (hSlices p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)
  · exact hContinuous
  · intro k p hp
    rw [potentialFiniteClockJet_native k S b (fun z => f (z, p.2)) p hO hp.1
      (hSslice p.2 hp.2) (hSlices p.2 hp.2) (hbslice p.2 hp.2) (hPos p hp)]
    exact hClock k p hp

end Yau.NodeProofs.F01Aux
