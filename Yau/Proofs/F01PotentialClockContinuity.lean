import Yau.Proofs.F01PotentialTensorBootstrap

/-! Continuity of the actual spatial potential jets implies continuity
of the computed clock jets up to a terminal face. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem potential_spatial_clock_jet_continuousOn
    (f b : Point n → ℝ) (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    {O : Set (Space n)} {I : Set ℝ} (hO : IsOpen O) (hI : IsOpen I)
    (hS : ContDiffOn ℝ ∞ S (O ×ˢ I)) (hb : ContDiffOn ℝ ∞ b (O ×ˢ I))
    {A : Set (Point n)} (hA : A ⊆ O ×ˢ I)
    (hSlices : ∀ p ∈ A, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) O)
    (hContinuous : ∀ k, ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) A)
    (hPos : ∀ p ∈ A, 0 < (S p + leviC (fun z => f (z, p.2)) p.1).det.re)
    (k : ℕ) : ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z =>
        Real.log (S (z, p.2) + leviC (fun y => f (y, p.2)) z).det.re + b (z, p.2)) p.1) A := by
  have hSslice (t : ℝ) (ht : t ∈ I) : ContDiffOn ℝ ∞ (fun z => S (z, t)) O :=
    hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hbslice (t : ℝ) (ht : t ∈ I) : ContDiffOn ℝ ∞ (fun z => b (z, t)) O :=
    hb.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hPhi := (potentialFiniteClockJet_contDiffOn k S b (O ×ˢ I)
    (fun j => slab_spatial_tensor_smooth hO hI.uniqueDiffOn hS j.val)
    (slab_spatial_tensor_smooth hO hI.uniqueDiffOn hb k)).continuousOn
  have hInput : ContinuousOn
      (fun p : Point n => (p, fun j : Fin (k + 2 + 1) =>
        iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1)) A :=
    continuousOn_id.prodMk (continuousOn_pi.mpr (fun j => hContinuous j.val))
  have hMap : MapsTo
      (fun p : Point n => (p, fun j : Fin (k + 2 + 1) =>
        iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1)) A
      (potentialFiniteClockDomain k S (O ×ˢ I)) := by
    intro p hp
    refine ⟨hA hp, ?_⟩
    rw [potentialFiniteMatrixJet_native k S (fun z => f (z, p.2)) p hO (hA hp).1
      (hSslice p.2 (hA hp).2) (hSlices p hp)]
    exact hPos p hp
  apply (hPhi.comp hInput hMap).congr
  intro p hp
  exact (potentialFiniteClockJet_native k S b (fun z => f (z, p.2)) p hO (hA hp).1
    (hSslice p.2 (hA hp).2) (hSlices p hp) (hbslice p.2 (hA hp).2) (hPos p hp)).symm

end Yau.NodeProofs.F01Aux
