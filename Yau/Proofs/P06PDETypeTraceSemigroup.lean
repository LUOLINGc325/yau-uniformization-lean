import Yau.Proofs.P06PDETypeTraceTimeJets
import Yau.Proofs.P06FormUniqueness

noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint
variable {n k : ℕ} {M : ComplexManifold n}

 theorem boundedFormHeat_time_shift (g : HermitianField M)
    {A : RealForm M k} {U : ℝ → RealForm M k} (hU : IsBoundedFormHeat g A U)
    (s : ℝ) (hs : 0 ≤ s) : IsBoundedFormHeat g (U s) (fun t => U (s + t)) := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa only [zero_add, hU.2.1.1] using hU
  refine ⟨?_, formSmoothInitial_time_shift hU.1 hs, ?_, ?_⟩
  · intro x I
    exact (hU.1 x I).comp
      (contDiffOn_fst.prodMk (contDiffOn_const.add contDiffOn_snd))
      (fun p hp => ⟨hp.1, add_pos hs hp.2⟩)
  · intro T hT
    obtain ⟨B, hB, hb⟩ := hU.2.2.1 (s + T) (add_pos hs hT)
    exact ⟨B, hB, fun x t ht htT => hb x (s + t) (add_pos hs ht) (by linarith)⟩
  · intro x z hz t ht I
    have hd := (hU.2.2.2 x z hz (s + t) (add_pos hs ht) I).comp t
      ((hasDerivAt_id t).const_add s)
    simpa only [Function.comp_def, mul_one] using hd

 theorem hodgeSemigroupLaw (X : KahlerManifold n) : HodgeSemigroupLaw X.metric.form := by
  intro A U hA hU s hs V hV t ht
  exact boundedFormHeat_unique X (U s) V (fun t => U (s + t)) hV
    (boundedFormHeat_time_shift X.metric.form hU s hs) t ht

end Yau.NodeProofs.P06Aux.PDETypeTrace
