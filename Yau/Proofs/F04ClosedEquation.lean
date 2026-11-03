import Yau.Proofs.F04ClosedChartOperator

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates

/-- Actual closed-slab smoothness carries the genuine positive-time
 forced equation to BOTH time faces by continuity. No endpoint PDE or
 initial compatibility is supplied as a separate premise. -/
theorem forced_equation_closed_of_positive
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {T : ℝ} (hT : 0 < T)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 T) a b)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (hf : ContinuousOn f (O ×ˢ Icc 0 T))
    (hEq : ∀ p ∈ O ×ˢ Ioo 0 T, linearOp (O ×ˢ Icc 0 T) a b u p = f p) :
    ∀ p ∈ O ×ˢ Icc 0 T, linearOp (O ×ˢ Icc 0 T) a b u p = f p := by
  have hLC := linearOp_continuousOn_closed_slab hO hT hSmooth hu
  intro p hp
  have hL : ContinuousOn (fun t => linearOp (O ×ˢ Icc 0 T) a b u (p.1,t)) (Icc 0 T) :=
    hLC.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hp.1,ht⟩)
  have hF : ContinuousOn (fun t => f (p.1,t)) (Icc 0 T) :=
    hf.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hp.1,ht⟩)
  have he : EqOn (fun t => linearOp (O ×ˢ Icc 0 T) a b u (p.1,t)) (fun t => f (p.1,t)) (Ioo 0 T) :=
    fun t ht => hEq (p.1,t) ⟨hp.1,ht⟩
  have hall := he.of_subset_closure hL hF Ioo_subset_Icc_self
    (show Icc (0 : ℝ) T ⊆ closure (Ioo 0 T) by rw [closure_Ioo hT.ne])
  exact hall hp.2

end Yau.F04Proof
