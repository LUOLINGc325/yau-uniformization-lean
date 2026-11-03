import Yau.Proofs.F04HalfTimeBoundary

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeGlue {G : Type*} (f g : E × ℝ → G) (p : E × ℝ) : G :=
  if p.2 < 0 then g p else f p

theorem timeGlue_nonneg {G : Type*} (f g : E × ℝ → G) (p : E × ℝ) (hp : 0 ≤ p.2) :
    timeGlue f g p = f p := ite_eq_right (not_lt.mpr hp)

theorem timeGlue_nonpos {G : Type*} {W : Set E} (f g : E × ℝ → G)
    (heq : ∀ x ∈ W, f (x, 0) = g (x, 0)) (p : E × ℝ) (hp : p ∈ W ×ˢ Iic 0) :
    timeGlue f g p = g p := by
  by_cases ht : p.2 < 0
  · exact ite_eq_left ht
  · have hz : p.2 = 0 := le_antisymm hp.2 (not_lt.mp ht)
    rw [timeGlue_nonneg f g p (not_lt.mp ht)]
    simpa only [← hz] using heq p.1 hp.1

theorem timeGlue_hasFDerivAt {W : Set E} {S : ℝ} (hW : IsOpen W)
    (f g : E × ℝ → F) (A B : E × ℝ → (E × ℝ →L[ℝ] F))
    (hfg : ∀ x ∈ W, f (x, 0) = g (x, 0))
    (hAB : ∀ x ∈ W, A (x, 0) = B (x, 0))
    (hf : ∀ p ∈ W ×ˢ Icc 0 S, HasFDerivWithinAt f (A p) (W ×ˢ Icc 0 S) p)
    (hg : ∀ p ∈ W ×ˢ Iic 0, HasFDerivWithinAt g (B p) (W ×ˢ Iic 0) p)
    (p : E × ℝ) (hp : p ∈ W ×ˢ Iio S) :
    HasFDerivAt (timeGlue f g) (timeGlue A B p) p := by
  have hplus : HasFDerivWithinAt (timeGlue f g) (timeGlue A B p) (W ×ˢ Icc 0 S) p := by
    by_cases ht : 0 ≤ p.2
    · rw [timeGlue_nonneg A B p ht]
      exact (hf p ⟨hp.1, ht, hp.2.le⟩).congr
        (fun q hq => timeGlue_nonneg f g q hq.2.1) (timeGlue_nonneg f g p ht)
    · apply HasFDerivWithinAt.of_notMem_closure
      intro hcl
      have hcl' := (closure_minimal (fun q (hq : q ∈ W ×ˢ Icc 0 S) => hq.2.1)
        (isClosed_le continuous_const continuous_snd)) hcl
      exact ht hcl'
  have hminus : HasFDerivWithinAt (timeGlue f g) (timeGlue A B p) (W ×ˢ Iic 0) p := by
    by_cases ht : p.2 ≤ 0
    · rw [timeGlue_nonpos A B hAB p ⟨hp.1, ht⟩]
      exact (hg p ⟨hp.1, ht⟩).congr
        (fun q hq => timeGlue_nonpos f g hfg q hq) (timeGlue_nonpos f g hfg p ⟨hp.1, ht⟩)
    · apply HasFDerivWithinAt.of_notMem_closure
      intro hcl
      have hcl' := (closure_minimal (fun q (hq : q ∈ W ×ˢ Iic 0) => hq.2)
        (isClosed_le continuous_snd continuous_const)) hcl
      exact ht hcl'
  apply (hplus.union hminus).hasFDerivAt
  apply mem_of_superset ((hW.prod isOpen_Iio).mem_nhds hp)
  intro q hq
  rcases le_total 0 q.2 with ht | ht
  · exact Or.inl ⟨hq.1, ht, hq.2.le⟩
  · exact Or.inr ⟨hq.1, ht⟩

end Yau.F04Proof.Seeley
