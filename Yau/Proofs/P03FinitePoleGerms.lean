import Yau.Proofs.P03FinitePoleWeights
import Yau.Proofs.P03WeakTests

open scoped Manifold Topology ContDiff
open Set Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Disjointness from the other prescribed points gives the exact single
logarithmic pole germ, uniformly for every regularization value. -/
theorem finitePole_single_germ (pts : Finset M.Carrier)
    (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1)
    (hs : ∀ p : pts, tsupport (b p : M.Carrier → ℝ) ⊆
      {x | x ∈ pts ∧ x ≠ p.1}ᶜ) (p : pts) (c : ℝ) :
    ∀ᶠ z in 𝓝 (chartPt p.1 p.1), ∀ ε : ℝ,
      (∑ q : pts, manifoldCutoffPole c (b q) ε (chartInv p.1 z)) =
        c * modelLogPole (chartPt p.1 p.1) ε z := by
  classical
  have hb (q : pts) : ∀ᶠ x in 𝓝 p.1, b q x = if q = p then 1 else 0 := by
    by_cases hq : q = p
    · subst q
      filter_upwards [(b p).eventuallyEq_one] with x hx
      simpa only [ite_true, Pi.one_apply] using hx
    · have hne : p.1 ≠ q.1 := fun h => hq (Subtype.ext h.symm)
      have hn : p.1 ∉ tsupport (b q : M.Carrier → ℝ) :=
        fun h => hs q h ⟨p.2, hne⟩
      filter_upwards [(isClosed_tsupport (b q : M.Carrier → ℝ)).isOpen_compl.mem_nhds hn]
        with x hx
      simpa only [if_neg hq] using image_eq_zero_of_notMem_tsupport hx
  have hcp : Tendsto (chartInv p.1) (𝓝 (chartPt p.1 p.1)) (𝓝 p.1) := by
    change Tendsto (extChartAt (ComplexModel n) p.1).symm
      (𝓝 ((extChartAt (ComplexModel n) p.1) p.1)) (𝓝 p.1)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) p.1).tendsto
  have ht : chartTarget p.1 ∈ 𝓝 (chartPt p.1 p.1) :=
    (isOpen_extChartAt_target p.1).mem_nhds (mem_extChartAt_target p.1)
  filter_upwards [hcp.eventually (Filter.eventually_all.mpr hb), ht] with z hz hzt
  intro ε
  have he (q : pts) : manifoldCutoffPole c (b q) ε (chartInv p.1 z) =
      if q = p then c * modelLogPole (chartPt p.1 p.1) ε z else 0 := by
    by_cases hq : q = p
    · subst q
      simp only [manifoldCutoffPole, hz p, ite_true, one_mul]
      rw [show chartPt p.1 (chartInv p.1 z) = z from
        (extChartAt (ComplexModel n) p.1).right_inv hzt]
    · simp only [manifoldCutoffPole, hz q, if_neg hq, zero_mul, mul_zero]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Yau.NodeProofs.P03Aux
