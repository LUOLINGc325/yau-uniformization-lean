import Yau.Proofs.C01CompactRicciCoercivity
import Yau.Proofs.C01RicciFrameCoercivity

/-! The true moving-frame solution propagates the time-one quantitative
Ricci bound to all later times in the original centered matrices. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_bound_from_one
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (c : ℝ)
    (hinitial : ∀ v : ComplexVector n,
      c * matrixQuadraticReal (gMat (h 1) x) v ≤ matrixQuadraticReal (ricci (h 1) x) v)
    (t : ℝ) (ht : 1 ≤ t) :
    ∀ v : Fin n → ℂ,
      c * (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re ≤
        t * (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re := by
  by_cases ht1 : t = 1
  · subst t
    intro v
    simpa only [matrixQuadraticReal, WithLp.ofLp_toLp, one_mul] using hinitial (WithLp.toLp 2 v)
  have h1t : 1 < t := lt_of_le_of_ne ht (Ne.symm ht1)
  have hsegment : Set.Icc (1 : ℝ) t ⊆ Set.Ioi 0 := by
    intro s hs
    exact zero_lt_one.trans_le hs.1
  obtain ⟨δ, hδ, W, hW₁, _hW, hsol⟩ :=
    Yau.LeafProofs.L23Aux.exists_interval_fundamental_solution
      (movingFrameCoefficient h x) (Set.Ioi 0) isOpen_Ioi
      (localizedFlow_movingFrameCoefficient_contDiffOn hflow x) 1 t h1t hsegment
  have hWactual (s : ℝ) (hs : s ∈ Set.Icc (1 : ℝ) t) :
      HasDerivAt W ((movingFrameCoefficient h x s).comp (W s)) s := by
    apply (hsol s ?_).2
    constructor <;> linarith [hs.1, hs.2]
  have hstart (v : Fin n → ℂ) :
      c * (star v ⬝ᵥ (gMat (h 1) x *ᵥ v)).re ≤
        1 * (star v ⬝ᵥ (ricci (h 1) x *ᵥ v)).re := by
    simpa only [matrixQuadraticReal, WithLp.ofLp_toLp, one_mul] using hinitial (WithLp.toLp 2 v)
  exact localizedFlow_ricci_quadratic_bound_of_movingFrame hflow hjoint x W 1 t c
    zero_lt_one ht hW₁ hWactual hstart

end Yau.NodeProofs.C01Aux
