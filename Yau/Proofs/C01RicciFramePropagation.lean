import Yau.Proofs.C01MovingFrameNorm
import Yau.Proofs.C01RicciTimeBoundary

/-! The proved matrix Harnack inequality propagates strict positivity
along a genuine fundamental solution of the original moving-frame ODE. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_posDef_of_movingFrame
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) (x : Pt X)
    (W : ℝ → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hinit : W a = ContinuousLinearMap.id ℝ (Fin n → ℂ))
    (hW : ∀ t ∈ Set.Icc a b, HasDerivAt W ((movingFrameCoefficient h x t).comp (W t)) t)
    (hpositive : (ricci (h a) x).PosDef) : (ricci (h b) x).PosDef := by
  have hb : 0 < b := ha.trans_le hab
  have hherm := localizedFlow_ricci_isHermitian hflow x hb
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
  intro v hv
  obtain ⟨u, hu⟩ := localizedFlow_movingFrame_endpoint_surjective hflow x W a b ha hab hinit hW v
  have hunz : u ≠ 0 := by
    intro hz
    apply hv
    rw [hz, map_zero] at hu
    exact hu.symm
  have hmono := localizedFlow_moving_ricci_weight_monotoneOn hflow hjoint x
    (fun s => W s u) a b ha
    (fun t ht => movingFrame_solution_vector_hasDerivAt x W u t (hW t ht))
  have hcomp := hmono (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩) hab
  have hcomp' : a * (star u ⬝ᵥ (ricci (h a) x *ᵥ u)).re ≤
      b * (star v ⬝ᵥ (ricci (h b) x *ᵥ v)).re := by
    simpa only [hinit, ContinuousLinearMap.id_apply, hu] using hcomp
  have hstart : 0 < a * (star u ⬝ᵥ (ricci (h a) x *ᵥ u)).re :=
    mul_pos ha (Complex.pos_iff.mp (hpositive.dotProduct_mulVec_pos hunz)).1
  apply Complex.pos_iff.mpr
  exact ⟨pos_of_mul_pos_right (hstart.trans_le hcomp') hb.le,
    (hherm.im_star_dotProduct_mulVec_self v).symm⟩

end Yau.NodeProofs.C01Aux
