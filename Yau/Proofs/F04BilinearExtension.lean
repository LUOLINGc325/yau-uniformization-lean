import Yau.Proofs.F04FiniteMass

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

/-- Extend the actual bounded form from a dense algebraic core in both
variables. The core needs no independently chosen norm or completion. -/
theorem bounded_bilinear_extension {E V : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : E →ₗ[ℝ] V) (he : DenseRange e) (b : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u v, |b u v| ≤ C * ‖e u‖ * ‖e v‖) :
    ∃ B : V →L[ℝ] V →L[ℝ] ℝ, ‖B‖ ≤ C ∧ ∀ u v, B (e u) (e v) = b u v := by
  let R : E → V →L[ℝ] ℝ := fun u => (b u).extendOfNorm e
  have hRb (u : E) : ‖R u‖ ≤ C * ‖e u‖ := by
    apply LinearMap.opNorm_extendOfNorm_le he (mul_nonneg hC (norm_nonneg _))
    intro v
    simpa only [Real.norm_eq_abs] using hb u v
  have hRc (u v : E) : R u (e v) = b u v := by
    apply LinearMap.extendOfNorm_eq he
    refine ⟨C * ‖e u‖, ?_⟩
    intro w
    simpa only [Real.norm_eq_abs] using hb u w
  let L : E →ₗ[ℝ] V →L[ℝ] ℝ :=
    { toFun := R
      map_add' := by
        intro u v
        apply ContinuousLinearMap.ext
        intro x
        refine he.induction (fun w hw => ?_) (isClosed_eq (R (u + v)).continuous
          ((R u).continuous.add (R v).continuous)) x
        rcases hw with ⟨w, rfl⟩
        change R (u + v) (e w) = R u (e w) + R v (e w)
        rw [hRc, hRc, hRc]
        simp only [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c u
        apply ContinuousLinearMap.ext
        intro x
        refine he.induction (fun w hw => ?_) (isClosed_eq (R (c • u)).continuous
          (continuous_const.mul (R u).continuous)) x
        rcases hw with ⟨w, rfl⟩
        change R (c • u) (e w) = c * R u (e w)
        rw [hRc, hRc]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] }
  have hLb (u : E) : ‖L u‖ ≤ C * ‖e u‖ := hRb u
  refine ⟨L.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le he hC hLb, ?_⟩
  intro u v
  rw [LinearMap.extendOfNorm_eq he ⟨C, hLb⟩ u]
  exact hRc u v

end Yau.F04Proof
