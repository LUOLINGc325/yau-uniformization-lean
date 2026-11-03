import Yau.Proofs.F04BilinearExtension

open Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

/-- The Banach-valued version allows one common extension with values in
continuous time profiles, so time continuity survives the actual completion. -/
theorem bounded_bilinear_extension_banach {E V F : Type*}
    [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E →ₗ[ℝ] V) (he : DenseRange e) (b : E →ₗ[ℝ] E →ₗ[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u v, ‖b u v‖ ≤ C * ‖e u‖ * ‖e v‖) :
    ∃ B : V →L[ℝ] V →L[ℝ] F, ‖B‖ ≤ C ∧ ∀ u v, B (e u) (e v) = b u v := by
  let R : E → V →L[ℝ] F := fun u => (b u).extendOfNorm e
  have hRb (u : E) : ‖R u‖ ≤ C * ‖e u‖ :=
    LinearMap.opNorm_extendOfNorm_le he (mul_nonneg hC (norm_nonneg _)) (hb u)
  have hRc (u v : E) : R u (e v) = b u v :=
    LinearMap.extendOfNorm_eq he ⟨C * ‖e u‖, hb u⟩ v
  let L : E →ₗ[ℝ] V →L[ℝ] F :=
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
          ((R u).continuous.const_smul c)) x
        rcases hw with ⟨w, rfl⟩
        change R (c • u) (e w) = c • R u (e w)
        rw [hRc, hRc]
        simp only [map_smul, LinearMap.smul_apply] }
  have hLb (u : E) : ‖L u‖ ≤ C * ‖e u‖ := hRb u
  refine ⟨L.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le he hC hLb, ?_⟩
  intro u v
  rw [LinearMap.extendOfNorm_eq he ⟨C, hLb⟩ u]
  exact hRc u v

end Yau.F04Proof
