import Yau.Proofs.V03Elementary
import Mathlib.Topology.ContinuousMap.Compact

/-! A continuous family of genuine linear derivatives on a compact trace
domain assembles into a native bounded derivative with the same norm bound. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {𝕜 K P F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def continuousMapOperator (A : C(K, P →L[𝕜] F)) : P →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => A k v,
        (ContinuousLinearMap.apply 𝕜 F v).continuous.comp A.continuous⟩
      map_add' := by intros; ext k; exact map_add (A k) _ _
      map_smul' := by intros; ext k; exact map_smul (A k) _ _ }
    ‖A‖ (by
      intro v
      change ‖(⟨fun k => A k v,
        (ContinuousLinearMap.apply 𝕜 F v).continuous.comp A.continuous⟩ : C(K, F))‖ ≤ ‖A‖ * ‖v‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
      intro k
      exact ((A k).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm k) (norm_nonneg v)))

theorem continuousMapOperator_apply (A : C(K, P →L[𝕜] F)) (v : P) (k : K) :
    continuousMapOperator A v k = A k v := rfl

theorem continuousMapOperator_norm_le (A : C(K, P →L[𝕜] F)) :
    ‖continuousMapOperator A‖ ≤ ‖A‖ := by
  apply LinearMap.mkContinuous_norm_le
  exact norm_nonneg A

def continuousMapOperatorL : C(K, P →L[𝕜] F) →L[𝕜] P →L[𝕜] C(K, F) := by
  let B : C(K, P →L[𝕜] F) →ₗ[𝕜] P →L[𝕜] C(K, F) :=
    {
      toFun := fun (A : C(K, P →L[𝕜] F)) =>
        continuousMapOperator (𝕜 := 𝕜) (K := K) (P := P) (F := F) A
      map_add' := by intros; ext v k; rfl
      map_smul' := by intros; ext v k; rfl
    }
  refine LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := C(K, P →L[𝕜] F)) (F := P →L[𝕜] C(K, F)) (σ := RingHom.id 𝕜) B 1 ?_
  intro A
  change ‖continuousMapOperator (𝕜 := 𝕜) (K := K) (P := P) (F := F) A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using
    continuousMapOperator_norm_le (𝕜 := 𝕜) (K := K) (P := P) (F := F) A

theorem continuousMapOperatorL_apply (A : C(K, P →L[𝕜] F)) :
    continuousMapOperatorL A = continuousMapOperator A := rfl

end Yau.Blueprint.V03Proof
