import Yau.Proofs.F04GalerkinPivot
import Yau.LeafProofs.L16FiniteVolterra
import Yau.LeafProofs.L16FiniteEnergyIdentity

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

/-- The finite reconstruction stays in the original energy space. -/
def variationalReconstruction (e : Fin m → V) : EuclideanSpace ℝ (Fin m) →L[ℝ] V :=
  ∑ i, (EuclideanSpace.proj i).smulRight (e i)

@[simp] theorem variationalReconstruction_apply (e : Fin m → V)
    (c : EuclideanSpace ℝ (Fin m)) :
    variationalReconstruction e c = ∑ i, c i • e i := by
  simp [variationalReconstruction]

def variationalForcing (j : V →L[ℝ] H) (e : Fin m → V) :
    H →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (j (e i))))

@[simp] theorem variationalForcing_apply (j : V →L[ℝ] H) (e : Fin m → V)
    (F : H) (i : Fin m) :
    variationalForcing j e F i = inner ℝ F (j (e i)) := by
  simp [variationalForcing, real_inner_comm]

def variationalMatrix (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (B.flip (e i)).comp (variationalReconstruction e)))

@[simp] theorem variationalMatrix_apply (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    variationalMatrix e B c i = ∑ k, B (e k) (e i) * c k := by
  simp [variationalMatrix, map_sum, mul_comm]

theorem variationalReconstruction_inner (j : V →L[ℝ] H) (e : Fin m → V)
    (he : Orthonormal ℝ (fun i => j (e i))) (c d : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (j (variationalReconstruction e c)) (j (variationalReconstruction e d)) =
      inner ℝ c d := by
  simp only [variationalReconstruction_apply, map_sum, map_smul]
  simpa [PiLp.inner_apply, mul_comm] using he.inner_sum (fun i => c i) (fun i => d i) Finset.univ

theorem variationalReconstruction_norm_sq (j : V →L[ℝ] H) (e : Fin m → V)
    (he : Orthonormal ℝ (fun i => j (e i))) (c : EuclideanSpace ℝ (Fin m)) :
    ‖j (variationalReconstruction e c)‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using variationalReconstruction_inner j e he c c

theorem variationalForcing_norm_le (j : V →L[ℝ] H) (e : Fin m → V)
    (he : Orthonormal ℝ (fun i => j (e i))) (F : H) :
    ‖variationalForcing j e F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simpa [variationalForcing_apply, real_inner_comm] using
    he.sum_inner_products_le (s := Finset.univ) F

theorem variationalMatrix_inner (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c d : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (variationalMatrix e B c) d =
      B (variationalReconstruction e c) (variationalReconstruction e d) := by
  simp [variationalMatrix, variationalReconstruction_apply, PiLp.inner_apply, map_sum]

theorem variationalForcing_inner (j : V →L[ℝ] H) (e : Fin m → V) (F : H)
    (c : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (variationalForcing j e F) c = inner ℝ F (j (variationalReconstruction e c)) := by
  simp [PiLp.inner_apply, variationalReconstruction_apply, map_sum, inner_sum, inner_smul_right]

def variationalTestEvaluation (e : Fin m → V) :
    (V →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ ℝ (e i)))

theorem variationalMatrix_eq_comp (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    variationalMatrix e B =
      (variationalTestEvaluation e).comp (B.comp (variationalReconstruction e)) := by
  ext c i
  simp [variationalMatrix, variationalTestEvaluation]

/-- This bound may depend on the finite basis. The later energy estimate does
 not use an H-orthogonal projection bound in the energy norm. -/
theorem variationalMatrix_norm_le (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    ‖variationalMatrix e B‖ ≤
      ‖variationalTestEvaluation e‖ * ‖B‖ * ‖variationalReconstruction e‖ := by
  rw [variationalMatrix_eq_comp]
  calc
    _ ≤ ‖variationalTestEvaluation e‖ * ‖B.comp (variationalReconstruction e)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖variationalTestEvaluation e‖ * (‖B‖ * ‖variationalReconstruction e‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_nonneg (variationalTestEvaluation e))
    _ = _ := by ring

theorem variationalMatrix_eq_sum (e : Fin m → V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    variationalMatrix e B = ∑ i, ∑ k, B (e k) (e i) •
      (EuclideanSpace.proj k).smulRight (EuclideanSpace.single i 1) := by
  ext c i
  simp [variationalMatrix_apply, Pi.single_apply, mul_comm]

theorem variationalMatrix_continuous (e : Fin m → V)
    (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (hc : ∀ u v, Continuous (fun t => B t u v)) :
    Continuous (fun t => variationalMatrix e (B t)) := by
  simp_rw [variationalMatrix_eq_sum]
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun k _ =>
    (hc (e k) (e i)).smul continuous_const))

end Yau.F04Proof
