import Yau.Proofs.P06HodgeRegularityScalarEnergy

/-! Exact scalar-principal cutoff identity with a forcing term that depends
only on values. It is the local H¹ entry for actual Hodge graph approximants. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem regularityDirection_const_mul {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℝ) (e : E) :
    regularityDirection e (fun z => c * u z) = fun z => c * regularityDirection e u z := by
  rw [regularityDirection_mul contDiff_const hu]
  simp only [regularityDirection, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, zero_add]

def regularityScalarCutoffFlux (v : ι → E) (q : ι → ι → E → ℝ)
    (χ u : E → ℝ) (i : ι) : E → ℝ :=
  fun z => -2 * ∑ j, (q i j z * regularityDirection (v j) χ z) * u z

def regularityScalarCutoffCoeff (v : ι → E) (q : ι → ι → E → ℝ)
    (χ : E → ℝ) : E → ℝ :=
  fun z => ∑ i, ∑ j, regularityDirection (v i)
    (fun y => q i j y * regularityDirection (v j) χ y) z

/-- The exact cutoff error is a value term plus the divergence of a value
flux. In particular no derivative of the unknown field is needed in either. -/
theorem regularityScalarDiv_cutoff
    (v : ι → E) (q : ι → ι → E → ℝ) {χ u : E → ℝ}
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hqs : ∀ i j z, q i j z = q j i z)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) (z : E) :
    regularityScalarDiv v q (fun y => χ y * u y) z =
      χ z * regularityScalarDiv v q u z + regularityScalarCutoffCoeff v q χ z * u z +
        ∑ i, regularityDirection (v i) (regularityScalarCutoffFlux v q χ u i) z := by
  classical
  let S := fun i j => regularityDirection (v i)
    (fun y => q i j y * regularityDirection (v j) u y)
  let T := fun i j y => regularityDirection (v i) χ y * q i j y * regularityDirection (v j) u y
  let R := fun i j => regularityDirection (v i)
    (fun y => (q i j y * regularityDirection (v j) χ y) * u y)
  let D := fun i j => regularityDirection (v i)
    (fun y => q i j y * regularityDirection (v j) χ y)
  have hqχ (i j : ι) : ContDiff ℝ ∞ (fun y => q i j y * regularityDirection (v j) χ y) :=
    (hq i j).mul (regularityDirection_contDiff hχ (v j))
  have hsplit (i j : ι) : regularityDirection (v i)
      (fun y => q i j y * regularityDirection (v j) (fun t => χ t * u t) y) =
      fun y => χ y * S i j y + T i j y + R i j y := by
    have hprod : (fun y => q i j y * regularityDirection (v j) (fun t => χ t * u t) y) =
        fun y => χ y * (q i j y * regularityDirection (v j) u y) +
          (q i j y * regularityDirection (v j) χ y) * u y := by
      rw [regularityDirection_mul hχ hu (v j)]
      funext y
      ring
    rw [hprod, regularityDirection_add
      (hχ.mul ((hq i j).mul (regularityDirection_contDiff hu (v j)))) ((hqχ i j).mul hu) (v i),
      regularityDirection_mul hχ ((hq i j).mul (regularityDirection_contDiff hu (v j))) (v i)]
    funext y
    dsimp only [S, T, R]
    ring
  have hR (i j : ι) : R i j z = D i j z * u z +
      (q i j z * regularityDirection (v j) χ z) * regularityDirection (v i) u z := by
    exact congrFun (regularityDirection_mul (hqχ i j) hu (v i)) z
  have hcross : (∑ i, ∑ j, (q i j z * regularityDirection (v j) χ z) * regularityDirection (v i) u z) =
      ∑ i, ∑ j, T i j z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [T]
    rw [hqs j i z]
    ring
  have hRsum : (∑ i, ∑ j, R i j z) = regularityScalarCutoffCoeff v q χ z * u z +
      ∑ i, ∑ j, T i j z := by
    simp_rw [hR, Finset.sum_add_distrib]
    rw [hcross]
    simp only [regularityScalarCutoffCoeff, D, Finset.sum_mul]
  have hflux (i : ι) : regularityDirection (v i) (regularityScalarCutoffFlux v q χ u i) =
      fun y => -2 * ∑ j, R i j y := by
    unfold regularityScalarCutoffFlux
    rw [regularityDirection_const_mul
      (ContDiff.sum fun j _ => (hqχ i j).mul hu) (-2) (v i),
      regularityDirection_sum _ (fun j => (hqχ i j).mul hu) (v i)]
  have hleft : regularityScalarDiv v q (fun y => χ y * u y) z =
      χ z * regularityScalarDiv v q u z - (∑ i, ∑ j, T i j z) - ∑ i, ∑ j, R i j z := by
    unfold regularityScalarDiv
    simp_rw [hsplit, Finset.sum_add_distrib]
    simp only [S, ← Finset.mul_sum]
    ring
  rw [hleft]
  simp_rw [hflux]
  rw [← Finset.mul_sum, hRsum]
  ring

end Yau.NodeProofs.P06Aux
