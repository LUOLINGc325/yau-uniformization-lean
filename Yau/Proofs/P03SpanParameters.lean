import Yau.Proofs.P03ProjectiveCoordinates
import Yau.Proofs.P03AffineSchurParameters

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

def coordinatePairing {n : ℕ} (q : Fin n → ℂ) : ComplexVector n →L[ℂ] ℂ :=
  ∑ i, q i • EuclideanSpace.proj i

theorem coordinatePairing_apply {n : ℕ} (q : Fin n → ℂ) (v : ComplexVector n) :
    coordinatePairing q v = ∑ i, q i * v i := by
  simp only [coordinatePairing, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, EuclideanSpace.coe_proj, smul_eq_mul]

theorem coordinatePairing_stdVec {n : ℕ} (q : Fin n → ℂ) (i : Fin n) :
    coordinatePairing q (stdVec i) = q i := by
  rw [coordinatePairing_apply]
  simp [stdVec, PiLp.single_apply, Pi.single_apply, eq_comm]

theorem coordinatePairing_eq_zero_iff {n : ℕ} (q : Fin n → ℂ) :
    coordinatePairing q = 0 ↔ q = 0 := by
  constructor
  · intro h
    funext i
    have heq := DFunLike.congr_fun h (stdVec i)
    simpa only [coordinatePairing_stdVec, ContinuousLinearMap.zero_apply, Pi.zero_apply] using heq
  · rintro rfl
    ext v
    rw [coordinatePairing_apply]
    simp

/-- The dual evaluation map tests actual finite spanning by injectivity,
so the native openness theorem for injective linear maps applies directly. -/
def annihilatorEvaluationCLM {n m : ℕ} (V : Fin m → ComplexVector n) :
    (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi (fun j => ∑ i, V j i • ContinuousLinearMap.proj i)

theorem annihilatorEvaluationCLM_apply {n m : ℕ} (V : Fin m → ComplexVector n)
    (q : Fin n → ℂ) (j : Fin m) :
    annihilatorEvaluationCLM V q j = coordinatePairing q (V j) := by
  simp only [annihilatorEvaluationCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, coordinatePairing_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem span_top_iff_annihilatorEvaluation_injective {n m : ℕ}
    (V : Fin m → ComplexVector n) :
    Submodule.span ℂ (range V) = ⊤ ↔ Function.Injective (annihilatorEvaluationCLM V) := by
  constructor
  · intro hspan q q' hq
    let qd := q - q'
    have hzero : annihilatorEvaluationCLM V qd = 0 := by
      simp only [qd, map_sub, hq, sub_self]
    have hker : Submodule.span ℂ (range V) ≤ (coordinatePairing qd).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change coordinatePairing qd (V j) = 0
      have h := congrFun hzero j
      simpa only [annihilatorEvaluationCLM_apply, Pi.zero_apply] using h
    rw [hspan] at hker
    have hpair : coordinatePairing qd = 0 := by
      ext v
      exact hker (Submodule.mem_top)
    exact sub_eq_zero.mp ((coordinatePairing_eq_zero_iff qd).mp hpair)
  · intro hinj
    by_contra hspan
    obtain ⟨pivot, w, hw⟩ := exists_projective_annihilator V hspan
    have hz : annihilatorEvaluationCLM V (projectiveCoordinates pivot w) =
        annihilatorEvaluationCLM V 0 := by
      ext j
      rw [map_zero, Pi.zero_apply, annihilatorEvaluationCLM_apply, coordinatePairing_apply]
      exact hw j
    have heq := congrFun (hinj hz) pivot
    simpa [projectiveCoordinates_pivot] using heq

def affineVectorTuple {n m L : ℕ} (V : Fin m → ComplexVector n)
    (W : Fin L → ComplexVector n) (T : Fin m → Fin L → ℂ) : Fin m → ComplexVector n :=
  fun j => V j + ∑ l, T j l • W l

/-- Every failed span is covered by a projective annihilator and an actual
affine row-solving chart. No transversality or rank-stratum oracle is used. -/
theorem affineVectorTuple_bad_span_chart {n m L : ℕ}
    (V : Fin m → ComplexVector n) (W : Fin L → ComplexVector n)
    (hW : Submodule.span ℂ (range W) = ⊤) (T : Fin m → Fin L → ℂ)
    (hbad : Submodule.span ℂ (range (affineVectorTuple V W T)) ≠ ⊤) :
    ∃ (direction : Fin n) (w : {i : Fin n // i ≠ direction} → ℂ) (pivot : Fin L),
      let ξ := coordinatePairing (projectiveCoordinates direction w)
      ξ (W pivot) ≠ 0 ∧
      T = affineSchurRows (fun l => ξ (W l)) pivot (fun j => -ξ (V j))
        (fun j q => T j q.1) := by
  classical
  obtain ⟨direction, w, hw⟩ := exists_projective_annihilator (affineVectorTuple V W T) hbad
  let ξ := coordinatePairing (projectiveCoordinates direction w)
  have hξ : ξ.toLinearMap ≠ 0 := by
    intro h
    have heq := DFunLike.congr_fun h (stdVec direction)
    change coordinatePairing (projectiveCoordinates direction w) (stdVec direction) = 0 at heq
    simpa [coordinatePairing_stdVec, projectiveCoordinates_pivot] using heq
  obtain ⟨pivot, hp⟩ := exists_pivot_pairing_of_span_top W hW ξ.toLinearMap hξ
  refine ⟨direction, w, pivot, hp, ?_⟩
  apply affineSchurRows_cover _ pivot hp
  intro j
  have hz : ξ (affineVectorTuple V W T j) = 0 := by
    rw [coordinatePairing_apply]
    exact hw j
  change ξ (V j + ∑ l, T j l • W l) = 0 at hz
  rw [map_add, map_sum] at hz
  simp only [map_smul, smul_eq_mul] at hz
  exact eq_neg_of_add_eq_zero_right hz

end Yau.NodeProofs.P03Aux
