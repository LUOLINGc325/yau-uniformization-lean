import Yau.Proofs.F01MatrixCoercivity

/-! Positive definiteness persists in an actual continuous Hermitian
matrix family, proved by the genuine real bilinear operator norm. -/
noncomputable section
open Set Filter
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ} {A : Type*} [TopologicalSpace A]

theorem eventually_posDef_of_continuousAt_hermitian
    (G : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a)
    (hHerm : ∀ p, (G p).IsHermitian) (hpos : (G a).PosDef) :
    ∀ᶠ p in 𝓝 a, (G p).PosDef := by
  letI : NormedAddCommGroup (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) := inferInstance
  let T : (Fin n → Fin n → ℂ) →L[ℝ]
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin n → Fin n → ℂ)
      (F' := EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)
      (matrixRealBilinearMap (ι := Fin n))
  obtain ⟨ℓ, C, hℓ, hC, hb⟩ := compact_posDef_quadratic_bounds
    (G := fun _ : Unit => G a) (K := {()}) isCompact_singleton
    continuous_const.continuousOn (fun _ _ => hpos)
  have hnorm : ContinuousAt (fun p => ‖(fun i j => G p i j) - (fun i j => G a i j)‖) a :=
    (hG.sub continuousAt_const).norm
  have hcenter : ‖(fun i j => G a i j) - (fun i j => G a i j)‖ <
      (ℓ / 2) / (‖T‖ + 1) := by
    simpa only [sub_self, norm_zero] using (div_pos (half_pos hℓ) (by positivity : 0 < ‖T‖ + 1))
  have hsmall : ∀ᶠ p in 𝓝 a, ‖(fun i j => G p i j) - (fun i j => G a i j)‖ <
      (ℓ / 2) / (‖T‖ + 1) :=
    hnorm.eventually (Iio_mem_nhds hcenter)
  filter_upwards [hsmall] with p hp
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hHerm p)
  intro ξ hξ
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 ξ
  have hv : v ≠ 0 := by
    intro hv0
    have hh := congrArg WithLp.ofLp hv0
    exact hξ (by simpa only [WithLp.ofLp_toLp, WithLp.ofLp_zero] using hh)
  let D := T ((fun i j => G p i j) - (fun i j => G a i j))
  have hD : ‖D‖ < ℓ / 2 := by
    calc
      ‖D‖ ≤ ‖T‖ * ‖(fun i j => G p i j) - (fun i j => G a i j)‖ := T.le_opNorm _
      _ ≤ (‖T‖ + 1) * ‖(fun i j => G p i j) - (fun i j => G a i j)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < ℓ / 2 := by
        have hh := (lt_div_iff₀ (by positivity : 0 < ‖T‖ + 1)).mp hp
        simpa only [mul_comm] using hh
  have habs : |D v v| ≤ ‖D‖ * ‖v‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg v)
      _ = _ := by ring
  have hdiff : D v v = matrixRealBilinear (G p) v v - matrixRealBilinear (G a) v v := by
    simp only [D, map_sub, sub_apply]
    rfl
  have hlo : ℓ * ‖v‖ ^ 2 ≤ matrixRealBilinear (G a) v v :=
    (hb () (by simp) v).1
  have hnv : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hstrict := mul_lt_mul_of_pos_right hD hnv
  have hreal : 0 < matrixRealBilinear (G p) v v := by
    rw [hdiff] at habs
    have hh := (abs_le.mp habs).1
    nlinarith
  apply Complex.pos_iff.mpr
  constructor
  · exact hreal
  · have hh := congrArg Complex.im ((hHerm p).star_dotProduct_mulVec_comm ξ ξ)
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith

end Yau.NodeProofs.F01Aux
