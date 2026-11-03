import Yau.LeafProofs.L17ScalarSymbol

/-!
Pullback formulas use the differential of the actual local parametrization.
No free frame, Kähler identity, or flow existence assumption enters this file.
-/

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def pullbackMatrix (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => LeafCandidates.pullbackCoefficient g e z i j

theorem pullbackMatrix_isHermitian (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    (pullbackMatrix g e z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact ((g (e z)).conjugate_symmetric _ _).symm

theorem complexVector_basis_sum (v : ComplexVector n) :
    (∑ i, v i • stdVec i) = v := by
  ext i
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem pullbackMatrix_sesquilinear (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (z : ComplexVector n)
    (u v : ComplexVector n) :
    star (WithLp.ofLp u) ⬝ᵥ (pullbackMatrix g e z *ᵥ WithLp.ofLp v) =
      (g (e z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) e z u)
        (mfderiv (ComplexModel n) (ComplexModel n) e z v) := by
  have hL (w : ComplexVector n) :
      mfderiv (ComplexModel n) (ComplexModel n) e z w =
        ∑ i, w i • mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec i) := by
    calc
      _ = mfderiv (ComplexModel n) (ComplexModel n) e z (∑ i, w i • stdVec i) :=
        congrArg _ (complexVector_basis_sum w).symm
      _ = _ := by
        let L : ComplexVector n →L[ℂ] TangentVector M (e z) :=
          (mfderiv (ComplexModel n) (ComplexModel n) e z).comp
            (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm.toContinuousLinearMap
        change L (∑ i, w i • stdVec i) = ∑ i, w i • L (stdVec i)
        rw [map_sum]
        simp only [map_smul]
  rw [hL u, hL v]
  rw [L12Aux.hermitian_sum_left]
  simp only [L12Aux.hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, pullbackMatrix, LeafCandidates.pullbackCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Both inverse identities are native manifold derivative identities. -/
theorem chart_mfderiv_left_inverse
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    (mfderiv (ComplexModel n) (ComplexModel n) e.symm (e z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) e z) =
        ContinuousLinearMap.id ℂ _ :=
  (show e.MDifferentiable (ComplexModel n) (ComplexModel n) from ⟨he, hei⟩).symm_comp_deriv hz

theorem chart_mfderiv_right_inverse
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {y : M.Carrier} (hy : y ∈ e.target) :
    (mfderiv (ComplexModel n) (ComplexModel n) e (e.symm y)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) e.symm y) =
        ContinuousLinearMap.id ℂ _ :=
  (show e.MDifferentiable (ComplexModel n) (ComplexModel n) from ⟨he, hei⟩).comp_symm_deriv hy

/-- The background chart induces a genuine equivalence with the tangent fibre. -/
def chartFrameEquiv
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    ComplexVector n ≃L[ℂ] TangentVector M (e z) :=
  (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm.trans
    ((show e.MDifferentiable (ComplexModel n) (ComplexModel n) from ⟨he, hei⟩).mfderiv hz)

theorem chartFrameEquiv_apply
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (v : ComplexVector n) :
    chartFrameEquiv e he hei hz v = mfderiv (ComplexModel n) (ComplexModel n) e z v := rfl

theorem chart_mfderiv_injective
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    Function.Injective (mfderiv (ComplexModel n) (ComplexModel n) e z) :=
  (show e.MDifferentiable (ComplexModel n) (ComplexModel n) from ⟨he, hei⟩).mfderiv_injective hz

theorem pullbackMatrix_posDef
    (g : HermitianField M) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    (pullbackMatrix g e z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (pullbackMatrix_isHermitian g e z)
  intro u hu
  rw [pullbackMatrix_sesquilinear g e z (WithLp.toLp 2 u) (WithLp.toLp 2 u)]
  apply Complex.pos_iff.mpr
  refine ⟨hermitianNormSq_pos (g (e z)) ?_, ((g (e z)).self_adjoint _).symm⟩
  intro hzero
  have hzv := chart_mfderiv_injective e he hei hz
    (show mfderiv (ComplexModel n) (ComplexModel n) e z (WithLp.toLp 2 u) =
      mfderiv (ComplexModel n) (ComplexModel n) e z 0 by simpa using hzero)
  apply hu
  ext i
  exact congrArg (fun w : ComplexVector n => w i) hzv

theorem pullbackMatrix_det_re_pos
    (g : HermitianField M) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    0 < (pullbackMatrix g e z).det.re :=
  (Complex.pos_iff.mp (pullbackMatrix_posDef g e he hei hz).det_pos).1

/-- Complex polarization of the actual matrix quadratic values. -/
theorem matrix_eq_of_quadratic_eq {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ v : Fin n → ℂ, star v ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ (B *ᵥ v)) :
    A = B := by
  classical
  ext i j
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hs := h (Pi.single i 1 + Pi.single j 1)
  have hI := h (Pi.single i 1 + Complex.I • Pi.single j 1)
  simp only [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct] at hs hI
  simp at hi hj hs hI
  linear_combination (norm := ring_nf) (1 / 2 : ℂ) * hs - (1 / 2 : ℂ) * hi -
    (1 / 2 : ℂ) * hj - (Complex.I / 2) * hI + (Complex.I / 2) * hi +
      (Complex.I / 2) * hj
  norm_num [Complex.I_sq, pow_succ]

/-- Matrix of an actual complex linear differential in the standard frames. -/
def linearMatrix {m : ℕ} (L : ComplexVector n →L[ℂ] ComplexVector m) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => L (stdVec j) i

theorem linearMatrix_mulVec {m : ℕ}
    (L : ComplexVector n →L[ℂ] ComplexVector m) (v : ComplexVector n) :
    linearMatrix L *ᵥ WithLp.ofLp v = WithLp.ofLp (L v) := by
  have he : L v = ∑ i, v i • L (stdVec i) := by
    conv_lhs => rw [← complexVector_basis_sum v, map_sum]
    simp only [map_smul]
  ext i
  rw [he]
  simp [linearMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem congruence_quadratic {m : ℕ}
    (J : Matrix (Fin m) (Fin n) ℂ) (H : Matrix (Fin m) (Fin m) ℂ)
    (v : Fin n → ℂ) :
    star v ⬝ᵥ ((Jᴴ * H * J) *ᵥ v) =
      star (J *ᵥ v) ⬝ᵥ (H *ᵥ (J *ᵥ v)) := by
  conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.star_mulVec]

/-- Full matrix naturality, with the project's conjugate-linear-first convention. -/
theorem leviC_comp {m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) :
    leviC (f ∘ T) z =
      (linearMatrix (fderiv ℂ T z))ᴴ * leviC f (T z) *
        linearMatrix (fderiv ℂ T z) := by
  apply matrix_eq_of_quadratic_eq
  intro v
  rw [congruence_quadratic]
  have hv := linearMatrix_mulVec (fderiv ℂ T z) (WithLp.toLp 2 v)
  rw [hv]
  have hleft := L22Aux.leviC_quadratic (hf.comp z (hT.restrict_scalars ℝ))
    (WithLp.toLp 2 v)
  rw [hleft, L22Aux.leviC_quadratic hf, L22Aux.complexLeviQuadratic_comp hT hf]

theorem leviC_comp_posSemidef {m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (hpos : (leviC f (T z)).PosSemidef) :
    (leviC (f ∘ T) z).PosSemidef := by
  rw [leviC_comp hT hf]
  exact hpos.conjTranspose_mul_mul_same _

/-- Smooth real metric coefficients recover both parts of the Hermitian matrix. -/
theorem hMat_contDiffOn_of_metricSmooth
    (g : HermitianField M) (hg : MetricSmooth g) (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat g a z i j) (chartTarget a) := by
  have hr := (contDiffOn_const.mul (hg a (i, 0) (j, 0)) :
    ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * realMetricFn g a z (i, 0) (j, 0)) _)
  have hi := (contDiffOn_const.mul (hg a (i, 1) (j, 0)) :
    ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * realMetricFn g a z (i, 1) (j, 0)) _)
  have h := (Complex.ofRealCLM.contDiff.comp_contDiffOn hr).add
    ((contDiffOn_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hi))
  apply h.congr
  intro z hz
  apply Complex.ext <;>
    simp [L12Aux.realMetricFn_entries, Complex.mul_re, Complex.mul_im]

theorem logDet_contDiffOn_of_metricSmooth
    (g : HermitianField M) (hg : MetricSmooth g) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (logDet g a) (chartTarget a) := by
  have hd := Complex.reCLM.contDiff.comp_contDiffOn
    (L12Aux.contDiffOn_matrix_det (hMat_contDiffOn_of_metricSmooth g hg a))
  exact hd.log fun z hz => (L12Aux.hMat_det_re_pos g a hz).ne'

def coordinateDifferential (e : ComplexVector n → M.Carrier) (a : M.Carrier)
    (z : ComplexVector n) : ComplexVector n →L[ℂ] ComplexVector n :=
  (NormedSpace.fromTangentSpace (𝕜 := ℂ) (chartPt a (e z))).toContinuousLinearMap ∘L
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a) (e z)) ∘L
    (mfderiv (ComplexModel n) (ComplexModel n) e z) ∘L
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm.toContinuousLinearMap

theorem coordinateDifferential_apply (e : ComplexVector n → M.Carrier) (a : M.Carrier)
    (z u : ComplexVector n) :
    coordinateDifferential e a z u =
      tangentCoords a (e z) (mfderiv (ComplexModel n) (ComplexModel n) e z u) := rfl

theorem chartVec_basis_sum (a y : M.Carrier) (v : ComplexVector n) :
    (∑ i, v i • chartVec a y (stdVec i)) = chartVec a y v := by
  simp_rw [← L12Aux.chartVec_complex_smul]
  rw [← L12Aux.chartVec_sum, complexVector_basis_sum]

theorem hMat_quadratic_chartVec (g : HermitianField M) (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector n) :
    star (WithLp.ofLp v) ⬝ᵥ (hMat g a (chartPt a y) *ᵥ WithLp.ofLp v) =
      (g y).toFun (chartVec a y v) (chartVec a y v) := by
  rw [L12Aux.hMat_quadratic]
  have he : chartInv a (chartPt a y) = y := (extChartAt (ComplexModel n) a).left_inv hy
  simp only [chartVec_basis_sum]
  rw [he]

/-- Genuine metric pullback in any local parametrization, in a fixed canonical frame. -/
theorem pullbackMatrix_eq_congruence (g : HermitianField M)
    (e : ComplexVector n → M.Carrier) (a : M.Carrier) (z : ComplexVector n)
    (hz : e z ∈ (extChartAt (ComplexModel n) a).source) :
    pullbackMatrix g e z = (linearMatrix (coordinateDifferential e a z))ᴴ *
      hMat g a (chartPt a (e z)) * linearMatrix (coordinateDifferential e a z) := by
  apply matrix_eq_of_quadratic_eq
  intro v
  rw [congruence_quadratic]
  have hv := linearMatrix_mulVec (coordinateDifferential e a z) (WithLp.toLp 2 v)
  rw [hv, hMat_quadratic_chartVec g a (e z) hz, coordinateDifferential_apply,
    L12Aux.chartVec_tangentCoords a (e z) hz]
  exact pullbackMatrix_sesquilinear g e z (WithLp.toLp 2 v) (WithLp.toLp 2 v)

theorem coordinateDifferential_injective
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ e.source)
    (ha : e z ∈ (extChartAt (ComplexModel n) a).source) :
    Function.Injective (coordinateDifferential e a z) := by
  intro u v huv
  apply chart_mfderiv_injective e he hei hz
  have h := congrArg (chartVec a (e z)) huv
  simpa only [coordinateDifferential_apply, L12Aux.chartVec_tangentCoords a (e z) ha] using h

theorem linearMatrix_det_ne_zero
    (L : ComplexVector n →L[ℂ] ComplexVector n) (hL : Function.Injective L) :
    (linearMatrix L).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have he := congrArg (WithLp.toLp 2) huv
  simp only [linearMatrix_mulVec L (WithLp.toLp 2 u),
    linearMatrix_mulVec L (WithLp.toLp 2 v), WithLp.toLp_ofLp] at he
  have huv' := hL he
  exact congrArg WithLp.ofLp huv'

theorem congruence_det (H J : Matrix (Fin n) (Fin n) ℂ) :
    (Jᴴ * H * J).det = (Complex.normSq J.det : ℂ) * H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  calc
    star J.det * H.det * J.det = (star J.det * J.det) * H.det := by ring
    _ = _ := by rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem congruence_det_re (H J : Matrix (Fin n) (Fin n) ℂ) :
    (Jᴴ * H * J).det.re = Complex.normSq J.det * H.det.re := by
  rw [congruence_det]
  simp

/-- The Jacobian factor cancels from the original real determinant quotient. -/
theorem determinant_ratio_congruence (H G J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.det ≠ 0) :
    (Jᴴ * H * J).det.re / (Jᴴ * G * J).det.re = H.det.re / G.det.re := by
  rw [congruence_det_re, congruence_det_re]
  exact mul_div_mul_left _ _ (Complex.normSq_pos.mpr hJ).ne'

theorem pullbackMatrix_determinant_ratio
    (h g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ e.source)
    (ha : e z ∈ (extChartAt (ComplexModel n) a).source) :
    (pullbackMatrix h e z).det.re / (pullbackMatrix g e z).det.re =
      (hMat h a (chartPt a (e z))).det.re / (hMat g a (chartPt a (e z))).det.re := by
  rw [pullbackMatrix_eq_congruence h e a z ha, pullbackMatrix_eq_congruence g e a z ha]
  exact determinant_ratio_congruence _ _ _ (linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei a hz ha))

end Yau.LeafProofs.L17Aux
