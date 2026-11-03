import Yau.Proofs.P06WeakDDbarCurrentChart
import Yau.Proofs.P06ConeRepresentatives

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology Matrix ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Full support of the original volume promotes almost everywhere
positivity of a smooth actual (1,1) form to positivity at every point. -/
theorem smoothFormLE_of_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (hp : ∀ᵐ x ∂μ, (formHermitianMatrix A x).PosSemidef) : FormLE 0 A := by
  letI : μ.IsOpenPosMeasure := Yau.LeafProofs.L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  intro c
  rw [formHermitianMatrix_zero, sub_zero]
  have hcenter : WeakCurrent.chartHermitianMatrix A c (chartPt c c) =
      formHermitianMatrix A c := by
    rw [WeakCurrent.chartHermitianMatrix, chartForm]
    have hx : chartInv c (chartPt c c) = c :=
      (extChartAt (ComplexModel n) c).left_inv (mem_extChartAt_source c)
    rw [hx]
    exact G04Aux.centeredForm_matrix A c
  rw [← hcenter]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (WeakCurrent.chartHermitianMatrix_hermitian A h11 c _)
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (WeakCurrent.chartHermitianMatrix_hermitian A h11 c _).im_star_dotProduct_mulVec_self v |>.symm⟩
  let q : M.Carrier → ℝ := fun y =>
    (star v ⬝ᵥ (WeakCurrent.chartHermitianMatrix A c (chartPt c y) *ᵥ v)).re
  have hqc : ContinuousOn q (chartAt (ComplexVector n) c).source := by
    have he (a b : Fin n) : ContinuousOn
        (fun y => WeakCurrent.chartHermitianMatrix A c (chartPt c y) a b)
        (chartAt (ComplexVector n) c).source :=
      (WeakCurrent.chartHermitianMatrix_contDiffOn A hA c a b).continuousOn.comp
        (chartPt_continuousOn c) (fun y hy => by
          with_unfolding_all
            exact (extChartAt (ComplexModel n) c).map_source
              (by simpa only [extChartAt_source] using hy))
    change ContinuousOn (fun y => (∑ a, star (v a) *
      (∑ b, WeakCurrent.chartHermitianMatrix A c (chartPt c y) a b * v b)).re) _
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finsetSum
    intro a _
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro b _
    exact (he a b).mul continuousOn_const
  have hae : (fun y => min 0 (q y)) =ᵐ[μ.restrict (chartAt (ComplexVector n) c).source] 0 := by
    filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem (chartAt (ComplexVector n) c).open_source.measurableSet] with y hy hys
    have hz : chartPt c y ∈ chartTarget c := by
      with_unfolding_all
        exact (extChartAt (ComplexModel n) c).map_source
          (by simpa only [extChartAt_source] using hys)
    have hm : (WeakCurrent.chartHermitianMatrix A c (chartPt c y)).PosSemidef := by
      rw [WeakCurrent.chartHermitianMatrix_congruence A h11 c hz]
      have hiy : chartInv c (chartPt c y) = y :=
        (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hys)
      rw [hiy]
      exact hy.conjTranspose_mul_mul_same _
    have hq : 0 ≤ q y := (Complex.nonneg_iff.mp (hm.dotProduct_mulVec_nonneg v)).1
    exact min_eq_left hq
  have he := Measure.eqOn_open_of_ae_eq hae (chartAt (ComplexVector n) c).open_source
    (continuousOn_const.inf hqc) continuousOn_const (mem_chart_source _ c)
  change 0 ≤ q c
  simpa only [Pi.zero_apply, min_eq_left_iff] using he

theorem positiveCone_smooth_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hAL : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (hp : realizeActualForm g μ A hAL ∈ hodgeL2PositiveCone g μ) : FormLE 0 A := by
  apply smoothFormLE_of_ae g μ hμ A hA h11
  filter_upwards [positiveCone_representative_ae g μ A hAL h11 hp] with x hx
  have hm : formHermitianMatrix A x = formHermitianMatrix (Clip.positiveForm g.form A) x := by
    exact congrArg (fun P : (TangentVector M x) [⋀^Fin 2]→L[ℝ] ℝ =>
      fun a b => ((P ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] : ℂ) +
        Complex.I * (P ![chartVec x x (stdVec a), chartVec x x (stdVec b)] : ℂ)) / 2) hx
  rw [hm]
  simpa only [formHermitianMatrix_zero, sub_zero] using Clip.positiveForm_nonnegative g.form A x

theorem intervalCone_smooth_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hAL : L2RealForm g.form μ A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C)
    (hp : realizeActualForm g μ A hAL ∈ hodgeL2IntervalCone g μ C) :
    FormOrderBound g.form C A := by
  let W := G04Aux.omegaForm g.form
  have hW : SmoothRealForm W := G04Aux.omegaForm_smooth g.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)
  have hW11 : RealOneOne W := G04Aux.omegaForm_oneOne g.form
  have hmat (c : ℝ) (x : M.Carrier) : formHermitianMatrix (c • W) x =
      (c : ℂ) • gMat g.form x := by
    rw [G04Aux.formHermitianMatrix_real_smul,
      G04Aux.formHermitianMatrix_of_representsIota _ _ (G04Aux.omegaForm_represents g.form)]
  have hsm (c : ℝ) : SmoothRealForm (c • W) := smoothRealForm_smul c W hW
  have hty (c : ℝ) : RealOneOne (c • W) := realOneOne_multiply (fun _ => c) W hW11
  have hae := intervalCone_representative_ae g μ hμ A hAL h11 hC hp
  have hl : FormLE 0 (A - (-C) • W) := by
    apply smoothFormLE_of_ae g μ hμ _
      ((smoothFormSubmodule (M := M) 2).sub_mem hA (hsm (-C)))
      (realOneOne_sub A _ h11 (hty (-C)))
    filter_upwards [hae] with x hx
    rw [formHermitianMatrix_sub, hmat]
    have hm : formHermitianMatrix A x = formHermitianMatrix (Clip.intervalForm g.form C A) x := by
      exact congrArg (fun P : (TangentVector M x) [⋀^Fin 2]→L[ℝ] ℝ =>
      fun a b => ((P ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] : ℂ) +
        Complex.I * (P ![chartVec x x (stdVec a), chartVec x x (stdVec b)] : ℂ)) / 2) hx
    rw [hm]
    simpa only [Complex.ofReal_neg] using (Clip.intervalForm_orderBound g.form hC A h11 x).1
  have hu : FormLE 0 (C • W - A) := by
    apply smoothFormLE_of_ae g μ hμ _
      ((smoothFormSubmodule (M := M) 2).sub_mem (hsm C) hA)
      (realOneOne_sub _ A (hty C) h11)
    filter_upwards [hae] with x hx
    rw [formHermitianMatrix_sub, hmat]
    have hm : formHermitianMatrix A x = formHermitianMatrix (Clip.intervalForm g.form C A) x := by
      exact congrArg (fun P : (TangentVector M x) [⋀^Fin 2]→L[ℝ] ℝ =>
      fun a b => ((P ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] : ℂ) +
        Complex.I * (P ![chartVec x x (stdVec a), chartVec x x (stdVec b)] : ℂ)) / 2) hx
    rw [hm]
    exact (Clip.intervalForm_orderBound g.form hC A h11 x).2
  intro x
  have h₁ := hl x
  have h₂ := hu x
  simp only [formHermitianMatrix_zero, sub_zero, formHermitianMatrix_sub, hmat] at h₁ h₂
  exact ⟨by simpa only [Complex.ofReal_neg] using h₁, h₂⟩

end Yau.NodeProofs.P06Aux
