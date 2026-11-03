import Yau.Blueprint.Alignment
import Yau.LeafProofs.SharedCalculus

/-! Recover smooth complex metric coefficients and the actual dual norm from MetricFamilySmooth. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem chartVec_smul (x y : M.Carrier) (c : ℂ) (v : ComplexVector n) :
    chartVec x y (c • v) = c • chartVec x y v := by
  exact (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_smul c v

theorem realMetricFn_entries (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a b : RIdx n) :
    realMetricFn h x z a b = 2 *
      (if a.2 = b.2 then (hMat h x z a.1 b.1).re
        else if a.2 = 0 then -(hMat h x z a.1 b.1).im
        else (hMat h x z a.1 b.1).im) := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realMetricFn, realVec, hMat, stdVec, chartVec_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right]

theorem hMat_of_realMetricFn (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (i j : Fin n) :
    hMat h x z i j = (realMetricFn h x z (i, 0) (j, 0) / 2 : ℂ) -
      Complex.I * (realMetricFn h x z (i, 0) (j, 1) / 2 : ℂ) := by
  rw [realMetricFn_entries, realMetricFn_entries]
  apply Complex.ext <;> simp
  ring

theorem metricFamily_hMat_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hsmooth : MetricFamilySmooth h I) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => hMat (h p.2) x p.1 i j)
      (chartTarget x ×ˢ I) := by
  simp_rw [hMat_of_realMetricFn]
  have h₁ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hsmooth x (i, 0) (j, 0)).div_const 2)
  have h₂ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hsmooth x (i, 0) (j, 1)).div_const 2)
  convert h₁.sub ((contDiffOn_const (c := Complex.I)).mul h₂) using 1
  funext p
  simp [Complex.ofReal_div]

theorem hermitian_sum_left {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_left (0 : ℂ) (0 : V) v
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_left, ih]

theorem hermitian_sum_right {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_right (0 : ℂ) u (0 : V)
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_right, ih]

theorem hMat_quadratic (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (u : Fin n → ℂ) :
    star u ⬝ᵥ ((hMat h x z) *ᵥ u) =
      (h (chartInv x z)).toFun
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i))
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i)) := by
  rw [hermitian_sum_left]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, hMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartVec_injective (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) : Function.Injective (chartVec x y) := by
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  have hleft : Function.LeftInverse (tangentCoords x y) (chartVec x y) := by
    intro v
    have hv := congrArg (fun L => L v) hcomp
    exact hv
  exact hleft.injective

theorem hMat_posDef (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) : (hMat h x z).PosDef := by
  classical
  have hherm : (hMat h x z).IsHermitian := by
    ext i j
    exact ((h (chartInv x z)).conjugate_symmetric _ _).symm
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hherm
  intro u hu
  rw [hMat_quadratic]
  apply Complex.pos_iff.2
  refine ⟨hermitianNormSq_pos (h (chartInv x z)) ?_, ((h (chartInv x z)).self_adjoint _).symm⟩
  intro hzero
  have hsum : ∑ i, u i • stdVec i = (WithLp.toLp 2 u : ComplexVector n) := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have heq : ∑ i, u i • chartVec x (chartInv x z) (stdVec i) =
      chartVec x (chartInv x z) (WithLp.toLp 2 u) := by
    rw [← hsum]
    exact ((map_sum (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x (chartInv x z))) _ _).trans
        (Finset.sum_congr rfl fun i _ => chartVec_smul _ _ _ _)).symm
  rw [heq] at hzero
  have hzsource := (extChartAt (ComplexModel n) x).map_target hz
  have hzero' : chartVec x (chartInv x z) (WithLp.toLp 2 u) = chartVec x (chartInv x z) 0 := by
    have hzv : chartVec x (chartInv x z) 0 = 0 :=
      (mfderiv (ComplexModel n) (ComplexModel n)
        (extChartAt (ComplexModel n) x).symm (chartPt x (chartInv x z))).map_zero
    simpa only [hzv] using hzero
  have hu0 := chartVec_injective x (chartInv x z) hzsource hzero'
  apply hu
  ext i
  simpa using congrArg (fun v : ComplexVector n => v i) hu0

theorem metricFamily_hMat_inv_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hsmooth : MetricFamilySmooth h I) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (hMat (h p.2) x p.1)⁻¹ i j)
      (chartTarget x ×ˢ I) := by
  apply Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv (metricFamily_hMat_contDiffOn hsmooth x)
  intro p hp
  exact ne_of_gt (hMat_posDef (h p.2) x p.1 hp.1).det_pos

theorem dualNormClock_joint_contDiffAt {h : ℝ → HermitianField M}
    (hsmooth : MetricFamilySmooth h (Set.Ici 0)) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n × ℂ) (hq : q.1 ∈ chartTarget x) :
    ContDiffAt ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℂ =>
      dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1) q := by
  have hopen : IsOpen (chartTarget x) := isOpen_extChartAt_target x
  have hnhds : chartTarget x ×ˢ Set.Ici 0 ∈ 𝓝 (q.1, Real.exp (2 * q.2.2.re)) :=
    prod_mem_nhds (hopen.mem_nhds hq) (Ici_mem_nhds (Real.exp_pos _))
  have hre : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℂ => p.2.2.re) q :=
    Complex.reCLM.contDiff.contDiffAt.comp q contDiffAt_snd.snd
  have hmap : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℂ =>
      (p.1, Real.exp (2 * p.2.2.re))) q :=
    contDiffAt_fst.prodMk ((contDiffAt_const.mul hre).exp)
  have hcoeff : ∀ i j, ContDiffAt ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℂ =>
      (hMat (h (Real.exp (2 * p.2.2.re))) x p.1)⁻¹ i j) q := by
    intro i j
    exact ((metricFamily_hMat_inv_contDiffOn hsmooth x i j).contDiffAt hnhds).comp
      (f := fun p : ComplexVector n × ComplexVector n × ℂ => (p.1, Real.exp (2 * p.2.2.re))) q
      hmap
  have hξ : ∀ i, ContDiffAt ℝ ∞ (fun p : ComplexVector n × ComplexVector n × ℂ => p.2.1 i) q :=
    fun i => by fun_prop
  unfold dualNormChart dualNormMat Matrix.mulVec dotProduct
  apply Complex.reCLM.contDiff.contDiffAt.comp
  apply ContDiffAt.sum
  intro i _
  exact (Complex.conjCLE.contDiff.contDiffAt.comp q (hξ i)).mul
    (ContDiffAt.sum fun j _ => (hcoeff j i).mul (hξ j))

end Yau.Blueprint.Alignment.Y03Proof
