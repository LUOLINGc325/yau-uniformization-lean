import Yau.Proofs.D03ClosureSubmoduleLocal

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Bundle Module

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem closure_normSq_zero (h : HermitianInnerProduct V) : hermitianNormSq h 0 = 0 := by
  have hz : h.toFun 0 0 = 0 := by simpa using h.map_smul_left 0 (0 : V) (0 : V)
  simp only [hermitianNormSq, hz, Complex.zero_re]

theorem closure_normSq_smul (h : HermitianInnerProduct V) (a : ℂ) (v : V) :
    hermitianNormSq h (a • v) = ‖a‖ ^ 2 * hermitianNormSq h v := by
  unfold hermitianNormSq
  rw [h.map_smul_left, h.map_smul_right]
  have he : star a * (h.toFun v v * a) = (a * star a) * h.toFun v v := by ring
  rw [he, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

theorem closure_normSq_add_le (h : HermitianInnerProduct V) (u v : V) :
    hermitianNormSq h (u + v) ≤ 2 * hermitianNormSq h u + 2 * hermitianNormSq h v := by
  have he : hermitianNormSq h (u + v) + hermitianNormSq h (u + (-1 : ℂ) • v) =
      2 * hermitianNormSq h u + 2 * hermitianNormSq h v := by
    simp only [hermitianNormSq, h.map_add_left, h.map_add_right, h.map_smul_left,
      h.map_smul_right, star_neg, star_one, neg_mul, mul_neg, one_mul, mul_one,
      Complex.add_re, Complex.neg_re]
    ring
  linarith [hermitianNormSq_nonneg h (u + (-1 : ℂ) • v)]

private theorem closure_hermitian_sum_left (h : HermitianInnerProduct V)
    {ι : Type*} (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  have hz : h.toFun 0 v = 0 := by simpa using h.map_smul_left 0 (0 : V) v
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert i s hi ih => simp [hi, h.map_add_left, ih]

private theorem closure_hermitian_sum_right (h : HermitianInnerProduct V)
    {ι : Type*} (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  have hz : h.toFun u 0 = 0 := by simpa using h.map_smul_right 0 u (0 : V)
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert i s hi ih => simp [hi, h.map_add_right, ih]

private theorem closure_hermitian_coordinates (h : HermitianInnerProduct V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V) (u v : V) :
    (∑ i, ∑ j, star (b.repr u i) * h.toFun (b i) (b j) * b.repr v j) = h.toFun u v := by
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [closure_hermitian_sum_left, closure_hermitian_sum_right, h.map_smul_left,
    h.map_smul_right, Finset.sum_mul]
  rw [Finset.sum_comm]
end Algebra

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

private def closure_frameBasis (a x : M.Carrier)
    (hx : x ∈ (BundleDbar.localTriv (r := r) E a).baseSet) : Basis (Fin r) ℂ (E x) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.map
    ((BundleDbar.localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx).symm.toLinearEquiv

private theorem closure_frameBasis_apply (a x : M.Carrier)
    (hx : x ∈ (BundleDbar.localTriv (r := r) E a).baseSet) (i : Fin r) :
    closure_frameBasis E a x hx i =
      (BundleDbar.localTriv (r := r) E a).symmL ℂ x (stdVec i) := by
  simp only [closure_frameBasis, Basis.map_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
  exact congrFun ((BundleDbar.localTriv (r := r) E a).symm_continuousLinearEquivAt_eq hx) _

private theorem closure_frameBasis_repr (a x : M.Carrier)
    (hx : x ∈ (BundleDbar.localTriv (r := r) E a).baseSet) (v : E x) (i : Fin r) :
    (closure_frameBasis E a x hx).repr v i =
      (BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ x v i := by
  simp only [closure_frameBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    EuclideanSpace.basisFun_repr]
  change ((BundleDbar.localTriv (r := r) E a).continuousLinearEquivAt ℂ x hx v) i = _
  exact congrArg (fun f : E x → ComplexVector r => f v i)
    ((BundleDbar.localTriv (r := r) E a).coe_continuousLinearEquivAt_eq (R := ℂ) hx)

theorem closure_sectionNormSq_inChart (k : BundleDbar.Metric E) (b : Section E)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ BundleDbar.localDomain (r := r) E a) :
    hermitianNormSq (k (chartInv a z)) (b (chartInv a z)) =
      (∑ i, ∑ j, star (sectionCoefficients (r := r) E b a z i) *
        BundleDbar.metricMatrix (r := r) E k a z i j * sectionCoefficients (r := r) E b a z j).re := by
  let B := closure_frameBasis E a (chartInv a z) hz.2
  have he := closure_hermitian_coordinates (k (chartInv a z)) B
    (b (chartInv a z)) (b (chartInv a z))
  simpa only [hermitianNormSq, sectionCoefficients, B, closure_frameBasis_apply,
    closure_frameBasis_repr, BundleDbar.metricMatrix] using (congrArg Complex.re he).symm

theorem closure_localDomain_isOpen (a : M.Carrier) :
    IsOpen (BundleDbar.localDomain (r := r) E a) :=
  (continuousOn_extChartAt_symm (I := ComplexModel 1) a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (BundleDbar.localTriv (r := r) E a).open_baseSet

theorem closure_sectionNormSq_chart_continuousOn (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (b : Section E) {Ω : Set M.Carrier}
    (hb : HolomorphicSectionOn (r := r) E b Ω) (a : M.Carrier) :
    ContinuousOn (fun z => hermitianNormSq (k (chartInv a z)) (b (chartInv a z)))
      (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' Ω) := by
  have hcoord (i : Fin r) : ContinuousOn (fun z => sectionCoefficients (r := r) E b a z i)
      (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' Ω) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r => ℂ) i).continuous.comp_continuousOn (hb a).continuousOn
  have hQ : ContinuousOn (fun z =>
      (∑ i, ∑ j, star (sectionCoefficients (r := r) E b a z i) *
        BundleDbar.metricMatrix (r := r) E k a z i j * sectionCoefficients (r := r) E b a z j).re)
      (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' Ω) := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((hcoord i).star.mul ((hk a i j).continuousOn.mono inter_subset_left)).mul (hcoord j))
  apply hQ.congr
  intro z hz
  exact closure_sectionNormSq_inChart E k b a z hz.1

/-- Smooth original metric and local holomorphic coefficients give actual continuity of the norm. -/
theorem closure_sectionNormSq_continuousOn (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (b : Section E) {Ω : Set M.Carrier}
    (hΩ : IsOpen Ω) (hb : HolomorphicSectionOn (r := r) E b Ω) :
    ContinuousOn (fun x => hermitianNormSq (k x) (b x)) Ω := by
  intro x hx
  have hleft : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel 1) x).left_inv (mem_extChartAt_source x)
  have hD : IsOpen (BundleDbar.localDomain (r := r) E x ∩ (chartInv x) ⁻¹' Ω) :=
    ((continuousOn_extChartAt_symm (I := ComplexModel 1) x).mono inter_subset_left).isOpen_inter_preimage
      (closure_localDomain_isOpen E x) hΩ
  have hv : chartPt x x ∈ BundleDbar.localDomain (r := r) E x ∩ (chartInv x) ⁻¹' Ω := by
    refine ⟨⟨mem_extChartAt_target x, ?_⟩, ?_⟩
    · change chartInv x (chartPt x x) ∈ (BundleDbar.localTriv (r := r) E x).baseSet
      rw [hleft]
      exact mem_baseSet_trivializationAt (ComplexVector r) E x
    · simpa only [mem_preimage, hleft] using hx
  have hc := ((closure_sectionNormSq_chart_continuousOn E k hk b hb x).continuousAt (hD.mem_nhds hv)).comp
    (continuousAt_extChartAt (I := ComplexModel 1) x)
  have he : (fun y => hermitianNormSq (k (chartInv x (chartPt x y))) (b (chartInv x (chartPt x y)))) =ᶠ[𝓝 x]
      (fun y => hermitianNormSq (k y) (b y)) := by
    filter_upwards [(isOpen_extChartAt_source (I := ComplexModel 1) x).mem_nhds (mem_extChartAt_source x)] with y hy
    rw [show chartInv x (chartPt x y) = y from (extChartAt (ComplexModel 1) x).left_inv hy]
  exact (hc.congr_of_eventuallyEq he.symm).continuousWithinAt

end Yau.Proofs.D03Aux
