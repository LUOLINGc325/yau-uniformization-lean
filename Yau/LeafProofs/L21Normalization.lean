import Yau.LeafProofs.L21AffineNormalization
import Yau.LeafProofs.L21FiniteJetScaling
import Yau.LeafProofs.L21Integrability
import Yau.LeafProofs.L21GraphIntertwining

/-! Actual normalization to an arbitrarily small finite matrix jet. -/

open Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def JetBound (q : ℕ) (b : ℝ)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (O : Set (X n)) : Prop :=
  ∀ k ≤ q, ∀ x ∈ O, ∀ i j,
    ‖iteratedFDeriv ℝ k (fun y => A y i j) x‖ ≤ b

def matrixEntry (i j : Fin n) : (Fin n → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))

theorem matrixEntry_norm_le (i j : Fin n) : ‖matrixEntry i j‖ ≤ 1 := by
  apply (matrixEntry i j).opNorm_le_bound (by norm_num)
  intro A
  change ‖A i j‖ ≤ 1 * ‖A‖
  rw [one_mul]
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem norm_iteratedFDeriv_matrixEntry_le
    {A : X n → Fin n → Fin n → ℂ} {x : X n}
    (hA : ContDiffAt ℝ ∞ A x) (k : ℕ) (i j : Fin n) :
    ‖iteratedFDeriv ℝ k (fun y => A y i j) x‖ ≤ ‖iteratedFDeriv ℝ k A x‖ := by
  exact ((matrixEntry i j).norm_iteratedFDeriv_comp_left (n := k) hA (by simp)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (matrixEntry_norm_le i j))

theorem double_stdComplex_isInvertible (n : ℕ) :
    (stdComplex n + stdComplex n).IsInvertible := by
  have hd : (dilationEquiv (E := X n) 2 (by norm_num) : X n →L[ℝ] X n).IsInvertible :=
    ContinuousLinearMap.isInvertible_equiv
  have he := (stdComplex_isInvertible n).comp hd
  rw [dilationEquiv_coe] at he
  have hh : stdComplex n + stdComplex n =
      (stdComplex n).comp ((2 : ℝ) • ContinuousLinearMap.id ℝ (X n)) := by
    ext1 v
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, two_smul, map_add]
  rw [hh]
  exact he

theorem contDiffAt_graphMatrix
    {J : X n → X n →L[ℝ] X n} {x : X n}
    (hJ : ContDiffAt ℝ ∞ J x) (hi : (J x + stdComplex n).IsInvertible) :
    ContDiffAt ℝ ∞ (fun y i j => graphMatrix (fun y => cayleyMap (J y)) y i j) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact ((EuclideanSpace.proj j).restrictScalars ℝ).contDiff.comp_contDiffAt x
    ((contDiffAt_cayleyMap hJ hi).clm_apply contDiffAt_const)

/-- Dilation of an already linearly normalized germ. Both integrability and
the finite jet estimates concern the actual scaled matrix coefficients. -/
theorem normalized_small_graph
    {O : Set (X n)} (hO : IsOpen O) (hzero : (0 : X n) ∈ O)
    {J : X n → X n →L[ℝ] X n} (hJ : ContDiffOn ℝ ∞ J O)
    (hJ0 : J 0 = stdComplex n)
    (hJ2 : ∀ x ∈ O, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ O, ∀ v w, Yau.LeafCandidates.nijenhuis J x v w = 0)
    (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      (∀ z ∈ Metric.closedBall (0 : X n) 2, r • z ∈ O) ∧
      (∀ z ∈ Metric.ball (0 : X n) 2, (J (r • z) + stdComplex n).IsInvertible) ∧
      MatrixSmoothOn (graphMatrix (fun y => cayleyMap (J (r • y)))) (Metric.ball 0 2) ∧
      CommutesOn (graphMatrix (fun y => cayleyMap (J (r • y)))) (Metric.ball 0 2) ∧
      JetBound q δ (graphMatrix (fun y => cayleyMap (J (r • y)))) (Metric.ball 0 2) := by
  have hJat : ContDiffAt ℝ ∞ J 0 := hJ.contDiffAt (hO.mem_nhds hzero)
  have hi0 : (J 0 + stdComplex n).IsInvertible := by
    rw [hJ0]
    exact double_stdComplex_isInvertible n
  have hnear : ∀ᶠ y in 𝓝 (0 : X n), y ∈ O ∧ (J y + stdComplex n).IsInvertible :=
    (show ∀ᶠ y in 𝓝 (0 : X n), y ∈ O from hO.mem_nhds hzero).and
      ((hJat.continuousAt.add continuousAt_const).eventually hi0.eventually_nhds)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let A : X n → Fin n → Fin n → ℂ := fun y i j => graphMatrix (fun y => cayleyMap (J y)) y i j
  have hA : ContDiffAt ℝ ∞ A 0 := contDiffAt_graphMatrix hJat hi0
  have hA0 : A 0 = 0 := by
    ext i j
    simp [A, graphMatrix, cayleyMap, hJ0]
  obtain ⟨r, hr, hr1, hra, hjet⟩ :=
    exists_dilate_finite_jet_small_le hA hA0 q hδ (show 0 < a / 4 by positivity)
  have hgood (z : X n) (hz : z ∈ Metric.closedBall (0 : X n) 2) :
      r • z ∈ O ∧ (J (r • z) + stdComplex n).IsInvertible := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hzn : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    nlinarith
  have hJr : ContDiffOn ℝ ∞ (fun y => J (r • y)) (Metric.ball (0 : X n) 2) := by
    intro z hz
    exact ((hJ.contDiffAt (hO.mem_nhds (hgood z (Metric.ball_subset_closedBall hz)).1)).comp z
      (contDiff_id.const_smul r).contDiffAt).contDiffWithinAt
  have hir (z : X n) (hz : z ∈ Metric.ball (0 : X n) 2) :
      (J (r • z) + stdComplex n).IsInvertible := (hgood z (Metric.ball_subset_closedBall hz)).2
  have hNr (z : X n) (hz : z ∈ Metric.ball (0 : X n) 2) (v w : X n) :
      Yau.LeafCandidates.nijenhuis (fun y => J (r • y)) z v w = 0 := by
    have hd := (hJ.contDiffAt (hO.mem_nhds (hgood z (Metric.ball_subset_closedBall hz)).1)).differentiableAt
      (by simp)
    have hd' : DifferentiableAt ℝ J
        (rescalePoint 0 (ContinuousLinearEquiv.refl ℝ (X n)) r z) := by
      simpa [rescalePoint] using hd
    have he := nijenhuis_rescaleStructure (0 : X n) (ContinuousLinearEquiv.refl ℝ (X n)) r hd' v w
    have heq : rescaleStructure 0 (ContinuousLinearEquiv.refl ℝ (X n)) r J =
        (fun y => J (r • y)) := by
      funext y
      ext1 u
      simp [rescaleStructure_apply, rescalePoint]
    rw [heq] at he
    simpa [rescalePoint, hN _ (hgood z (Metric.ball_subset_closedBall hz)).1] using he
  refine ⟨r, hr, hr1, fun z hz => (hgood z hz).1, hir,
    cayley_graph_matrix_smooth Metric.isOpen_ball hJr hir,
    cayley_graph_commutes Metric.isOpen_ball hJr
      (fun z hz => hJ2 _ (hgood z (Metric.ball_subset_closedBall hz)).1) hNr hir, ?_⟩
  intro k hk z hz i j
  exact (norm_iteratedFDeriv_matrixEntry_le
    (contDiffAt_graphMatrix (hJr.contDiffAt (Metric.isOpen_ball.mem_nhds hz)) (hir z hz)) k i j).trans
      (hjet k hk z (Metric.ball_subset_closedBall hz))

/-- The complete geometric normalization uses only the original input
hypotheses and a caller-selected finite tolerance. -/
theorem exists_normalized_small_graph
    {O : Set (X n)} (hO : IsOpen O)
    {J : X n → X n →L[ℝ] X n} (hJ : ContDiffOn ℝ ∞ J O)
    (hJ2 : ∀ x ∈ O, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ O, ∀ v w, Yau.LeafCandidates.nijenhuis J x v w = 0)
    (p : X n) (hp : p ∈ O) (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : X n ≃L[ℝ] X n) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      rescaleStructure p S r J 0 = stdComplex n ∧
      (∀ z ∈ Metric.closedBall (0 : X n) 2, rescalePoint p S r z ∈ O) ∧
      (∀ z ∈ Metric.ball (0 : X n) 2,
        (rescaleStructure p S r J z + stdComplex n).IsInvertible) ∧
      MatrixSmoothOn (graphMatrix (fun y => cayleyMap (rescaleStructure p S r J y)))
        (Metric.ball 0 2) ∧
      CommutesOn (graphMatrix (fun y => cayleyMap (rescaleStructure p S r J y)))
        (Metric.ball 0 2) ∧
      JetBound q δ (graphMatrix (fun y => cayleyMap (rescaleStructure p S r J y)))
        (Metric.ball 0 2) := by
  obtain ⟨S, hS⟩ := exists_linear_normalization n (J p) (hJ2 p hp)
  let O₁ := rescalePoint p S 1 ⁻¹' O
  let J₁ := rescaleStructure p S 1 J
  have hO₁ : IsOpen O₁ := hO.preimage (contDiff_rescalePoint p S 1).continuous
  have hz : (0 : X n) ∈ O₁ := by simpa [O₁, rescalePoint] using hp
  have hJ₁ : ContDiffOn ℝ ∞ J₁ O₁ := by
    intro z hz
    exact (contDiffAt_rescaleStructure p S 1 (hJ.contDiffAt (hO.mem_nhds hz))).contDiffWithinAt
  have hJ₁0 : J₁ 0 = stdComplex n := by
    ext1 v
    exact rescaleStructure_at_zero p S 1 J hS v
  have hJ₁2 (z : X n) (hz : z ∈ O₁) (v : X n) : J₁ z (J₁ z v) = -v :=
    rescaleStructure_square p S 1 J z (hJ2 _ hz) v
  have hN₁ (z : X n) (hz : z ∈ O₁) (v w : X n) :
      Yau.LeafCandidates.nijenhuis J₁ z v w = 0 := by
    have he := nijenhuis_rescaleStructure p S 1
      ((hJ.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) v w
    simpa only [hN _ hz, map_zero, smul_zero] using he
  obtain ⟨r, hr, hr1, hsource, hinv, hsmooth, hcomm, hjet⟩ :=
    normalized_small_graph hO₁ hz hJ₁ hJ₁0 hJ₁2 hN₁ q hδ
  have heq (z : X n) : J₁ (r • z) = rescaleStructure p S r J z := by
    ext1 v
    simp only [J₁, rescaleStructure_apply, rescalePoint, map_smul, one_smul]
  refine ⟨S, r, hr, hr1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext1 v
    exact rescaleStructure_at_zero p S r J hS v
  · intro z hz
    simpa only [O₁, Set.mem_preimage, rescalePoint, map_smul, one_smul] using hsource z hz
  · simpa only [heq] using hinv
  · simpa only [heq] using hsmooth
  · simpa only [heq] using hcomm
  · simpa only [heq] using hjet

end Yau.LeafProofs.L21Aux
