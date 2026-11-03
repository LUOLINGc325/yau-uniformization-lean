import Yau.LeafProofs.L21GraphDifferential

/-! The original Nijenhuis hypothesis implies the actual matrix
Maurer--Cartan equations for the Cayley graph coefficients. -/

open Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def MatrixSmoothOn (A : X n → Matrix (Fin n) (Fin n) ℂ) (O : Set (X n)) : Prop :=
  ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O

def CommutesOn (A : X n → Matrix (Fin n) (Fin n) ℂ) (O : Set (X n)) : Prop :=
  ∀ x ∈ O, ∀ i j k,
    dbarA A i (fun y => A y j k) x = dbarA A j (fun y => A y i k) x

/-- No commutation premise is added: the matrix equations are deduced from
the frozen constant-vector Nijenhuis definition. -/
theorem cayley_graph_commutes
    {O : Set (X n)} (hO : IsOpen O)
    {J : X n → X n →L[ℝ] X n} (hJ : ContDiffOn ℝ ∞ J O)
    (hJ2 : ∀ x ∈ O, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ O, ∀ v w, Yau.LeafCandidates.nijenhuis J x v w = 0)
    (hi : ∀ x ∈ O, (J x + stdComplex n).IsInvertible) :
    CommutesOn (graphMatrix (fun y => cayleyMap (J y))) O := by
  intro x hx i j k
  let C : X n → X n →L[ℝ] X n := fun y => cayleyMap (J y)
  have hJx : ContDiffAt ℝ ∞ J x := hJ.contDiffAt (hO.mem_nhds hx)
  have hdJ : DifferentiableAt ℝ J x := hJx.differentiableAt (by simp)
  have hC : DifferentiableAt ℝ C x :=
    (contDiffAt_cayleyMap hJx (hi x hx)).differentiableAt (by simp)
  have hS (v : X n) : (fun y => J y (graphR C v y)) =ᶠ[𝓝 x] graphS C v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact structure_graphReal (J y) (hi y hy) v
  have ht := integrable_graph_bracket hdJ
    (differentiableAt_graphR hC (Yau.stdVec i))
    (differentiableAt_graphR hC (Yau.stdVec j))
    (hJ2 x hx) (hN x hx) (hS (Yau.stdVec i)) (hS (Yau.stdVec j))
  have hs := graph_bracket_standard_part
    (fderiv_graphS hC (Yau.stdVec i)) (fderiv_graphS hC (Yau.stdVec j))
  have hz := (graph_bracket_zero (hi x hx) ht hs).1
  have he :
      fderiv ℝ C x (graphR C (Yau.stdVec i) x) (Yau.stdVec j) +
          Complex.I • fderiv ℝ C x (graphS C (Yau.stdVec i) x) (Yau.stdVec j) =
        fderiv ℝ C x (graphR C (Yau.stdVec j) x) (Yau.stdVec i) +
          Complex.I • fderiv ℝ C x (graphS C (Yau.stdVec j) x) (Yau.stdVec i) := by
    apply sub_eq_zero.mp
    rw [graph_coefficient_bracket hC, hz, smul_zero]
  change dbarA (graphMatrix C) i (fun y => (C y (Yau.stdVec j)) k) x =
    dbarA (graphMatrix C) j (fun y => (C y (Yau.stdVec i)) k) x
  rw [dbarA_graph_component (hC.clm_apply (differentiableAt_const (Yau.stdVec j))),
    dbarA_graph_component (hC.clm_apply (differentiableAt_const (Yau.stdVec i))),
    fderiv_structure_apply_const hC, fderiv_structure_apply_const hC]
  exact congrArg (fun u : X n => u k) he

theorem cayley_graph_matrix_smooth
    {O : Set (X n)} (hO : IsOpen O)
    {J : X n → X n →L[ℝ] X n} (hJ : ContDiffOn ℝ ∞ J O)
    (hi : ∀ x ∈ O, (J x + stdComplex n).IsInvertible) :
    MatrixSmoothOn (graphMatrix (fun y => cayleyMap (J y))) O := by
  intro i k x hx
  have hC := contDiffAt_cayleyMap (hJ.contDiffAt (hO.mem_nhds hx)) (hi x hx)
  exact (((EuclideanSpace.proj k).restrictScalars ℝ).contDiff.comp_contDiffAt x
    (hC.clm_apply contDiffAt_const)).contDiffWithinAt

end Yau.LeafProofs.L21Aux
