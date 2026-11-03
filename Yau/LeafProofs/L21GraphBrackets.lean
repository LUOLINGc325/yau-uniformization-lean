import Yau.LeafProofs.L21CayleyGraph

/-! Real and imaginary parts of the graph-field commutator. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}
open Yau.LeafCandidates

theorem bracket_congr_of_eventuallyEq
    {V W V' W' : X n → X n} {x : X n}
    (hV : V =ᶠ[𝓝 x] V') (hW : W =ᶠ[𝓝 x] W') :
    bracket V W x = bracket V' W' x := by
  simp only [bracket, hV.fderiv_eq, hW.fderiv_eq, hV.eq_of_nhds, hW.eq_of_nhds]

/-- The original Nijenhuis condition forces the bracket of two graph fields
to remain in the same eigenspace. This formulation uses real fields only. -/
theorem integrable_graph_bracket
    {J : X n → X n →L[ℝ] X n} {R S V W : X n → X n} {x : X n}
    (hJ : DifferentiableAt ℝ J x)
    (hR : DifferentiableAt ℝ R x) (hV : DifferentiableAt ℝ V x)
    (hJ2 : ∀ v, J x (J x v) = -v)
    (hN : ∀ v w, nijenhuis J x v w = 0)
    (hS : (fun y => J y (R y)) =ᶠ[𝓝 x] S)
    (hW : (fun y => J y (V y)) =ᶠ[𝓝 x] W) :
    J x (bracket R V x - bracket S W x) =
      bracket R W x + bracket S V x := by
  have he := nijenhuis_vector_fields hJ hR hV hJ2
  rw [hN] at he
  rw [bracket_congr_of_eventuallyEq hS hW,
    bracket_congr_of_eventuallyEq hS EventuallyEq.rfl,
    bracket_congr_of_eventuallyEq EventuallyEq.rfl hW] at he
  have hz : bracket S W x - J x (bracket S V x) -
      J x (bracket R W x) - bracket R V x = 0 := he.symm
  have hk : J x (bracket R W x + bracket S V x) =
      -(bracket R V x - bracket S W x) := by
    rw [map_add]
    apply sub_eq_zero.mp
    have hh := congrArg Neg.neg hz
    convert hh using 1 <;> abel
  have hh := congrArg (J x) hk
  simp only [hJ2, map_neg] at hh
  exact neg_injective hh.symm

/-- The constant standard `∂bar` part makes this commutator purely of type
`(1,0)` for the standard structure. -/
theorem graph_bracket_standard_part
    {R S V W : X n → X n} {x : X n}
    (hS : fderiv ℝ S x = -Complex.I • fderiv ℝ R x)
    (hW : fderiv ℝ W x = -Complex.I • fderiv ℝ V x) :
    bracket R W x + bracket S V x =
      -Complex.I • (bracket R V x - bracket S W x) := by
  simp only [bracket, hS, hW, _root_.smul_apply, smul_sub, smul_add,
    smul_smul, neg_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul,
    neg_smul, smul_neg]
  abel

/-- The two type conditions have zero intersection, using the actual
invertibility of `J + I`. -/
theorem graph_bracket_zero
    {J : X n →L[ℝ] X n} {H K : X n}
    (h : (J + stdComplex n).IsInvertible)
    (hJ : J H = K) (hI : K = -Complex.I • H) : H = 0 ∧ K = 0 := by
  have hH : H = 0 := h.injective (by
    change J H + Complex.I • H = J 0 + Complex.I • (0 : X n)
    rw [hJ, hI]
    simp)
  exact ⟨hH, by simp [hH] at hJ; exact hJ.symm⟩

end Yau.LeafProofs.L21Aux
