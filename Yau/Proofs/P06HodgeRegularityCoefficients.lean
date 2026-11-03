import Yau.Proofs.P06HodgeRegularityCoordinates
import Yau.Proofs.P06HodgeRegularityScalarSystem
import Yau.LeafProofs.L03HodgeCoercivity

/-! The scalar inverse metric and forward lower-order matrices of the
actual Hodge operator. Compact ellipticity is uniform before choosing data. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def hodgeRegularityQ (g : HermitianField M) (x : M.Carrier)
    (i j : RIdx n) (z : ComplexVector n) : ℝ := (realMetricFn g x z)⁻¹ i j

def hodgeRegularityBeta {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (r c : α) (i : RIdx n) (z : ComplexVector n) : ℝ :=
  hodgeRegularityE1 g x b r c i z +
    if r = c then ∑ j, regularityDirection (realModelBasis n j) (hodgeRegularityQ g x j i) z else 0

theorem hodgeRegularityQ_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (hodgeRegularityQ g.form x i j) (chartTarget x) :=
  L18Aux.realMetricFn_inverse_contDiffOn g x i j

theorem hodgeRegularityQ_symm (g : HermitianField M) (x : M.Carrier)
    (i j : RIdx n) (z : ComplexVector n) :
    hodgeRegularityQ g x i j z = hodgeRegularityQ g x j i z :=
  (realMetricFn_inv_isSymm g x z).apply j i

theorem hodgeRegularityBeta_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (r c : α) (i : RIdx n) :
    ContDiffOn ℝ ∞ (hodgeRegularityBeta g.form x b r c i) (chartTarget x) := by
  unfold hodgeRegularityBeta
  apply (hodgeRegularityE1_contDiffOn g x b r c i).add
  by_cases hrc : r = c
  · simp only [hrc, ite_true]
    exact ContDiffOn.sum fun j _ =>
      (((hodgeRegularityQ_contDiffOn g x j i).fderiv_of_isOpen
        (isOpen_extChartAt_target (I := ComplexModel n) x) (m := ∞) (by simp)).clm_apply contDiffOn_const)
  · simpa only [hrc, ite_false] using (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : ComplexVector n => (0 : ℝ)) (chartTarget x))

/-- Actual inverse metric ellipticity on an arbitrary prescribed compact
chart buffer, independently of the section and its operator source. -/
theorem hodgeRegularityQ_uniform_coercive
    (g : SmoothMetric M) (x : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKO : K ⊆ chartTarget x) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ ξ : RIdx n → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, hodgeRegularityQ g.form x i j z * ξ j * ξ i := by
  classical
  let T : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ := fun z => (realMetricFn g.form x z)⁻¹
  have hT (i j : RIdx n) : ContDiffOn ℝ ∞ (fun z => T z i j) (chartTarget x) :=
    hodgeRegularityQ_contDiffOn g x i j
  have hpos (z : ComplexVector n) (hz : z ∈ chartTarget x) : (T z).PosDef :=
    (realMetricFn_posDef_of_mem_target g.form x hz).inv
  obtain ⟨lam, hlam, hb⟩ := uniform_matrix_coercivity_on_compact T (chartTarget x) hT hpos hK hKO
  refine ⟨lam, hlam, fun z hz ξ => (hb z hz ξ).trans_eq ?_⟩
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm (ξ i) (T z i j * ξ j)

theorem hodgeRegularityQ_finite_uniform_coercive {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKO : K ⊆ chartTarget x) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ ξ : RIdx n × α → ℝ,
      lam * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ c, ∑ i, ∑ j,
        regularityScalarSystemA (hodgeRegularityQ g.form x) r c i j z * ξ (j,c) * ξ (i,r) := by
  obtain ⟨lam, hlam, hb⟩ := hodgeRegularityQ_uniform_coercive g x hK hKO
  exact ⟨lam, hlam, fun z hz ξ => regularityScalarSystemA_coercive _ z lam (hb z hz) ξ⟩

end Yau.NodeProofs.P06Aux
