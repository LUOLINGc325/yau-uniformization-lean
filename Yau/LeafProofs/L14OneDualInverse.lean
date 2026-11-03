import Yau.LeafProofs.L14InverseDual
import Yau.LeafProofs.L14TwoAdjointModel

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def oneWeightedDualInverse (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (w : ComplexVector n → (Fin n × Fin r) → ℂ)
    (z : ComplexVector n) (j : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => (Real.exp (φ (chartInv a z)) : ℂ)*
    ∑ c,(chartOneMetricMatrix (r := r) E g h a z)⁻¹ (j,α) c*w z c)

theorem oneWeightedDualInverse_sub (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (w v : ComplexVector n → (Fin n × Fin r) → ℂ)
    (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    oneWeightedDualInverse (r := r) E g h φ a (fun z c => w z c-v z c) z j α =
      oneWeightedDualInverse (r := r) E g h φ a w z j α-oneWeightedDualInverse (r := r) E g h φ a v z j α := by
  simp only [oneWeightedDualInverse,WithLp.ofLp_toLp,mul_sub,Finset.sum_sub_distrib]

theorem oneWeightedDualInverse_tsupport (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (w : ComplexVector n → (Fin n × Fin r) → ℂ)
    {K : Set (ComplexVector n)} (hK : IsClosed K) (hsw : ∀ c,tsupport (fun z => w z c) ⊆ K) :
    tsupport (oneWeightedDualInverse (r := r) E g h φ a w) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hn
  have hw (c : Fin n × Fin r) : w z c = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => w y c) (fun ht => hn (hsw c ht))
  apply hz
  funext j
  apply PiLp.ext
  intro α
  simp only [oneWeightedDualInverse,WithLp.ofLp_toLp,hw,mul_zero,Finset.sum_const_zero,Pi.zero_apply,PiLp.zero_apply]

theorem oneWeightedDualInverse_chartOneDual (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (j : Fin n) (α : Fin r) :
    oneWeightedDualInverse (r := r) E g h φ a (fun z c => chartOneDual (r := r) E g h φ a F z c.1 c.2) z j α = F z j α := by
  have he := matrix_exp_dual_inverse_cancel (chartOneMetricMatrix (r := r) E g h a z)
    (chartOneMetricMatrix_posDef E g h a z hz) (φ (chartInv a z)) (fun c : Fin n × Fin r => F z c.1 c.2) (j,α)
  change (Real.exp (φ (chartInv a z)) : ℂ)*∑ c,(chartOneMetricMatrix (r := r) E g h a z)⁻¹ (j,α) c *
    chartOneDual (r := r) E g h φ a F z c.1 c.2 = _
  simp only [chartOneDual_eq_weighted_matrix,Matrix.mulVec,dotProduct] at he ⊢
  convert he using 1 <;> congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_comm (Real.exp (-φ (chartInv a z)) : ℂ)]

theorem oneWeightedDualInverse_coefficient_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row c : Fin n × Fin r) :
    ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ)*
      (chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ row c) (localDomain (r := r) E a) := by
  have he : ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ)) (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn ((hφ a).mono Set.inter_subset_left))
  exact he.mul (L18Aux.contDiffOn_matrix_inv (chartOneMetricMatrix_contDiffOn E g h hh a)
    (fun z hz => ((chartOneMetricMatrix_posDef E g.form h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero) row c)

theorem oneWeightedDualInverse_l2_errors (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (w : ℕ → ComplexVector n → (Fin n × Fin r) → ℂ) (v : ComplexVector n → (Fin n × Fin r) → ℂ)
    (hsw : ∀ m c,tsupport (fun z => w m z c) ⊆ K) (hsv : ∀ c,tsupport (fun z => v z c) ⊆ K)
    (he : ∀ m c,MemLp (fun z => w m z c-v z c) 2 (lebesgueC n))
    (ht : ∀ c,Tendsto (fun m => ∫ z,‖w m z c-v z c‖^2 ∂lebesgueC n) atTop (𝓝 0)) (row : Fin n × Fin r) :
    (∀ m,MemLp (fun z => oneWeightedDualInverse (r := r) E g.form h φ a (w m) z row.1 row.2-
      oneWeightedDualInverse (r := r) E g.form h φ a v z row.1 row.2) 2 (lebesgueC n)) ∧
    Tendsto (fun m => ∫ z,‖oneWeightedDualInverse (r := r) E g.form h φ a (w m) z row.1 row.2-
      oneWeightedDualInverse (r := r) E g.form h φ a v z row.1 row.2‖^2 ∂lebesgueC n) atTop (𝓝 0) := by
  have hs (m : ℕ) (c : Fin n × Fin r) : tsupport (fun z => w m z c-v z c) ⊆ K :=
    tsupport_sub_subset_closed hK.isClosed (hsw m c) (hsv c)
  have ha := integral_sq_tendsto_zero_compact_local_matrix (localDomain_isOpen E a) hK hKO
    (fun m z c => w m z c-v z c) he hs ht _ (oneWeightedDualInverse_coefficient_contDiffOn E g h hh φ hφ a) row
  have hval (m : ℕ) (z : ComplexVector n) :
      (∑ c,(Real.exp (φ (chartInv a z)) : ℂ)*(chartOneMetricMatrix (r := r) E g.form h a z)⁻¹ row c*(w m z c-v z c)) =
      oneWeightedDualInverse (r := r) E g.form h φ a (w m) z row.1 row.2-
        oneWeightedDualInverse (r := r) E g.form h φ a v z row.1 row.2 := by
    simp only [oneWeightedDualInverse,WithLp.ofLp_toLp,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  simpa only [hval] using ha

end Yau.LeafProofs.L14Aux
