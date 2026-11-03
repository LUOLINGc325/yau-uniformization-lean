import Yau.LeafProofs.L14LocalMultipliers
import Yau.LeafProofs.L14BundleFriedrichsModels

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open MeasureTheory Bundle Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem tsupport_sub_subset_closed {X F : Type*} [TopologicalSpace X] [AddGroup F]
    {f g : X → F} {K : Set X} (hK : IsClosed K) (hf : tsupport f ⊆ K) (hg : tsupport g ⊆ K) :
    tsupport (fun x => f x - g x) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  apply hx
  change f x - g x = 0
  rw [image_eq_zero_of_notMem_tsupport (f := f) (fun hs => hn (hf hs)),
    image_eq_zero_of_notMem_tsupport (f := g) (fun hs => hn (hg hs)), sub_self]

theorem matrix_exp_dual_inverse_cancel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (t : ℝ) (v : ι → ℂ) (α : ι) :
    (Real.exp t : ℂ) * ∑ β, H⁻¹ α β * ((∑ γ, H β γ * v γ) * (Real.exp (-t) : ℂ)) = v α := by
  have hinv : H⁻¹ *ᵥ (H *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have he : (∑ β, H⁻¹ α β * ((∑ γ, H β γ * v γ) * (Real.exp (-t) : ℂ))) =
      (H⁻¹ *ᵥ (H *ᵥ v)) α * (Real.exp (-t) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  rw [he, hinv]
  have hc : (Real.exp t : ℂ) * (Real.exp (-t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = ((Real.exp t : ℂ) * (Real.exp (-t) : ℂ)) * v α := by ring
    _ = _ := by rw [hc, one_mul]

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def weightedModelDualInverse (h : Metric E) (φ : M.Carrier → ℝ) (a : M.Carrier)
    (w : ComplexVector n → Fin r → ℂ) (z : ComplexVector n) (α : Fin r) : ℂ :=
  (Real.exp (φ (chartInv a z)) : ℂ) * ∑ β, (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β * w z β

theorem weightedModelDualInverse_sub (h : Metric E) (φ : M.Carrier → ℝ) (a : M.Carrier)
    (w v : ComplexVector n → Fin r → ℂ) (z : ComplexVector n) (α : Fin r) :
    weightedModelDualInverse E h φ a (fun z β => w z β - v z β) z α =
      weightedModelDualInverse E h φ a w z α - weightedModelDualInverse E h φ a v z α := by
  simp only [weightedModelDualInverse, mul_sub, Finset.sum_sub_distrib]

theorem weightedModelDualInverse_tsupport_subset (h : Metric E) (φ : M.Carrier → ℝ) (a : M.Carrier)
    (w : ComplexVector n → Fin r → ℂ) {K : Set (ComplexVector n)} (hK : IsClosed K)
    (hsw : ∀ β, tsupport (fun z => w z β) ⊆ K) (α : Fin r) :
    tsupport (fun z => weightedModelDualInverse E h φ a w z α) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hn
  have hw (β : Fin r) : w z β = 0 := image_eq_zero_of_notMem_tsupport
    (f := fun y => w y β) (fun hs => hn (hsw β hs))
  apply hz
  simp only [weightedModelDualInverse, hw, mul_zero, Finset.sum_const_zero]

theorem weightedModelDualInverse_bundleOutput (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) (z : ComplexVector n) (α : Fin r) :
    weightedModelDualInverse E h φ a (fun z β => bundleModelSystemOutput E g h φ a F z (.inl β)) z α =
      chartDbarAdjoint (r := r) E g h φ a F z α := by
  by_cases hz : z ∈ localDomain (r := r) E a
  · exact matrix_exp_dual_inverse_cancel _ (metricMatrix_posDef E h a z hz)
      (φ (chartInv a z)) (fun β => chartDbarAdjoint (r := r) E g h φ a F z β) α
  · have hn : z ∉ tsupport F := fun hs => hz (hsF hs)
    have hd : chartDbarAdjoint (r := r) E g h φ a F z = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hn (tsupport_chartDbarAdjoint_subset E g h φ a F hs))
    simp only [weightedModelDualInverse, bundleModelSystemOutput, hd, PiLp.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_mul]

theorem weightedModelDualInverse_coefficient_contDiffOn (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ) *
      (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β) (localDomain (r := r) E a) := by
  have he : ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ)) (localDomain (r := r) E a) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn ((hφ a).mono Set.inter_subset_left)))
  exact he.mul (L18Aux.contDiffOn_matrix_inv (hh a) (fun z hz =>
    ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero) α β)

/-- Recovering the actual adjoint coefficient from its weighted dual preserves
strong model L² graph convergence on a fixed chart compact. -/
theorem chartDbarAdjoint_graph_tendsto_of_weighted_dual
    (g : HermitianField M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a)
    (F : ℕ → ComplexVector n → Fin n → ComplexVector r) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (w : ComplexVector n → Fin r → ℂ) (hsw : ∀ β, tsupport (fun z => w z β) ⊆ K)
    (he : ∀ j β, MemLp (fun z => bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β) 2 (lebesgueC n))
    (ht : ∀ β, Tendsto (fun j => ∫ z, ‖bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β‖ ^ 2
      ∂lebesgueC n) atTop (𝓝 0)) (α : Fin r) :
    (∀ j, MemLp (fun z => chartDbarAdjoint (r := r) E g h φ a (F j) z α - weightedModelDualInverse E h φ a w z α)
      2 (lebesgueC n)) ∧
      Tendsto (fun j => ∫ z, ‖chartDbarAdjoint (r := r) E g h φ a (F j) z α - weightedModelDualInverse E h φ a w z α‖ ^ 2
        ∂lebesgueC n) atTop (𝓝 0) := by
  have hs (j : ℕ) (β : Fin r) :
      tsupport (fun z => bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β) ⊆ K :=
    tsupport_sub_subset_closed hK.isClosed
      ((bundleModelSystemOutput_tsupport_subset E g h φ a (F j) (.inl β)).trans (hsF j)) (hsw β)
  have hlim := integral_sq_tendsto_zero_compact_local_matrix (localDomain_isOpen E a) hK hKO
    (fun j z β => bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β) he hs ht
    (fun α β z => (Real.exp (φ (chartInv a z)) : ℂ) * (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β)
    (weightedModelDualInverse_coefficient_contDiffOn E h hh φ hφ a) α
  have heq (j : ℕ) (z : ComplexVector n) :
      (∑ β, ((Real.exp (φ (chartInv a z)) : ℂ) * (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β) *
        (bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β)) =
      chartDbarAdjoint (r := r) E g h φ a (F j) z α - weightedModelDualInverse E h φ a w z α := by
    rw [show (∑ β, ((Real.exp (φ (chartInv a z)) : ℂ) * (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β) *
        (bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β)) =
        weightedModelDualInverse E h φ a
          (fun z β => bundleModelSystemOutput E g h φ a (F j) z (.inl β) - w z β) z α by
      simp only [weightedModelDualInverse, Finset.mul_sum, mul_assoc]]
    rw [weightedModelDualInverse_sub, weightedModelDualInverse_bundleOutput E g h φ a (F j) ((hsF j).trans hKO)]
  simpa only [heq] using hlim

end Yau.LeafProofs.L14Aux
