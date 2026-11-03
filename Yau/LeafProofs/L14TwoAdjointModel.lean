import Yau.LeafProofs.L14TwoLocalCoefficient

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal Kronecker
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
def twoCoefficientFlip (n r : ℕ) : TwoCoefficientIndex n r ≃ TwoCoefficientIndex n r where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv := by rintro ⟨⟨α,i⟩,j⟩; rfl
  right_inv := by rintro ⟨⟨α,i⟩,j⟩; rfl

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartTwoDual (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i j : Fin n) (α : Fin r) : ℂ :=
  (Real.exp (-φ (chartInv a z)) : ℂ) *
    (chartTwoMetricMatrix (r := r) E g h a z *ᵥ
      (fun p : TwoCoefficientIndex n r => F z p.1.2 p.2 p.1.1)) ((α,i),j)

def chartTwoDbarAdjoint (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (j : Fin n) : ComplexVector r :=
  WithLp.toLp 2 (fun α => -(Real.exp (φ (chartInv a z)) : ℂ) *
    ∑ c : Fin n × Fin r, (chartOneMetricMatrix (r := r) E g h a z)⁻¹ (j,α) c *
      ∑ i, wirt (fun w => chartTwoDual E g h φ a F w i c.1 c.2) z (stdVec i))

theorem chartOneDual_eq_weighted_matrix (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a F z j α =
      (Real.exp (-φ (chartInv a z)) : ℂ) *
        (chartOneMetricMatrix (r := r) E g h a z *ᵥ (fun c : Fin n × Fin r => F z c.1 c.2)) (j,α) := by
  simp only [chartOneDual, chartOneMetricMatrix, Matrix.kronecker_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem chartTwoDbarAdjoint_dual (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (j : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a (chartTwoDbarAdjoint E g h φ a F) z j α =
      -∑ i, wirt (fun w => chartTwoDual E g h φ a F w i j α) z (stdVec i) := by
  classical
  let A := chartOneMetricMatrix (r := r) E g h a z
  let D := fun c : Fin n × Fin r => ∑ i, wirt (fun w => chartTwoDual E g h φ a F w i c.1 c.2) z (stdVec i)
  let c : ℂ := Real.exp (φ (chartInv a z))
  let ρ : ℂ := Real.exp (-φ (chartInv a z))
  have hρc : ρ * c = 1 := by
    dsimp only [ρ,c]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hcancel : A *ᵥ (A⁻¹ *ᵥ D) = D := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((chartOneMetricMatrix_posDef E g h a z hz).isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hR : (fun d : Fin n × Fin r => chartTwoDbarAdjoint E g h φ a F z d.1 d.2) =
      (-c) • (A⁻¹ *ᵥ D) := by
    funext d
    rfl
  rw [chartOneDual_eq_weighted_matrix, hR, Matrix.mulVec_smul, hcancel]
  change ρ * ((-c) * D (j,α)) = -D (j,α)
  calc
    _ = -(ρ * c) * D (j,α) := by ring
    _ = _ := by rw [hρc, neg_one_mul]

theorem tsupport_chartTwoDual_subset (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (i j : Fin n) (α : Fin r) : tsupport (fun z => chartTwoDual E g h φ a F z i j α) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  have hF : F z = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hz
  simp only [chartTwoDual, hF, Pi.zero_apply, PiLp.zero_apply, Matrix.mulVec, dotProduct, mul_zero,
    Finset.sum_const_zero]

theorem chartTwoDual_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (i j : Fin n) (α : Fin r) :
    ContDiffOn ℝ ∞ (fun z => chartTwoDual E g.form h φ a F z i j α) (localDomain (r := r) E a) := by
  have he : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ)) (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (((hφ a).mono Set.inter_subset_left).neg))
  have hFc (p : TwoCoefficientIndex n r) : ContDiffOn ℝ ∞ (fun z => F z p.1.2 p.2 p.1.1)
      (localDomain (r := r) E a) :=
    ((contDiff_piLp 2).mp ((contDiff_pi.mp ((contDiff_pi.mp hF) p.1.2)) p.2) p.1.1).contDiffOn
  unfold chartTwoDual
  simp only [Matrix.mulVec, dotProduct]
  apply he.mul
  apply ContDiffOn.sum
  intro p _
  exact (chartTwoMetricMatrix_contDiffOn E g h hh a ((α,i),j) p).mul (hFc p)

theorem chartTwoDual_contDiff (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hsF : tsupport F ⊆ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    ContDiff ℝ ∞ (fun z => chartTwoDual E g.form h φ a F z i j α) :=
  contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen (r := r) E a) _
    (chartTwoDual_contDiffOn E g h hh φ hφ a F hF i j α)
    ((tsupport_chartTwoDual_subset E g.form h φ a F i j α).trans hsF)

theorem tsupport_chartTwoDbarAdjoint_subset (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r) :
    tsupport (chartTwoDbarAdjoint E g h φ a F) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro z hz
  by_contra hn
  have hd (i j : Fin n) (α : Fin r) : wirt (fun w => chartTwoDual E g h φ a F w i j α) z (stdVec i) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => wirt (fun w => chartTwoDual E g h φ a F w i j α) y (stdVec i))
      (fun hs => hn ((tsupport_wirt_subset _ _).trans (tsupport_chartTwoDual_subset E g h φ a F i j α) hs))
  apply hz
  funext j
  apply PiLp.ext
  intro α
  simp only [chartTwoDbarAdjoint, hd, mul_zero, Finset.sum_const_zero, Pi.zero_apply, PiLp.zero_apply]

theorem chartTwoDbarAdjoint_contDiff (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hsF : tsupport F ⊆ localDomain (r := r) E a) :
    ContDiff ℝ ∞ (chartTwoDbarAdjoint E g.form h φ a F) := by
  have hdet : ∀ z ∈ localDomain (r := r) E a, (chartOneMetricMatrix (r := r) E g.form h a z).det ≠ 0 :=
    fun z hz => ((chartOneMetricMatrix_posDef E g.form h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  have hInv (c d : Fin n × Fin r) :=
    L18Aux.contDiffOn_matrix_inv (chartOneMetricMatrix_contDiffOn (r := r) E g h hh a) hdet c d
  have he : ContDiffOn ℝ ∞ (fun z => -(Real.exp (φ (chartInv a z)) : ℂ)) (localDomain (r := r) E a) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn ((hφ a).mono Set.inter_subset_left))).neg
  have hD (i : Fin n) (c : Fin n × Fin r) : ContDiffOn ℝ ∞
      (fun z => wirt (fun w => chartTwoDual E g.form h φ a F w i c.1 c.2) z (stdVec i)) (localDomain (r := r) E a) :=
    wirt_contDiffOn (localDomain_isOpen (r := r) E a) _ (chartTwoDual_contDiffOn E g h hh φ hφ a F hF i c.1 c.2) (stdVec i)
  apply contDiff_pi.mpr
  intro j
  apply (contDiff_piLp 2).mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen (r := r) E a)
  · apply he.mul
    apply ContDiffOn.sum
    intro c _
    apply (hInv (j,α) c).mul
    exact ContDiffOn.sum (fun i _ => hD i c)
  · exact (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V j α) (by rfl)
      (chartTwoDbarAdjoint E g.form h φ a F)).trans ((tsupport_chartTwoDbarAdjoint_subset E g.form h φ a F).trans hsF)

theorem chartTwoMetricMatrix_flip (g : HermitianField M) (h : Metric E) (a : M.Carrier)
    (z : ComplexVector n) (p q : TwoCoefficientIndex n r) :
    chartTwoMetricMatrix (r := r) E g h a z (twoCoefficientFlip n r p) (twoCoefficientFlip n r q) =
      chartTwoMetricMatrix (r := r) E g h a z p q := by
  rcases p with ⟨⟨α,i⟩,j⟩
  rcases q with ⟨⟨β,k⟩,l⟩
  simp only [chartTwoMetricMatrix, Matrix.kronecker_apply, twoCoefficientFlip, Equiv.coe_fn_mk]
  ring

theorem chartTwoDual_skew (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r) (z : ComplexVector n)
    (hskew : ∀ i j, F z j i = -F z i j) (i j : Fin n) (α : Fin r) :
    chartTwoDual E g h φ a F z j i α = -chartTwoDual E g h φ a F z i j α := by
  classical
  let A := chartTwoMetricMatrix (r := r) E g h a z
  let p : TwoCoefficientIndex n r := ((α,i),j)
  let T := twoCoefficientFlip n r
  let v := fun q : TwoCoefficientIndex n r => F z q.1.2 q.2 q.1.1
  have hA (q : TwoCoefficientIndex n r) : A (T p) (T q) = A p q := chartTwoMetricMatrix_flip E g h a z p q
  have hv (q : TwoCoefficientIndex n r) : v (T q) = -v q := by
    simpa only [v, T, twoCoefficientFlip, Equiv.coe_fn_mk, PiLp.neg_apply] using
      congrArg (fun V : ComplexVector r => V q.1.1) (hskew q.1.2 q.2)
  have hs : (∑ q, A (T p) q * v q) = -(∑ q, A p q * v q) := by
    rw [← T.sum_comp (fun q => A (T p) q * v q)]
    simp only [hA, hv, mul_neg, Finset.sum_neg_distrib]
  change (Real.exp (-φ (chartInv a z)) : ℂ) * (∑ q, A (T p) q * v q) =
    -((Real.exp (-φ (chartInv a z)) : ℂ) * (∑ q, A p q * v q))
  rw [hs, mul_neg]

end Yau.LeafProofs.L14Aux
