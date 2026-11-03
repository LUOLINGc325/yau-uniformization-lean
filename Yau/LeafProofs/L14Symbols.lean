import Yau.LeafProofs.L14Two

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle

namespace Yau.LeafProofs.L14Aux

theorem rankOne_positive_trace {n : ℕ}
    (G B : Matrix (Fin n) (Fin n) ℂ) (a u v : Fin n → ℂ) :
    ((Matrix.vecMulVec a u)ᴴ * B * Matrix.vecMulVec a v * Gᵀ).trace =
      (star a ⬝ᵥ B *ᵥ a) * (star u ⬝ᵥ G *ᵥ v) := by
  rw [Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
    Matrix.smul_vecMul, Matrix.vecMul_transpose, dotProduct_smul, Matrix.dotProduct_mulVec]
  simp only [smul_eq_mul, ← Matrix.dotProduct_mulVec]

theorem rankOne_cross_trace {n : ℕ} (a u v : Fin n → ℂ) :
    ((Matrix.vecMulVec a u)ᵀᴴ * Matrix.vecMulVec a v).trace =
      star (star a ⬝ᵥ u) * (star a ⬝ᵥ v) := by
  rw [Matrix.transpose_vecMulVec, Matrix.conjTranspose_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  congr 1
  exact Matrix.star_dotProduct _ _

theorem loweredCurl_rankOne {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (a u : Fin n → ℂ) (i j : Fin n) :
    loweredCurlMatrix G (Matrix.vecMulVec a u) i j =
      a i * (G *ᵥ u) j - a j * (G *ᵥ u) i := by
  rw [loweredCurlMatrix_apply]
  simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem wedge_contraction_energy_identity {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (a : Fin n → ℂ) (W : Fin r → Fin n → ℂ) :
    twoCoefficientNormSq G H (fun α i j =>
      a i * (G *ᵥ W α) j - a j * (G *ᵥ W α) i) +
      (star (fun α => star a ⬝ᵥ W α) ⬝ᵥ H *ᵥ (fun α => star a ⬝ᵥ W α)).re =
        (star a ⬝ᵥ G⁻¹ *ᵥ a).re *
          (∑ α, ∑ β, H α β * (star (W α) ⬝ᵥ G *ᵥ W β)).re := by
  let D := fun α => Matrix.vecMulVec a (W α)
  have hc := loweredCurl_energy_identity G H D hG.isHermitian
    (hG.isUnit.map Matrix.detMonoidHom)
  have hcurl : twoCoefficientNormSq G H
      (fun α i j => a i * (G *ᵥ W α) j - a j * (G *ᵥ W α) i) =
      ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        H α β * G⁻¹ i k * G⁻¹ j l * star (loweredCurlMatrix G (D α) i j) *
          loweredCurlMatrix G (D β) k l).re := by
    simp only [D, loweredCurl_rankOne, twoCoefficientNormSq]
  have hcross : (∑ α, ∑ β, ∑ i, ∑ j,
      H α β * star (D α i j) * D β j i) =
      star (fun α => star a ⬝ᵥ W α) ⬝ᵥ H *ᵥ (fun α => star a ⬝ᵥ W α) := by
    have he (α β : Fin r) := rankOne_cross_trace a (W α) (W β)
    simp only [trace_cross_contraction] at he
    change _ = ∑ α, star (star a ⬝ᵥ W α) * ∑ β, H α β * (star a ⬝ᵥ W β)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    calc
      _ = H α β * (∑ i, ∑ j, star (D α i j) * D β j i) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = H α β * (star (star a ⬝ᵥ W α) * (star a ⬝ᵥ W β)) := congrArg (fun c : ℂ => H α β * c) (he α β)
      _ = _ := by ring
  have hpositive : (∑ α, ∑ β, H α β * ((D α)ᴴ * G⁻¹ * D β * Gᵀ).trace) =
      (star a ⬝ᵥ G⁻¹ *ᵥ a) * ∑ α, ∑ β, H α β * (star (W α) ⬝ᵥ G *ᵥ W β) := by
    simp only [D, rankOne_positive_trace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hAim : (star a ⬝ᵥ G⁻¹ *ᵥ a).im = 0 :=
    (Complex.nonneg_iff.mp (hG.inv.posSemidef.dotProduct_mulVec_nonneg a)).2.symm
  have he := congrArg Complex.re hc
  have hre (b : ℂ) : ((star a ⬝ᵥ G⁻¹ *ᵥ a) * b).re =
      (star a ⬝ᵥ G⁻¹ *ᵥ a).re * b.re := by
    rw [Complex.mul_re, hAim, zero_mul, sub_zero]
  rw [hpositive, hcross, Complex.sub_re, hre] at he
  rw [hcurl]
  linarith

theorem wedge_contraction_energy_identity_coefficients {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (a : Fin n → ℂ) (F : Fin r → Fin n → ℂ) :
    twoCoefficientNormSq G H (fun α i j => a i * F α j - a j * F α i) +
      (star (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α) ⬝ᵥ H *ᵥ (fun α => star a ⬝ᵥ G⁻¹ *ᵥ F α)).re =
        (star a ⬝ᵥ G⁻¹ *ᵥ a).re *
          (∑ α, ∑ β, H α β * (star (F α) ⬝ᵥ G⁻¹ *ᵥ F β)).re := by
  have hcancel (v : Fin n → ℂ) : G *ᵥ (G⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hG.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  have hpair (u v : Fin n → ℂ) :
      star (G⁻¹ *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ G⁻¹ *ᵥ v := by
    rw [Matrix.star_mulVec, hG.inv.isHermitian.eq, ← Matrix.dotProduct_mulVec]
  simpa only [hcancel, hpair] using
    wedge_contraction_energy_identity G H hG a (fun α => G⁻¹ *ᵥ F α)

theorem modelOneDbar_mul_scalar {n r : ℕ}
    (η : Yau.ComplexVector n → ℂ)
    (F : Yau.ComplexVector n → Fin n → Yau.ComplexVector r)
    (z : Yau.ComplexVector n) (hη : DifferentiableAt ℝ η z)
    (hF : DifferentiableAt ℝ F z) (i j : Fin n) :
    modelOneDbar (fun y k => η y • F y k) z i j =
      η z • modelOneDbar F z i j +
        wirtBar η z (stdVec i) • F z j - wirtBar η z (stdVec j) • F z i := by
  have hd (k : Fin n) (α : Fin r) : DifferentiableAt ℝ (fun y => F y k α) z :=
    ((EuclideanSpace.proj α : Yau.ComplexVector r →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt.comp z
      (differentiableAt_pi.mp hF k)
  ext α
  change wirtBar (fun y => η y * F y j α) z (stdVec i) -
      wirtBar (fun y => η y * F y i α) z (stdVec j) =
    η z * (wirtBar (fun y => F y j α) z (stdVec i) -
      wirtBar (fun y => F y i α) z (stdVec j)) +
        wirtBar η z (stdVec i) * F z j α - wirtBar η z (stdVec j) * F z i α
  rw [wirtBar_mul_rule η _ z (stdVec i) hη (hd j α),
    wirtBar_mul_rule η _ z (stdVec j) hη (hd i α)]
  ring

section IMSAlgebra

theorem finite_hermitian_IMS {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (h : Yau.HermitianInnerProduct V) (χ : ι → ℝ) (v : V) (w : ι → V)
    (hχ : ∑ i, χ i ^ 2 = 1) (hw : ∑ i, (χ i : ℂ) • w i = 0) :
    (∑ i, (h.toFun ((χ i : ℂ) • v + w i) ((χ i : ℂ) • v + w i)).re) =
      (h.toFun v v).re + ∑ i, (h.toFun (w i) (w i)).re := by
  have hzeroL : h.toFun 0 v = 0 := by simpa using h.map_smul_left 0 (0 : V) v
  have hzeroR : h.toFun v 0 = 0 := by simpa using h.map_smul_right 0 v (0 : V)
  have hstar (c : ℝ) : star (c : ℂ) = (c : ℂ) := by simp
  have hleft : (∑ i, (χ i : ℂ) * h.toFun (w i) v) = 0 := by
    have he := congrArg (fun z : V => h.toFun z v) hw
    simpa only [hermitian_sum_left, h.map_smul_left, hstar, hzeroL] using he
  have hright : (∑ i, (χ i : ℂ) * h.toFun v (w i)) = 0 := by
    have he := congrArg (fun z : V => h.toFun v z) hw
    simpa only [hermitian_sum_right, h.map_smul_right, hzeroR, mul_comm] using he
  have hcoeff : (∑ i, (χ i : ℂ) * (χ i : ℂ)) = 1 := by
    simpa only [pow_two] using (show (∑ i, (χ i : ℂ) ^ 2) = 1 by exact_mod_cast hχ)
  have hterm (i : ι) : h.toFun ((χ i : ℂ) • v + w i) ((χ i : ℂ) • v + w i) =
      ((χ i : ℂ) * (χ i : ℂ)) * h.toFun v v + (χ i : ℂ) * h.toFun (w i) v +
        (χ i : ℂ) * h.toFun v (w i) + h.toFun (w i) (w i) := by
    simp only [h.map_add_left, h.map_add_right, h.map_smul_left, h.map_smul_right, hstar]
    ring
  have he : (∑ i, h.toFun ((χ i : ℂ) • v + w i) ((χ i : ℂ) • v + w i)) =
      h.toFun v v + ∑ i, h.toFun (w i) (w i) := by
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hcoeff, one_mul, hleft, hright]
    ring
  have hre (f : ι → ℂ) : (∑ i, f i).re = ∑ i, (f i).re := map_sum Complex.reCLM _ _
  simpa only [hre, Complex.add_re] using congrArg Complex.re he

end IMSAlgebra

open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem chartOneDual_mul_scalar (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (η : ComplexVector n → ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (i : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a (fun y k => η y • F y k) z i α =
      η z * chartOneDual (r := r) E g h φ a F z i α := by
  unfold chartOneDual
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem chartOneDual_inverse (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (i : Fin n) (α : Fin r) :
    (∑ β, (BundleDbar.metricMatrix (r := r) E h a z)⁻¹ α β *
      chartOneDual (r := r) E g h φ a F z i β) =
        (Real.exp (-φ (chartInv a z)) : ℂ) * chartOneRaise g a F z i α := by
  simp_rw [chartOneDual_eq_weighted_raise]
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let W := fun β => chartOneRaise g a F z i β
  change (H⁻¹ *ᵥ (((Real.exp (-φ (chartInv a z)) : ℂ) • H) *ᵥ W)) α = _
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul H ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom),
    Matrix.one_mulVec]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chartDbarAdjoint_mul_scalar (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (η : ComplexVector n → ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hη : DifferentiableAt ℝ η z) :
    chartDbarAdjoint (r := r) E g.form h φ a (fun y k => η y • F y k) z =
      η z • chartDbarAdjoint (r := r) E g.form h φ a F z -
        WithLp.toLp 2 (fun α => ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α) := by
  let B := chartOneDual (r := r) E g.form h φ a F
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let c : ℂ := Real.exp (φ (chartInv a z))
  let ρ : ℂ := Real.exp (-φ (chartInv a z))
  have hρ : c * ρ = 1 := by
    dsimp only [c, ρ]
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hd (i : Fin n) (β : Fin r) : DifferentiableAt ℝ (fun y => B y i β) z :=
    (chartOneDual_contDiff E g h hh φ hφ a F hF hs i β).contDiffAt.differentiableAt (by simp)
  have hder (i : Fin n) (β : Fin r) :
      wirt (fun y => chartOneDual (r := r) E g.form h φ a (fun t k => η t • F t k) y i β) z (stdVec i) =
        wirt η z (stdVec i) * B z i β + η z * wirt (fun y => B y i β) z (stdVec i) := by
    simp_rw [chartOneDual_mul_scalar]
    exact wirt_mul_rule η _ z (stdVec i) hη (hd i β)
  ext α
  change -c * (∑ β, H⁻¹ α β * ∑ i,
      wirt (fun y => chartOneDual (r := r) E g.form h φ a (fun t k => η t • F t k) y i β) z (stdVec i)) =
    η z * (-c * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i))) -
      ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α
  simp_rw [hder, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ β, H⁻¹ α β * ∑ i, wirt η z (stdVec i) * B z i β) =
      ρ * ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α := by
    calc
      _ = ∑ i, wirt η z (stdVec i) * ∑ β, H⁻¹ α β * B z i β := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro β _
        ring
      _ = ∑ i, wirt η z (stdVec i) * (ρ * chartOneRaise g.form a F z i α) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [chartOneDual_inverse E g.form h φ a F z hz i α]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsecond : (∑ β, H⁻¹ α β * ∑ i, η z * wirt (fun y => B y i β) z (stdVec i)) =
      η z * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst, hsecond]
  calc
    _ = η z * (-c * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i))) -
        (c * ρ) * (∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α) := by ring
    _ = _ := by rw [hρ, one_mul]

end Yau.LeafProofs.L14Aux
