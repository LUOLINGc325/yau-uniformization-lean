import Yau.LeafProofs.L03DivergenceMollifier

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

section Euclidean

variable {E ι α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α]

theorem directional_derivative_mul (χ φ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun z => χ z * φ z) x v =
      χ x * fderiv ℝ φ x v + φ x * fderiv ℝ χ x v := by
  exact DFunLike.congr_fun (fderiv_fun_mul (hχ.differentiable (by simp) x)
    (hφ.differentiable (by simp) x)) v

theorem directional_second_derivative_mul (χ φ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => χ y * φ y) z v) x w =
      χ x * fderiv ℝ (fun z => fderiv ℝ φ z v) x w +
      φ x * fderiv ℝ (fun z => fderiv ℝ χ z v) x w +
      fderiv ℝ χ x w * fderiv ℝ φ x v + fderiv ℝ φ x w * fderiv ℝ χ x v := by
  have hdχ : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdφ : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heq : (fun z => fderiv ℝ (fun y => χ y * φ y) z v) =
      (fun z => χ z * fderiv ℝ φ z v + φ z * fderiv ℝ χ z v) :=
    funext fun z => directional_derivative_mul χ φ hχ hφ z v
  rw [heq, fderiv_fun_add ((hχ.mul hdφ).differentiable (by simp) x)
    ((hφ.mul hdχ).differentiable (by simp) x)]
  simp only [add_apply]
  rw [directional_derivative_mul χ _ hχ hdφ, directional_derivative_mul φ _ hφ hdχ]
  ring

/-- The genuine scalar formal-transpose row, containing derivatives
only of the test and coefficient. -/
def divergenceFormalTest (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (φ : E → ℝ) (x : E) (r : β) (c : α) : ℝ :=
  -(∑ i, ∑ j, (a r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
    fderiv ℝ (a r c i j) x (v j) * fderiv ℝ φ x (v i))) -
    (∑ i, B r c i x * fderiv ℝ φ x (v i)) + C r c x * φ x

/-- The compact-localization value datum before multiplying the raw input. -/
def localizedDivergenceValueCoefficient (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (χ : E → ℝ) (x : E) (r : β) (c : α) : ℝ :=
  (∑ i, ∑ j, (fderiv ℝ (a r c i j) x (v j) * fderiv ℝ χ x (v i) +
    a r c i j x * fderiv ℝ (fun z => fderiv ℝ χ z (v i)) x (v j))) +
    ∑ i, B r c i x * fderiv ℝ χ x (v i)

/-- The compact-localization divergence flux coefficient. Both cross
terms occur, without assuming symmetry of the coefficient system. -/
def localizedDivergenceFluxCoefficient (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (χ : E → ℝ) (x : E) (r : β) (c : α) (l : ι) : ℝ :=
  -(∑ j, a r c l j x * fderiv ℝ χ x (v j)) -
    ∑ i, fderiv ℝ χ x (v i) * a r c i l x

/-- Exact localization of the formal transpose. This identity holds
before integrating and never differentiates the rough input. -/
theorem divergenceFormalTest_mul (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (χ φ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ)
    (x : E) (r : β) (c : α) :
    χ x * divergenceFormalTest v a B C φ x r c =
      divergenceFormalTest v a B C (fun z => χ z * φ z) x r c +
        localizedDivergenceValueCoefficient v a B χ x r c * φ x -
        ∑ l, localizedDivergenceFluxCoefficient v a χ x r c l * fderiv ℝ φ x (v l) := by
  classical
  have hcross : (∑ i, ∑ j, a r c i j x * fderiv ℝ χ x (v i) * fderiv ℝ φ x (v j)) =
      ∑ j, ∑ i, a r c i j x * fderiv ℝ χ x (v i) * fderiv ℝ φ x (v j) := Finset.sum_comm
  unfold divergenceFormalTest localizedDivergenceValueCoefficient localizedDivergenceFluxCoefficient
  simp_rw [directional_second_derivative_mul χ φ hχ hφ, directional_derivative_mul χ φ hχ hφ]
  simp only [mul_add, mul_sub, mul_neg, neg_mul, add_mul, sub_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm] at hcross ⊢
  linarith

theorem divergenceFormalTest_mul_sum (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ) (u : E → α → ℝ)
    (χ φ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (x : E) (r : β) :
    (∑ c, divergenceFormalTest v a B C φ x r c * (χ x * u x c)) =
      (∑ c, divergenceFormalTest v a B C (fun z => χ z * φ z) x r c * u x c) +
        (∑ c, localizedDivergenceValueCoefficient v a B χ x r c * u x c) * φ x -
        ∑ l, (∑ c, localizedDivergenceFluxCoefficient v a χ x r c l * u x c) * fderiv ℝ φ x (v l) := by
  classical
  have hc (c : α) : divergenceFormalTest v a B C φ x r c * (χ x * u x c) =
      divergenceFormalTest v a B C (fun z => χ z * φ z) x r c * u x c +
        localizedDivergenceValueCoefficient v a B χ x r c * u x c * φ x -
        ∑ l, localizedDivergenceFluxCoefficient v a χ x r c l * u x c * fderiv ℝ φ x (v l) := by
    have h := congrArg (fun t => t * u x c) (divergenceFormalTest_mul v a B C χ φ hχ hφ x r c)
    simp only [add_mul, sub_mul, Finset.sum_mul] at h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  simp_rw [hc]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun c l =>
    localizedDivergenceFluxCoefficient v a χ x r c l * u x c * fderiv ℝ φ x (v l))]

theorem integral_divergenceFormalTest [MeasurableSpace E] (ν : Measure E)
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (u : E → α → ℝ) (φ : E → ℝ) (r : β)
    (hp : ∀ c i j, Integrable (fun x =>
      (a r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
        fderiv ℝ (a r c i j) x (v j) * fderiv ℝ φ x (v i)) * u x c) ν)
    (hb : ∀ c i, Integrable (fun x => (B r c i x * fderiv ℝ φ x (v i)) * u x c) ν)
    (hc : ∀ c, Integrable (fun x => φ x * (C r c x * u x c)) ν) :
    (∫ x, ∑ c, divergenceFormalTest v a B C φ x r c * u x c ∂ν) =
      ∑ c, ((∑ i, ∑ j, -(∫ x,
        (a r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
          fderiv ℝ (a r c i j) x (v j) * fderiv ℝ φ x (v i)) * u x c ∂ν)) +
        (∑ i, -(∫ x, (B r c i x * fderiv ℝ φ x (v i)) * u x c ∂ν)) +
        ∫ x, φ x * (C r c x * u x c) ∂ν) := by
  classical
  let p := fun c i j x =>
    (a r c i j x * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) x (v j) +
      fderiv ℝ (a r c i j) x (v j) * fderiv ℝ φ x (v i)) * u x c
  let q := fun c i x => (B r c i x * fderiv ℝ φ x (v i)) * u x c
  let t := fun c x => φ x * (C r c x * u x c)
  have hpi (c : α) : Integrable (fun x => ∑ i, ∑ j, p c i j x) ν :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hp c i j))
  have hqi (c : α) : Integrable (fun x => ∑ i, q c i x) ν :=
    integrable_finsetSum Finset.univ (fun i _ => hb c i)
  have heq (c : α) : (fun x => divergenceFormalTest v a B C φ x r c * u x c) =
      (fun x => -(∑ i, ∑ j, p c i j x) - (∑ i, q c i x) + t c x) := by
    funext x
    simp only [divergenceFormalTest, p, q, t, add_mul, sub_mul, neg_mul, Finset.sum_mul]
    ring
  have hrow (c : α) : Integrable (fun x => divergenceFormalTest v a B C φ x r c * u x c) ν := by
    rw [heq]
    exact ((hpi c).neg.sub (hqi c)).add (hc c)
  rw [integral_finsetSum Finset.univ (fun c _ => hrow c)]
  apply Finset.sum_congr rfl
  intro c _
  have hIP : (∫ x, ∑ i, ∑ j, p c i j x ∂ν) = ∑ i, ∑ j, ∫ x, p c i j x ∂ν := by
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hp c i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hp c i j)
  have hIQ := integral_finsetSum Finset.univ (fun i _ => hb c i)
  have hAdd := integral_add ((hpi c).neg.sub (hqi c)) (hc c)
  have hSub := integral_sub (hpi c).neg (hqi c)
  simp only [Pi.sub_apply, Pi.neg_apply] at hAdd hSub
  rw [heq, hAdd, hSub, integral_neg, hIP, hIQ]
  simp only [Finset.sum_neg_distrib]
  rfl

end Euclidean

end Yau.LeafProofs.L03
