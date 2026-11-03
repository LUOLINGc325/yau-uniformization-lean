import Yau.Proofs.E02InfConvolution
import Yau.Proofs.E02PeanoFirst

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual smooth quadratic lower polynomial supplied by a Peano jet.
Only this polynomial is differentiated in the viscosity argument. -/
def peanoLowerPolynomial (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ε : ℝ) (y : E) : ℝ :=
  c+p (y-a)+(1/2)*A (y-a) (y-a)-ε*‖y-a‖^2

theorem peanoLowerPolynomial_contDiff (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ε : ℝ) :
    ContDiff ℝ ∞ (peanoLowerPolynomial c a p A ε) := by
  have hn : ContDiff ℝ ∞ (fun y : E => ‖y-a‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hPoly : ContDiff ℝ ∞ (fun y : E => c+p (y-a)+(1/2)*A (y-a) (y-a)) := by
    fun_prop
  exact hPoly.sub (contDiff_const.mul hn)

theorem peanoLowerPolynomial_at (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ε : ℝ) :
    peanoLowerPolynomial c a p A ε a = c := by
  simp [peanoLowerPolynomial]

/-- Translating a genuine lower Peano polynomial to an attained interior
source gives a smooth lower test for the original function, with exactly
the same linear and quadratic coefficients. -/
theorem compactInfConvolution_source_lower_test
    (K : Set E) (v : E → ℝ) (hv0 : ∀ y ∈ K, 0 ≤ v y)
    {κ : ℝ} (hκ : 0 < κ) (q a : E) (ha : a ∈ interior K)
    (hmin : compactInfConvolution K v κ q = v a+‖q-a‖^2/(2*κ))
    (p : E →L[ℝ] ℝ) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hJet : RealSecondJet (compactInfConvolution K v κ) q p A)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (peanoLowerPolynomial (v a) a p A ε) ∧
      peanoLowerPolynomial (v a) a p A ε a = v a ∧
      ∀ᶠ y in 𝓝 a, peanoLowerPolynomial (v a) a p A ε y ≤ v y := by
  refine ⟨peanoLowerPolynomial_contDiff _ _ _ _ _,peanoLowerPolynomial_at _ _ _ _ _,?_⟩
  have hShift : Tendsto (fun y : E => q+(y-a)) (𝓝 a) (𝓝 q) := by
    have hc : Continuous (fun y : E => q+(y-a)) := by fun_prop
    simpa only [sub_self,add_zero] using hc.tendsto a
  have hBounds := hShift.eventually (realSecondJet_quadratic_bounds hJet hε)
  have hK : ∀ᶠ y in 𝓝 a, y ∈ K := mem_interior_iff_mem_nhds.mp ha
  filter_upwards [hBounds,hK] with y hy hyK
  have hUpper := compactInfConvolution_le_cost K v hv0 hκ (q+(y-a)) y hyK
  have heq : q+(y-a)-y = q-a := by abel
  have heq' : q+(y-a)-q = y-a := by abel
  rw [heq] at hUpper
  rw [heq',hmin] at hy
  unfold peanoLowerPolynomial
  linarith [hy.1]

end Yau.NodeProofs.E02Aux
