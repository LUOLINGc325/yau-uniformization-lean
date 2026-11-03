import Yau.Proofs.E02InfLowerTest
import Yau.Proofs.E02PolynomialJet

open Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner product with an explicit real-linear declared type. -/
def realInnerTensor : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

theorem peanoLowerPolynomial_eq_jetPolynomial (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (ε : ℝ) :
    peanoLowerPolynomial c a p A ε = jetPolynomial c a p (A-(2*ε) • (realInnerTensor (E := E))) := by
  funext y
  change c+p (y-a)+(1/2)*A (y-a) (y-a)-ε*‖y-a‖^2 =
    c+p (y-a)+(1/2)*(A (y-a) (y-a)-(2*ε)*⟪y-a,y-a⟫_ℝ)
  rw [real_inner_self_eq_norm_sq]
  ring

theorem lowerTestTensor_symmetric (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (ε : ℝ) :
    ∀ v w, (A-(2*ε) • (realInnerTensor (E := E))) v w = (A-(2*ε) • (realInnerTensor (E := E))) w v := by
  intro v w
  change A v w-(2*ε)*⟪v,w⟫_ℝ = A w v-(2*ε)*⟪w,v⟫_ℝ
  rw [hA v w,real_inner_comm v w]

/-- The regularizing error is exactly twice epsilon in the real Hessian. -/
theorem peanoLowerPolynomial_second_fderiv (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) (ε : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (peanoLowerPolynomial c a p A ε)) x = A-(2*ε) • (realInnerTensor (E := E)) := by
  rw [peanoLowerPolynomial_eq_jetPolynomial]
  exact jetPolynomial_second_fderiv c a p _ (lowerTestTensor_symmetric A hA ε) x

theorem peanoLowerPolynomial_first_fderiv_at (c : ℝ) (a : E) (p : E →L[ℝ] ℝ)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : ∀ v w, A v w = A w v) (ε : ℝ) :
    fderiv ℝ (peanoLowerPolynomial c a p A ε) a = p := by
  rw [peanoLowerPolynomial_eq_jetPolynomial]
  simpa only [sub_self,map_zero,add_zero] using
    (jetPolynomial_hasFDerivAt c a p _ (lowerTestTensor_symmetric A hA ε) a).fderiv

end Yau.NodeProofs.E02Aux
