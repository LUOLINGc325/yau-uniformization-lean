import Yau.Proofs.F03OperatorDifferentiation

/-! The genuine finite-dimensional derivative of bounded source-word maps. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Direction linearity is proved using the actual scalar Fréchet
derivative, then finite dimensionality supplies continuity. -/
def wordOperatorDerivative
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) (Q : Set E)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (w : List E) (x : E) : E →L[ℝ] H →L[ℝ] ℝ := by
  classical
  exact if hx : x ∈ Q then
    ({ toFun := fun v => A (v::w) x
       map_add' := by
         intro v z
         ext f
         simp only [heval _ x hx,directionalWordDerivative,add_apply,map_add]
       map_smul' := by
         intro c v
         ext f
         simp only [heval _ x hx,directionalWordDerivative,smul_apply,map_smul,RingHom.id_apply] }
      : E →ₗ[ℝ] H →L[ℝ] ℝ).toContinuousLinearMap
    else 0

theorem wordOperatorDerivative_apply
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) (Q : Set E)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (w : List E) {x : E} (hx : x ∈ Q) (v : E) :
    wordOperatorDerivative A F Q heval w x v = A (v::w) x := by
  classical
  simp only [wordOperatorDerivative,dif_pos hx,LinearMap.coe_toContinuousLinearMap']
  rfl

theorem wordOperatorDerivative_flip_apply
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) (Q : Set E)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (w : List E) {x : E} (hx : x ∈ Q) (f : H) :
    (wordOperatorDerivative A F Q heval w x).flip f =
      fderiv ℝ (directionalWordDerivative (F f) w) x := by
  ext v
  rw [ContinuousLinearMap.flip_apply,wordOperatorDerivative_apply A F Q heval w hx,
    heval _ x hx]
  rfl

theorem wordOperatorDerivative_hasFDerivAt_apply
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) {Q : Set E} (hQ : IsOpen Q)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (hF : ∀ f, ContDiffOn ℝ ∞ (F f) Q)
    (w : List E) {x : E} (hx : x ∈ Q) (f : H) :
    HasFDerivAt (fun y => A w y f) (wordOperatorDerivative A F Q heval w x |>.flip f) x := by
  rw [wordOperatorDerivative_flip_apply A F Q heval w hx]
  have heq : (fun y => A w y f) =ᶠ[𝓝 x] directionalWordDerivative (F f) w := by
    filter_upwards [hQ.mem_nhds hx] with y hy
    exact heval w y hy f
  exact (((directionalWordDerivative_contDiffOn hQ (hF f) w).contDiffAt
    (hQ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.congr_of_eventuallyEq heq

theorem wordOperatorDerivative_continuousOn
    (A : List E → E → H →L[ℝ] ℝ) (F : H → E → ℝ) (Q : Set E)
    (heval : ∀ w, ∀ x ∈ Q, ∀ f, A w x f = directionalWordDerivative (F f) w x)
    (hA : ∀ w, ContinuousOn (A w) Q) (w : List E) :
    ContinuousOn (wordOperatorDerivative A F Q heval w) Q := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply (hA (v::w)).congr
  intro x hx
  exact wordOperatorDerivative_apply A F Q heval w hx v

end Yau.Proofs.F03Aux
