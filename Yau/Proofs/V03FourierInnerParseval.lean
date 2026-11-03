import Yau.Proofs.V03FourierParsevalCircle
import Yau.Proofs.V03FourierFunctional

/-! Native complex cross-Parseval for continuous circle traces, with its
actual convergent series rather than a formal coefficient pairing. -/

open scoped Topology lp
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem circle_parseval_inner {u v : AddCircle T → ℂ} (hu : Continuous u) (hv : Continuous v) :
    HasSum (fun k : ℤ => star (fourierCoeff u k) * fourierCoeff v k)
      (∫ x : AddCircle T, star (u x) * v x ∂haarAddCircle) := by
  let f : C(AddCircle T, ℂ) := ⟨u, hu⟩
  let g : C(AddCircle T, ℂ) := ⟨v, hv⟩
  let F := ContinuousMap.toLp 2 haarAddCircle ℂ f
  let G := ContinuousMap.toLp 2 haarAddCircle ℂ g
  have hcoeff (k : ℤ) : inner ℂ (fourierBasis k) F = fourierCoeff u k := by
    rw [← fourierBasis.repr_apply_apply F k, fourierBasis_repr, fourierCoeff_toLp]
    rfl
  have hcoeff' (k : ℤ) : inner ℂ (fourierBasis k) G = fourierCoeff v k := by
    rw [← fourierBasis.repr_apply_apply G k, fourierBasis_repr, fourierCoeff_toLp]
    rfl
  have hh := fourierBasis.hasSum_inner_mul_inner F G
  have hleft (k : ℤ) : inner ℂ F (fourierBasis k) = star (fourierCoeff u k) := by
    rw [← inner_conj_symm, hcoeff]
    rfl
  simp_rw [hleft, hcoeff'] at hh
  have hi : inner ℂ F G = ∫ x : AddCircle T, star (u x) * v x ∂haarAddCircle := by
    rw [ContinuousMap.inner_toLp]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm (v x) (star (u x)))
  rwa [hi] at hh

end Yau.Blueprint.V03Proof
