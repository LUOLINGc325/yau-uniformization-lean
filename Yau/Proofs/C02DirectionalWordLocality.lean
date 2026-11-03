import Yau.Proofs.C02DirectionalWords

/-! Ordered directional derivatives compose by concatenation and depend
only on the actual local function, with no extension chosen outside it. -/

noncomputable section
open Filter
open scoped Topology
namespace Yau.Blueprint.C02Proof
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directionalWord_append (b : ι → E) (f : E → F) (u w : List ι) :
    directionalWord b f (u ++ w) = directionalWord b (directionalWord b f w) u := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, directionalWord, ih]

theorem eventuallyEq_directionalWord (b : ι → E) {f g : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] g) (w : List ι) :
    directionalWord b f w =ᶠ[𝓝 x] directionalWord b g w := by
  induction w with
  | nil => exact h
  | cons a w ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun L : E →L[ℝ] F => L (b a)) hy

end Yau.Blueprint.C02Proof
