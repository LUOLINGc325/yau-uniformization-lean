import Yau.Proofs.F05BackgroundBounds
import Yau.Proofs.F05SmoothSchauder
import Yau.Proofs.F05ExponentialHolder

/-! Subtracting fixed smooth Dirichlet data leaves a uniformly Hölder
source controlled only by the candidate's value Hölder bound. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05DirichletForcing (h : ℝ → HermitianField M) (T : ℝ)
    (p w : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  (1-Real.exp (-w x t))*scalarCurvature (h t) x-
    derivWithin (p x) (Icc 0 T) t+Real.exp (-w x t)*laplacian (h t) (fun y => p y t) x

theorem F05_value_dirichlet_source_budgets {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {S D : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S)) (hD : 0 ≤ D) :
    ∃ F : ℝ, 0 < F ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∀ T : ℝ, 0 < T → T ≤ S → ∀ w : M.Carrier → ℝ → ℝ,
      (∀ i, HolderBound α (F05Q A i T) (pull A i w) D) →
      ∀ i, HolderBound α (F05Q A i T) (pull A i (F05DirichletForcing h T p w)) F := by
  obtain ⟨B,hB,hBackground⟩ := F05_background_holder_budgets hA h p hS hh hp hR
  obtain ⟨K,hK,hSchauder⟩ := F05_smooth_schauder_uniform hA p hS hp
  let E := Real.exp D*(1+D)
  let F := 1+2*(1+E)*B+K+2*E*B
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  refine ⟨F,hF,?_⟩
  intro α hα hα1 T hT hTS w hw i
  have hExp : HolderBound α (F05Q A i T) (fun z => Real.exp (-pull A i w z)) E :=
    F05_holder_exp (holderBound_neg (hw i)) (fun z hz =>
      (neg_le_abs _).trans ((hw i).2.1 z hz))
  have hTime : HolderBound α (F05Q A i T)
      (pull A i (fun x t => derivWithin (p x) (Icc 0 T) t)) K := by
    apply holderBound_congr_on (hSchauder α hα hα1 T hT hTS i).2.2.2.2
    intro z hz
    exact F05_timeD_pull A i T p hz.1
  have hData := hBackground α hα hα1 T hTS i
  have hOne : HolderBound α (F05Q A i T) (fun _ => (1 : ℝ)) 1 := by
    simpa using (holderBound_const (α := α) (Q := F05Q A i T) (1 : ℝ))
  have hSource := holderBound_add
    (holderBound_sub (holderBound_mul (holderBound_sub hOne hExp) hData.2.2) hTime)
    (holderBound_mul hExp hData.2.1)
  apply holderBound_mono_const (show HolderBound α (F05Q A i T)
    (pull A i (F05DirichletForcing h T p w)) (2*(1+E)*B+K+2*E*B) from hSource)
  dsimp only [F]
  linarith

end Yau.Proofs.F05Aux
