import Yau.Proofs.F05SchauderTimeAffine
import Yau.Proofs.F05ClosedChartEquation

/-! A genuine local solution for the shifted original metric transports
back to its actual interval, with both one-sided endpoint derivatives. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ShiftedRestart (τ : ℝ) (v : M.Carrier → ℝ → ℝ) : M.Carrier → ℝ → ℝ :=
  fun x t => v x (t-τ)

theorem F05_shifted_restart_schauder (A : AtlasData M) {τ δ α C : ℝ} (hδ : 0 < δ)
    (v : M.Carrier → ℝ → ℝ)
    (hv : ∀ i, SchauderBound α (F05Q A i δ) (pull A i v) C) :
    ∀ i, SchauderBound α (cylinder (F05D A i) τ (τ+δ))
      (pull A i (F05ShiftedRestart τ v)) (4*C) := by
  intro i
  have hMap : MapsTo (fun t : ℝ => 1*t+(-τ)) (Icc τ (τ+δ)) (Icc 0 δ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hResult := F05_schauder_timeAffine (by linarith : τ < τ+δ) hMap (hv i)
  have hPull : pull A i (F05ShiftedRestart τ v) = F05TimeAffine 1 (-τ) (pull A i v) := by
    funext p
    simp only [pull,F05ShiftedRestart,F05TimeAffine,F05TimeAffinePoint,one_mul,sub_eq_add_neg]
  rw [hPull]
  convert! hResult using 1
  norm_num
  ring

theorem F05_shifted_restart_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {τ δ : ℝ} (hδ : 0 < δ)
    (v : M.Carrier → ℝ → ℝ) (hv : ∀ i, C2 (F05Q A i δ) (pull A i v))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 δ,
      derivWithin (v x) (Icc 0 δ) t = Real.exp (-v x t)*laplacian (h (t+τ)) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h (t+τ)) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc τ (τ+δ),
      derivWithin (F05ShiftedRestart τ v x) (Icc τ (τ+δ)) t =
        Real.exp (-F05ShiftedRestart τ v x t)*
          laplacian (h t) (fun y => F05ShiftedRestart τ v y t) x+
        (1-Real.exp (-F05ShiftedRestart τ v x t))*scalarCurvature (h t) x := by
  intro x hx t ht
  have hMap : MapsTo (fun t : ℝ => t-τ) (Icc τ (τ+δ)) (Icc 0 δ) := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2]
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hFiber : {r : ℝ | (z,r) ∈ F05Q A i δ} = Icc 0 δ := by
    ext r
    change (z ∈ F05D A i ∧ r ∈ Icc 0 δ) ↔ r ∈ Icc 0 δ
    exact and_iff_right hz
  have hDiff : DifferentiableWithinAt ℝ (v x) (Icc 0 δ) (t-τ) := by
    have hAt := (hv i).2.2.2.2.2 (z,t-τ) ⟨hz,hMap ht⟩
    simpa only [hFiber,pull,hzx] using hAt
  have hChain := hDiff.hasDerivWithinAt.comp t
    (((hasDerivAt_id t).sub_const τ).hasDerivWithinAt) hMap
  have hTime := hChain.derivWithin (uniqueDiffOn_Icc (by linarith : τ < τ+δ) t ht)
  have hOriginal := hEq x hx (t-τ) (hMap ht)
  simp only [sub_add_cancel] at hOriginal
  have hTime' : derivWithin (F05ShiftedRestart τ v x) (Icc τ (τ+δ)) t =
      derivWithin (v x) (Icc 0 δ) (t-τ) := by
    change derivWithin (fun r => v x (r-τ)) (Icc τ (τ+δ)) t =
      derivWithin (v x) (Icc 0 δ) (t-τ)
    simpa only [Function.comp_def,id_eq,mul_one] using hTime
  exact hTime'.trans hOriginal

theorem F05_shifted_restart_continuous {O : Set M.Carrier} {τ δ : ℝ}
    (v : M.Carrier → ℝ → ℝ)
    (hv : ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc 0 δ)) :
    ContinuousOn (fun z : M.Carrier × ℝ => F05ShiftedRestart τ v z.1 z.2)
      (closure O ×ˢ Icc τ (τ+δ)) := by
  apply hv.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
  intro z hz
  change z.1 ∈ closure O ∧ z.2-τ ∈ Icc 0 δ
  exact ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩

end Yau.Proofs.F05Aux
