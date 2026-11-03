import Yau.Proofs.F05PositiveProfileExtension
import Yau.Proofs.F05TerminalProfileTrace
import Yau.Proofs.F05SmoothDirichletLocal

/-! An actual smooth terminal profile produces an actual compatible local
restart on the same supplied metric family, with the original lateral
datum. The global profile and restart datum are constructed inside. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_local_restart (hn : 0 < n) {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) {τ S α : ℝ} (hτ : 0 < τ) (hτS : τ < S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (p w : M.Carrier → ℝ → ℝ) (hp : SmoothSpaceTime p (Icc 0 S))
    (hα : 0 < α) (hα1 : α < 1)
    (hw : ∀ i, C2 (F05Q A i τ) (pull A i w))
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 τ, w x t = p x t)
    (hEquation : ∀ x ∈ closure O,
      derivWithin (w x) (Icc 0 τ) τ = Real.exp (-w x τ)*laplacian (h τ) (fun y => w y τ) x+
        (1-Real.exp (-w x τ))*scalarCurvature (h τ) x)
    (hSmooth : ∀ s : ℝ, 0 < s → s < τ → ∀ i,
      ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc s τ)) :
    ∃ ε K : ℝ, 0 < ε ∧ ε ≤ S-τ ∧ ε ≤ 1 ∧ 0 < K ∧
      ∀ T : ℝ, 0 < T → T ≤ ε → ∃ v : M.Carrier → ℝ → ℝ,
        (∀ i, SchauderBound α (F05Q A i T) (pull A i v) K) ∧
        ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc 0 T) ∧
        (∀ x ∈ closure O, v x 0 = w x τ) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, v x t = p x (t+τ)) ∧
        (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
          derivWithin (v x) (Icc 0 T) t = Real.exp (-v x t)*laplacian (h (t+τ)) (fun y => v y t) x+
            (1-Real.exp (-v x t))*scalarCurvature (h (t+τ)) x) ∧
        ∀ s : ℝ, 0 < s → s < T → ∀ i,
          ContDiffOn ℝ ∞ (pull A i v) (F05D A i ×ˢ Icc s T) := by
  have hInner (i : Fin A.count) : ContDiffOn ℝ ∞ (pull A i w)
      (region (A.normal i) (3/2) ×ˢ Icc (τ/2) τ) :=
    (hSmooth (τ/2) (by positivity) (by linarith) i).mono
      (prod_mono (F05_region_mono (by norm_num)) subset_rfl)
  obtain ⟨g,hg,hgEq⟩ := F05_positive_profile_global_extension hA w
    (show τ ∈ Icc (τ/2) τ from ⟨by linarith,le_rfl⟩) hInner
  let J := F05ProfileNonlinearJet h τ g
  have hJRaw := F05_fixed_profile_nonlinear_smooth h hh hR hg
    (show τ ∈ Icc 0 S from ⟨hτ.le,hτS.le⟩)
  have hJ : SmoothFn J := hJRaw
  have hS : 0 < S-τ := sub_pos.mpr hτS
  have hEnd : τ+(S-τ) = S := by ring
  have hpTail : SmoothSpaceTime p (Icc τ (τ+(S-τ))) := by
    rw [hEnd]
    exact fun x => (hp x).mono (prod_mono subset_rfl (Icc_subset_Icc hτ.le le_rfl))
  let q := F05RestartDatum τ (S-τ) p g J
  have hq : SmoothSpaceTime q (Icc 0 (S-τ)) := F05_restart_datum_smooth hS p g J hpTail hg hJ
  have hJet := F05_terminal_profile_boundary_jet hA h hτ hτS p w hp hw hBoundary hEquation hg hgEq
  have hgTrace : EqOn g (fun x => p x τ) (frontier O) := fun x hx =>
    (hgEq (frontier_subset_closure hx)).trans (hBoundary x hx τ ⟨hτ.le,le_rfl⟩)
  have hJTrace : EqOn J (fun x => derivWithin (p x) (Icc τ (τ+(S-τ))) τ) (frontier O) := by
    simpa only [hEnd] using hJet
  have hMap : MapsTo (fun t : ℝ => t+τ) (Icc 0 (S-τ)) (Icc 0 S) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let hShift := fun t => h (t+τ)
  have hEmb (x : M.Carrier) : ContDiffOn ℝ ∞ (fun z : Point n => (z.1,z.2+τ))
      (chartTarget x ×ˢ Icc 0 (S-τ)) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)
  have hMapQ (x : M.Carrier) : MapsTo (fun z : Point n => (z.1,z.2+τ))
      (chartTarget x ×ˢ Icc 0 (S-τ)) (chartTarget x ×ˢ Icc 0 S) :=
    fun z hz => ⟨hz.1,hMap hz.2⟩
  have hhShift : MetricFamilySmooth hShift (Icc 0 (S-τ)) := by
    intro x a b
    have hRaw := (hh x a b).comp (hEmb x) (hMapQ x)
    exact hRaw
  have hRShift : SmoothSpaceTime (fun x t => scalarCurvature (hShift t) x) (Icc 0 (S-τ)) := by
    intro x
    have hRaw := (hR x).comp (hEmb x) (hMapQ x)
    exact hRaw
  have hCompat := F05_restart_nonlinear_compatible h hS p g hpTail
  obtain ⟨ε,K,hε,hεS,hε1,hK,hSolve⟩ := F05_smooth_dirichlet_local hn hA hχ hShift q hS
    hhShift hq hRShift hα hα1 (by simpa only [hShift,zero_add] using hCompat)
  refine ⟨ε,K,hε,hεS,hε1,hK,?_⟩
  intro T hT hTε
  obtain ⟨v,hV,hCont,hInitial,hLat,hEq,hSm⟩ := hSolve T hT hTε
  refine ⟨v,hV,hCont,?_,?_,hEq,hSm⟩
  · intro x hx
    exact (hInitial x hx).trans ((F05_restart_initial τ (S-τ) p g J x).trans (hgEq hx))
  · intro x hx t ht
    exact (hLat x hx t ht).trans (F05_restart_lateral p g J hgTrace hJTrace hx t)

end Yau.Proofs.F05Aux
