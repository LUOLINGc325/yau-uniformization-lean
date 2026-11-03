import Yau.Proofs.F05CompactDirichletSolution

/-! Actual compact-domain uniqueness fixes the early values of any
pointwise limit of longer solutions with the same original data. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_coherent_limit_eq {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p u W : M.Carrier → ℝ → ℝ)
    {r t₀ S : ℝ} (hr : 0 ≤ r) (ht₀ : 0 < t₀)
    (hh : MetricFamilySmooth h (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hu : F05CompactDirichletSolution O A h p t₀ u)
    (τ : ℕ → ℝ) (w : ℕ → M.Carrier → ℝ → ℝ)
    (hτ : ∀ k, t₀ ≤ τ k) (hτS : ∀ k, τ k ≤ S)
    (hw : ∀ k, F05CompactDirichletSolution O A h p (τ k) (w k))
    (hConv : ∀ x ∈ closure O, ∀ t ∈ Icc r t₀,
      Tendsto (fun k => w k x t) atTop (𝓝 (W x t))) :
    ∀ x ∈ closure O, ∀ t ∈ Icc r t₀, W x t = u x t := by
  have hCoherent (k : ℕ) := by
    have hSub : Icc (0 : ℝ) (τ k) ⊆ Icc 0 S := Icc_subset_Icc le_rfl (hτS k)
    have hhK : MetricFamilySmooth h (Icc 0 (τ k)) :=
      fun x a b => (hh x a b).mono (prod_mono subset_rfl hSub)
    have hRK : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 (τ k)) :=
      fun x => (hR x).mono (prod_mono subset_rfl hSub)
    exact F05_compact_solution_coherent hA h p (w k) u ht₀ (hτ k) hhK hRK (hw k) hu
  intro x hx t ht
  have htFull : t ∈ Icc 0 t₀ := ⟨hr.trans ht.1,ht.2⟩
  have hConst : Tendsto (fun k => w k x t) atTop (𝓝 (u x t)) :=
    (tendsto_const_nhds (x := u x t)).congr'
      (Eventually.of_forall fun k => (hCoherent k x hx t htFull).symm)
  exact tendsto_nhds_unique (hConv x hx t ht) hConst

end Yau.Proofs.F05Aux
