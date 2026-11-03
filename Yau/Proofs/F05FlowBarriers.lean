import Yau.Proofs.F04Source
import Yau.Proofs.F02InitialRicci
import Yau.Proofs.F05InitialData

/-! Actual barriers and initial-face compatibility on the supplied localized flow. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.F05Aux

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem flow_source_nonneg (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) :
    0 ≤ Yau.F04Proof.source X h x t := by
  apply F02Aux.traceWith_nonneg
  · exact (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  · exact F02Aux.initialRicci_posSemidef X o h U P ρ hloc x

theorem smoothFn_slice {I : Set ℝ} {u : STF X} (hu : SmoothSpaceTime u I)
    {t : ℝ} (ht : t ∈ I) : SmoothFn (fun x => u x t) := by
  intro x
  exact (hu x).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)

theorem rho_laplacian_le_scalar (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S : ℝ) (hS : 0 < S)
    (x : Pt X) (t : ℝ) (ht : t ∈ Set.Icc 0 S) :
    laplacian (h t) (fun y => ρ y t) x ≤ scalarCurvature (h t) x := by
  have heq := Yau.F04Proof.rho_source_equation o h U P ρ hloc S hS x t ht
  rw [heatOp, Yau.F04Proof.rho_derivWithin_Icc o h U P ρ hloc S hS x t ht] at heq
  have hnonneg := flow_source_nonneg o h U P ρ hloc x t
  linarith

theorem shifted_rho_supersolution (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S : ℝ) (hS : 0 < S) (c : ℝ)
    (x : Pt X) (t : ℝ) (ht : t ∈ Set.Icc 0 S) :
    scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => ρ y t + c) x) (ρ x t + c) ≤
        derivWithin (fun s => ρ x s + c) (Set.Icc 0 S) t := by
  have hρsmooth : SmoothFn (fun y => ρ y t) := smoothFn_slice hloc.2.2.2.1 ht.1
  rw [LeafProofs.L18Aux.laplacian_add_const (h t) hρsmooth c x]
  have hderiv := ((Yau.F04Proof.rho_hasDerivWithinAt_Icc o h U P ρ hloc S x t ht).add_const c).derivWithin
    (uniqueDiffOn_Icc hS t ht)
  rw [hderiv]
  exact scalarNonlinearRHS_le_scalar _ _ _ (rho_laplacian_le_scalar o h U P ρ hloc S hS x t ht)

theorem bounded_subsolution_initial_zero (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) (hT : 0 ≤ T) (v : STF X)
    (hbound : ∀ x t, t ∈ Set.Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t) (x : Pt X) :
    v x 0 = 0 := by
  have hv := hbound x 0 ⟨le_rfl, hT⟩
  rw [Yau.F04Proof.rho_initial o h U P ρ hloc x] at hv
  linarith

def flowCornerBoundary (X : KahlerManifold n) (ρ : STF X) (α δ : ℝ) (ζ : ℝ → ℝ) : STF X :=
  fun x t => cornerBoundary (ρ x) α (scalarCurvature X.metric.form x) δ ζ t

theorem flowCornerBoundary_initial (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (α δ : ℝ) (ζ : ℝ → ℝ) (x : Pt X) :
    flowCornerBoundary X ρ α δ ζ x 0 = α :=
  cornerBoundary_initial _ _ _ _ _ (Yau.F04Proof.rho_initial o h U P ρ hloc x)

theorem flowCornerBoundary_initial_derivative (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (α δ : ℝ) (ζ : ℝ → ℝ)
    (hζ : ζ =ᶠ[𝓝 0] (fun _ => 1)) (x : Pt X) :
    HasDerivWithinAt (flowCornerBoundary X ρ α δ ζ x)
      ((1 - Real.exp (-α)) * scalarCurvature X.metric.form x) (Set.Ici 0) 0 := by
  apply cornerBoundary_hasDerivWithinAt
  · simpa only [hloc.1.1] using Yau.F04Proof.rho_hasDerivWithinAt o h U P ρ hloc x 0 le_rfl
  · exact hζ

end Yau.Proofs.F05Aux
