import Yau.Proofs.F01NativeBackwardAllSpatialSchauder
import Yau.Proofs.F01AllPotentialSpatialJetHolder

/-! Every full spatial jet of the same genuine native potential has
a common parabolic Holder budget on the fixed closed backward core.
Orders zero and one come from the actual closed-face Schauder estimate. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem native_backward_potential_jet_budgets
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧
      ∀ k (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      SmoothSpaceTime U (Icc 0 T) → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) → ∀ a : M.Carrier,
      HolderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0)
        (fun p => iteratedFDeriv ℝ k
          (fun z => shiftedNativePotential A U a (ρ * (1 / 4)) τ (z, p.2)) p.1) (K k) := by
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  have hδ1 : δ < 1 := (min_le_left α β).trans_lt hα1
  obtain ⟨Ci, hCi, hInitial⟩ := backward_native_schauder g hg A hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  obtain ⟨Cu, hCu, hWords⟩ := native_backward_all_spatial_schauder g hg A
    hρ hρr hρ1 hTcap hC hα hα1 hβ hβ1
  obtain ⟨K, hK, hBudget⟩ := all_potential_spatial_jet_holder_budgets (n := n)
    (by positivity : 0 < 16 * Ci) hδ1.le Cu hCu
  refine ⟨K, hK, ?_⟩
  intro k h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσρ : σ ≤ ρ := by dsimp only [σ]; linarith [hρ.le]
  have hσr : σ ≤ A.radius := hσρ.trans hρr
  have hσLower : σ ^ 2 ≤ τ := by
    have hh : σ ^ 2 ≤ ρ ^ 2 := by dsimp only [σ]; nlinarith [sq_nonneg ρ]
    exact hh.trans hLower
  let V := shiftedNativePotential A U a σ τ
  have hV := shifted_backward_native_potential_smooth A U hσ hσr hσLower hUpper hU a
  have hInit : SchauderBound δ (cylinder (ball 0 1) (-1) 0) V (16 * Ci) :=
    shifted_native_quarter_schauder A U a ρ τ hδ.le
      (hInitial h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a)
  have hBase : SchauderBound δ (cylinder (ball 0 (1 / 2)) (-(1 / 2)) 0) V (16 * Ci) :=
    schauderBound_closed_cylinder_restrict (by norm_num)
      (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) hInit
  exact hBudget V
    (fun t ht => (contDiffOn_space_slice hV ⟨by linarith [ht.1], ht.2⟩).mono
      (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))) hBase
    (fun i ws hws => hWords ws.length h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a i ws hws rfl) k

end Yau.NodeProofs.F01Aux
