import Yau.Proofs.F01NativeBackwardPotentialJets
import Yau.Proofs.F01ClockCenterHolderPatching

/-! Every potential jet has a common Holder modulus on the genuine
open terminal interval. The amplitude and spatial scale stay fixed
while the backward clock center varies. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem partial_native_potential_jet_holder
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tstar C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTstar : 0 ≤ Tstar) (hC : 1 ≤ C)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hEarly : ρ ^ 2 ≤ Tstar - (ρ * (1 / 4)) ^ 2 / 4) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ),
      (∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T)) →
      (∀ x, U x 0 = 0) →
      (∀ s ∈ Ico 0 Tstar, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
        HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Ico 0 Tstar →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ (a : M.Carrier) (k : ℕ),
      let σ := ρ * (1 / 4)
      HolderBound (min α β) (ball 0 (1 / 2) ×ˢ Ioo (Tstar - σ ^ 2 / 4) Tstar)
        (fun p => iteratedFDeriv ℝ k
          (fun z => (σ ^ 2)⁻¹ * U ((A.chart a) (σ • z)) p.2) p.1) (B k) := by
  let σ : ℝ := ρ * (1 / 4)
  have hσ : 0 < σ := mul_pos hρ (by norm_num)
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  let I : Set ℝ := Ioo (Tstar - σ ^ 2 / 4) Tstar
  obtain ⟨K, hK, hNative⟩ := native_backward_potential_jet_budgets g hg A hρ hρr hρ1
    hTstar hC hα hα1 hβ hβ1
  refine ⟨fun k => (1 + (σ ^ 2)⁻¹ ^ (min α β / 2)) * K k,
    fun k => mul_pos (by positivity) (hK k), ?_⟩
  intro h U hU hU0 hpot hpde hflow a k
  dsimp only
  change HolderBound (min α β) (ball 0 (1 / 2) ×ˢ I)
    (fun p => iteratedFDeriv ℝ k
      (fun z => (σ ^ 2)⁻¹ * U ((A.chart a) (σ • z)) p.2) p.1) _
  apply holder_from_common_backward_clock_patches (ball 0 (1 / 2)) I
    (fun p => iteratedFDeriv ℝ k (fun z => (σ ^ 2)⁻¹ * U ((A.chart a) (σ • z)) p.2) p.1)
    hσ2 (R := 1 / 2) (by norm_num) (hK k).le
  · intro s hs t ht
    exact ⟨hs.1.trans_le (le_max_left _ _), max_lt hs.2 ht.2⟩
  · intro s hs t ht
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  · intro τ hτ
    have hLower : ρ ^ 2 ≤ τ := hEarly.trans (le_of_lt hτ.1)
    have hNonneg : 0 ≤ τ := (sq_nonneg ρ).trans hLower
    have hSub : Icc 0 τ ⊆ Ico 0 Tstar := fun s hs => ⟨hs.1, hs.2.trans_lt hτ.2⟩
    have hh := hNative k h U τ τ hτ.2.le hLower le_rfl
      (hU τ hNonneg hτ.2) hU0
      (fun s hs x => hpot s (hSub hs) x) (hpde τ hNonneg hτ.2)
      (fun x s hs => hflow x s (hSub hs)) a
    simpa only [σ, cylinder, shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
      affineParabolicPoint, add_zero] using hh

end Yau.NodeProofs.F01Aux
