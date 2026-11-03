import Yau.Proofs.F01ActualTerminalRestart

/-! The exact finite native potential tuple returned by the proved
short-time theorem. This definition only records actual metric fields,
potentials, orders and derivatives on their stated closed interval. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def NativePotentialTuple (g : HermitianField M) (T C : ℝ)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) : Prop :=
  1 ≤ C ∧ h 0 = g ∧ MetricFamilySmooth h (Icc 0 T) ∧ SmoothSpaceTime U (Icc 0 T) ∧
  (∀ x, U x 0 = 0) ∧ ∀ x t, t ∈ Icc 0 T →
    (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
    ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef ∧
    gMat (h t) x = gMat g x - (t : ℂ) • ricci g x + levi (fun y => U y t) x ∧
    HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Icc 0 T) t

theorem exists_native_short_time_tuple
    (g : HermitianField M) (hg : MetricSmooth g)
    (hComplete : IsCompleteDistance (inducedDistance g))
    (hBG : Yau.LeafCandidates.HermitianBoundedGeometry g) :
    ∃ (T C : ℝ) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ),
      0 < T ∧ NativePotentialTuple g T C h U := by
  obtain ⟨T, C, hT, hC, h, U, hh0, hh, hU, hU0, hData⟩ :=
    Yau.LeafProofs.L17 n M g hg hComplete hBG
  exact ⟨T, C, h, U, hT, hC, hh0, hh, hU, hU0, hData⟩

theorem NativePotentialTuple.restrict
    {g : HermitianField M} {T S C : ℝ} {h : ℝ → HermitianField M}
    {U : M.Carrier → ℝ → ℝ} (hTuple : NativePotentialTuple g T C h U)
    (hST : S ≤ T) : NativePotentialTuple g S C h U := by
  obtain ⟨hC, hh0, hh, hU, hU0, hData⟩ := hTuple
  have hSub : Icc 0 S ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans hST⟩
  refine ⟨hC, hh0, (fun a i j => (hh a i j).mono (prod_mono Subset.rfl hSub)),
    (fun a => (hU a).mono (prod_mono Subset.rfl hSub)), hU0, ?_⟩
  intro x t ht
  have hx := hData x t (hSub ht)
  exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.mono hSub⟩

end Yau.NodeProofs.F01Aux
