import Yau.Proofs.C04RicciLowerBound
import Yau.Proofs.C04CenterWindows
import Yau.Proofs.C04SelectedWindows

/-! One common tail of the original selected windows has normalized central
scalar one and a uniformly positive actual Ricci minimum. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem central_window_sequence (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hCharts : UniformCharts X h) (hStatic : StaticDistortion X) :
    ∃ a b, 0 < a ∧ a < 1 ∧ 0 < b ∧
      (∃ T, ∀ t u, T ≤ t → 0 ≤ u → ρ o u = a * ρ o t →
        b * clockSpeed o h u ≤ ricciMin o h t) ∧
      ∃ S : ℕ → ℝ, ∃ K : ℝ, 1 ≤ K ∧ Tendsto S atTop atTop ∧
        (∀ i t u, 0 ≤ t → 0 ≤ u → ρ o t = 2 * S i → ρ o u = a * S i →
          clockSpeed o h t ≤ K * clockSpeed o h u) ∧
        ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
          (∀ i, 5 * S i / 4 ≤ ρ o (tw i) ∧ ρ o (tw i) ≤ 7 * S i / 4) ∧
          Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
            (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0) ∧
          ∃ lambda0, 0 < lambda0 ∧
            (∀ i, 0 < scalarCurvature (h (tw i)) o) ∧
            (∀ i (hR : 0 < scalarCurvature (h (tw i)) o),
              let g0 := scaleField (scalarCurvature (h (tw i)) o) hR (h (tw i))
              scalarCurvature g0 o = 1 ∧
                lambda0 ≤ relMinEigenvalue (gMat g0 o) (ricci g0 o)) := by
  obtain ⟨a, b, ha, ha1, hb, T, hmin⟩ := ricci_lower_bound X o h U P ρ hf hH hCharts hStatic
  obtain ⟨S, K, hKone, hSinf, hwindow, tw, htwpos, htwinf, hmiddle, hratio, hRpos, hRone⟩ :=
    selected_window_sequence X o h U P ρ hf hH ha ha1
  have hK : 0 < K := zero_lt_one.trans_le hKone
  obtain ⟨B, hB, hcenter⟩ := center_lower_of_good_window X o h U P ρ hf hH ha ha1 hb hK hmin
  obtain ⟨NS, hNS⟩ := (tendsto_atTop_atTop.1 hSinf) B
  obtain ⟨Nt, hNt⟩ := (tendsto_atTop_atTop.1 htwinf) T
  let N := max NS Nt
  let S' := fun i : ℕ => S (i + N)
  let tw' := fun i : ℕ => tw (i + N)
  have hshift : Tendsto (fun i : ℕ => i + N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  refine ⟨a, b, ha, ha1, hb, ⟨T, hmin⟩, S', K, hKone, hSinf.comp hshift,
    (fun i => hwindow (i + N)), tw', (fun i => htwpos (i + N)), htwinf.comp hshift,
    (fun i => hmiddle (i + N)), hratio.comp hshift, b / K, div_pos hb hK,
    (fun i => hRpos (i + N)), ?_⟩
  intro i hR
  refine ⟨hRone (i + N) hR, ?_⟩
  exact hcenter (S (i + N)) (tw (i + N))
    (hNS _ ((le_max_left NS Nt).trans (Nat.le_add_left N i)))
    (htwpos (i + N)) (hNt _ ((le_max_right NS Nt).trans (Nat.le_add_left N i)))
    (hmiddle (i + N)).1 (hmiddle (i + N)).2 (hwindow (i + N)) hR

end Yau.Proofs.C04Aux
