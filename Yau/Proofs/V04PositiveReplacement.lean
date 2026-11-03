import Yau.Proofs.V04PositiveReplacementWeighted

/-! The original positive replacement, with the same frame and the
original order epsilon then sequence. No energy-smallness input is used. -/
open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem positiveReplacement {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {a : ℕ} (ha : 4 ≤ a)
    (hsymbol : SymbolBounds d a) : PositiveReplacement d k a := by
  intro j
  obtain ⟨W, hW, hweight⟩ := fixed_index_clock_boundary_weight_bound hd hk j a
  obtain ⟨L, hL, hbound⟩ := fixed_index_weighted_replacement_bound hd hk ha hsymbol j
  let C : ℝ := W * L
  have hC : 0 ≤ C := mul_nonneg hW hL
  refine ⟨C, hC, fun δ hδ hδ1 F E hF hnegative r hr => ?_⟩
  have hsmall := hnegative (r / (C + 1)) (div_pos hr (by positivity))
  have hεpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hεle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hF, hsmall, hεpos, hεle] with ε hF hsmall hεpos hεle
  filter_upwards [hweight ε hεpos hεle (F ε) hF.1, hsmall] with ν hweight hsmall
  have hb := hbound hδ hδ1 (F ε ν) (E ε ν) (hF.1.1 ν) (hF.2 ν) hW hweight
  have hn : negativeTrace d j a (F ε ν) (E ε ν) 1 ≤ r / (C + 1) :=
    (le_abs_self _).trans hsmall
  have hprod : C * negativeTrace d j a (F ε ν) (E ε ν) 1 ≤ r := by
    have hmul := mul_le_mul_of_nonneg_left hn hC
    have haux : C * (r / (C + 1)) ≤ r := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
      nlinarith
    exact hmul.trans haux
  calc
    _ ≤ C * (negativeTrace d j a (F ε ν) (E ε ν) 1 + δ) := hb
    _ ≤ C * δ + r := by nlinarith

end Yau.Blueprint.V04Proof.PositiveReplacementAux
