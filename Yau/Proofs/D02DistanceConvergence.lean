import Yau.Proofs.D02CotangentCompact

/-! Uniform convergence and compact centre sets for the same computed
length distance used in the frozen D02 statement. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- The metric-space uniform convergence interface is the frozen lengthEDist interface. -/
theorem tendstoUniformlyOn_lengthEDist_iff (g : SmoothMetric M)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier) (L : Set ℂ) :
    letI := Yau.LeafProofs.L12Aux.inducedMetricSpace g
    TendstoUniformlyOn fs f atTop L ↔
      ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∀ ζ ∈ L, lengthEDist g.form (fs k ζ) (f ζ) < ε := by
  letI := Yau.LeafProofs.L12Aux.inducedMetricSpace g
  have he (x y : M.Carrier) : edist x y = lengthEDist g.form x y := by
    rw [edist_dist]
    rfl
  rw [EMetric.tendstoUniformlyOn_iff]
  simp only [he, eventually_atTop, lengthEDist, g.induced_distance_symm]

/-- If every admissible sequence has a converging extracted centre, all
centres lie in one actual compact metric ball. -/
theorem compact_centres_of_subsequence (g : SmoothMetric M)
    (P : (ℂ → M.Carrier) → Prop)
    (hseq : ∀ fs : ℕ → ℂ → M.Carrier, (∀ j, P (fs j)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : M.Carrier,
        ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          lengthEDist g.form (fs (φ k) 0) x < ε) :
    ∃ K : Set M.Carrier, IsCompact K ∧ ∀ f : ℂ → M.Carrier, P f → f 0 ∈ K := by
  classical
  let o : M.Carrier := Classical.choice (inferInstance : Nonempty M.Carrier)
  have hbounded : ∃ R : ℝ, ∀ f : ℂ → M.Carrier, P f → inducedDistance g.form o (f 0) ≤ R := by
    by_contra h
    push Not at h
    choose fs hp hlarge using fun j : ℕ => h (j : ℝ)
    obtain ⟨φ, hφ, x, hconv⟩ := hseq fs hp
    obtain ⟨N, hN⟩ := hconv (ENNReal.ofReal 1) (by simp)
    obtain ⟨J, hJ⟩ := exists_nat_gt (inducedDistance g.form o x + 1)
    let k := max N J
    have hNk : N ≤ k := le_max_left _ _
    have hJk : J ≤ k := le_max_right _ _
    have hclose : inducedDistance g.form (fs (φ k) 0) x < 1 :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp (hN k hNk)
    have htriangle := g.induced_distance_triangle o x (fs (φ k) 0)
    rw [g.induced_distance_symm x (fs (φ k) 0)] at htriangle
    have hcast : (J : ℝ) ≤ (φ k : ℝ) :=
      Nat.cast_le.mpr (hJk.trans (hφ.id_le k))
    have hfar := hlarge (φ k)
    linarith
  obtain ⟨R, hR⟩ := hbounded
  exact ⟨{x | inducedDistance g.form o x ≤ R},
    Yau.LeafProofs.L12Aux.isCompact_inducedDistance_sublevel g o R, hR⟩

end Yau.NodeProofs.D02Aux
