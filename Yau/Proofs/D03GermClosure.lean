import Yau.Proofs.D03GermJets
import Yau.LeafProofs.L25

noncomputable section

open Filter Topology

namespace Yau.Proofs.D03Aux

/-- Closed finite jet images and the actual Krull theorem imply membership in
an arbitrary analytic-germ submodule. The ambient module is finite free. -/
theorem mem_of_tendsto_all_jets
    (hKrull : Yau.LeafObligations.L25)
    (q : ℕ) (S : Submodule AnalyticGerm (Fin q → AnalyticGerm))
    (gseq : ℕ → Fin q → AnalyticGerm) (g : Fin q → AnalyticGerm)
    (hmem : ∀ n, gseq n ∈ S)
    (hjets : ∀ k, Tendsto (fun n => jet q k (gseq n)) atTop (𝓝 (jet q k g))) :
    g ∈ S := by
  let Q := (Fin q → AnalyticGerm) ⧸ S
  let π : (Fin q → AnalyticGerm) →ₗ[AnalyticGerm] Q := S.mkQ
  have hpow : ∀ k : ℕ,
      π g ∈ germMaximalIdeal ^ k • (⊤ : Submodule AnalyticGerm Q) := by
    intro k
    let J : Submodule ℂ (Jet q k) := (S.restrictScalars ℂ).map (jet q k)
    have : FiniteDimensional ℂ (Jet q k) := Module.Finite.pi
    have : FiniteDimensional ℂ J :=
      FiniteDimensional.of_injective J.subtype Subtype.val_injective
    have hclosed : IsClosed (J : Set (Jet q k)) := J.closed_of_finiteDimensional
    have hn : ∀ᶠ n in atTop, jet q k (gseq n) ∈ J := by
      exact Eventually.of_forall fun n => Submodule.mem_map_of_mem (hmem n)
    have hgJ : jet q k g ∈ J := hclosed.mem_of_tendsto (hjets k) hn
    obtain ⟨s, hs, hsj⟩ := Submodule.mem_map.mp hgJ
    have hzero : jet q k (g - s) = 0 := by rw [map_sub, hsj, sub_self]
    obtain ⟨h, hgh⟩ := (jet_eq_zero_iff q k (g - s)).mp hzero
    have hs0 : π s = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hs
    have heq : π g = zGerm ^ k • π h := by
      have hm := congrArg π hgh
      simpa only [map_sub, map_smul, hs0, sub_zero] using hm
    rw [heq, germMaximalIdeal_eq_span, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mem_pointwise_smul (π h) (zGerm ^ k) ⊤ Submodule.mem_top
  have hinter : π g ∈
      (⨅ k : ℕ, germMaximalIdeal ^ k • (⊤ : Submodule AnalyticGerm Q)) :=
    (Submodule.mem_iInf _).mpr hpow
  have hbot := hKrull AnalyticGerm Q germMaximalIdeal germMaximalIdeal_ne_top
  rw [hbot] at hinter
  have hzero : π g = 0 := by simpa only [Submodule.mem_bot] using hinter
  apply (Submodule.Quotient.mk_eq_zero S).mp
  rw [← Submodule.mkQ_apply]
  exact hzero

/-- Unconditional discharge by the accepted L25 theorem. -/
theorem mem_of_tendsto_all_jets_proved
    (q : ℕ) (S : Submodule AnalyticGerm (Fin q → AnalyticGerm))
    (gseq : ℕ → Fin q → AnalyticGerm) (g : Fin q → AnalyticGerm)
    (hmem : ∀ n, gseq n ∈ S)
    (hjets : ∀ k, Tendsto (fun n => jet q k (gseq n)) atTop (𝓝 (jet q k g))) :
    g ∈ S :=
  mem_of_tendsto_all_jets Yau.LeafProofs.L25 q S gseq g hmem hjets

end Yau.Proofs.D03Aux
