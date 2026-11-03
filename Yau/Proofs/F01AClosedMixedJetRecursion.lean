import Yau.Proofs.F01AQuantitativeJetRecursion

/-! The quantitative finite-jet recursion retains both closed time faces.
It uses actual within clock derivatives and never extends the potential to
negative times. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteState_hasDerivWithinAt_of_clock
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {I : Set ℝ} (p : E × ℝ)
    (hClock : ∀ j, HasDerivWithinAt (fun t => J j (p.1, t))
      (prolong F j (stateJ J j p)) I p.2) (k : ℕ) :
    HasDerivWithinAt (fun t => stateJ J k (p.1, t))
      (finiteClockTimeDirection F k (stateJ J (k + 2) p)) I p.2 := by
  have hBase : HasDerivWithinAt (fun t : ℝ => (p.1, t)) ((0 : E), 1) I p.2 :=
    (hasDerivWithinAt_const p.2 I p.1).prodMk (hasDerivWithinAt_id p.2 I)
  exact hBase.prodMk (hasDerivWithinAt_pi.mpr (fun j => hClock j.val))

/-- Every iterated within clock derivative of the actual spatial state is
the computed finite-jet expression, including the original closed faces. -/
theorem finiteMixedClockJet_actualWithin
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {I : Set ℝ} (hI : UniqueDiffOn ℝ I) {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (x : E)
    (hState : ∀ t ∈ I, stateJ J 0 (x, t) ∈ D)
    (hClock : ∀ j t, t ∈ I → HasDerivWithinAt (fun s => J j (x, s))
      (prolong F j (stateJ J j (x, t))) I t)
    (a b : ℕ) : ∀ t ∈ I,
      iteratedDerivWithin a (fun s => J b (x, s)) I t =
        finiteMixedClockJet F b a (stateJ J (mixedClockJetOrder a b) (x, t)) := by
  induction a with
  | zero => intro t ht; rfl
  | succ a ih =>
      intro t ht
      have hMem : stateJ J (mixedClockJetOrder a b) (x, t) ∈
          prolongDomain D (mixedClockJetOrder a b) := hState t ht
      have hDiff := ((finiteMixedClockJet_contDiffOn hD hF a b).contDiffAt
        ((prolongDomain_isOpen hD _).mem_nhds hMem)).differentiableAt (by simp)
      have hDerivative := hDiff.hasFDerivAt.comp_hasDerivWithinAt t
        (finiteState_hasDerivWithinAt_of_clock J F (x, t)
          (fun j => hClock j t ht) (mixedClockJetOrder a b))
      have hActual := hDerivative.congr_of_mem (fun s hs => ih s hs) ht
      rw [iteratedDerivWithin_succ]
      exact hActual.derivWithin (hI t ht)

/-- One compact range of spatial jets gives one mixed derivative bound for
all actual solutions on the same closed slab. -/
theorem actual_closed_mixed_clock_jets_uniformly_bounded
    {ι : Type*} (J : ι → (j : ℕ) → E × ℝ → Jet E ℝ j)
    (F : State E 0 → ℝ) {S : Set E} {I : Set ℝ} (hI : UniqueDiffOn ℝ I)
    {D : Set (State E 0)} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : ∀ i, MapsTo (stateJ (J i) 0) (S ×ˢ I) D)
    (hClock : ∀ i j p, p ∈ S ×ˢ I → HasDerivWithinAt (fun t => J i j (p.1, t))
      (prolong F j (stateJ (J i) j p)) I p.2)
    (a b : ℕ) {Q : Set (E × ℝ)} (hQ : Q ⊆ S ×ˢ I)
    {K : Set (State E (mixedClockJetOrder a b))} (hK : IsCompact K)
    (hKD : K ⊆ prolongDomain D (mixedClockJetOrder a b))
    (hRange : ∀ i p, p ∈ Q → stateJ (J i) (mixedClockJetOrder a b) p ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedDerivWithin a (fun t => J i b (p.1, t)) I p.2‖ ≤ B := by
  obtain ⟨B, hB, hBound⟩ := finiteMixedClockJet_compact_bound hD hF a b hK hKD
  refine ⟨B, hB, ?_⟩
  intro i p hp
  rw [finiteMixedClockJet_actualWithin (J i) F hI hD hF p.1
    (fun t ht => hState i ⟨(hQ hp).1, ht⟩)
    (fun j t ht => hClock i j (p.1, t) ⟨(hQ hp).1, ht⟩) a b p.2 (hQ hp).2]
  exact hBound _ (hRange i p hp)

end Yau.NodeProofs.F01Aux
