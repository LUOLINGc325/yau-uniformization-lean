import Yau.LeafProofs.L17BootstrapEvolutionJetsProlong
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Quantitative time prolongation of the proved finite spatial-jet clock.
Every mixed clock jet is computed from finitely many spatial jets. A compact
positive jet range therefore gives one bound before the solution index. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restriction keeps the base point and the actual low spatial jets. -/
def clockRestrictState {m r : ℕ} (h : m ≤ r) : State E r →L[ℝ] State E m :=
  (ContinuousLinearMap.id ℝ (E × ℝ)).prodMap (restrictPack E (by omega))

@[simp] theorem projectBaseState_clockRestrictState {m r : ℕ} (h : m ≤ r) (s : State E r) :
    projectBaseState E m (clockRestrictState h s) = projectBaseState E r s := rfl

theorem clockRestrictState_mapsTo (D : Set (State E 0)) {m r : ℕ} (h : m ≤ r) :
    MapsTo (clockRestrictState (E := E) h) (prolongDomain D r) (prolongDomain D m) := by
  intro s hs
  exact hs

/-- The genuine clock vector of the spatial finite state. Its jet components
are the already computed spatial prolongations of the scalar clock map. -/
def finiteClockTimeDirection (F : State E 0 → ℝ) (k : ℕ) (s : State E (k + 2)) : State E k :=
  ((0, 1), fun j => prolong F j.val (clockRestrictState (by omega : j.val ≤ k + 2) s))

theorem finiteClockTimeDirection_contDiffOn {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (k : ℕ) :
    ContDiffOn ℝ ∞ (finiteClockTimeDirection F k) (prolongDomain D (k + 2)) := by
  apply contDiffOn_const.prodMk
  apply contDiffOn_pi.mpr
  intro j
  exact (prolong_contDiffOn hD hF j.val).comp
    (clockRestrictState (E := E) (m := j.val) (r := k + 2) (by omega)).contDiff.contDiffOn
    (clockRestrictState_mapsTo D _)

def mixedClockJetOrder : ℕ → ℕ → ℕ
  | 0, b => b
  | a + 1, b => mixedClockJetOrder a b + 2

theorem mixedClockJetOrder_eq (a b : ℕ) : mixedClockJetOrder a b = b + 2 * a := by
  induction a with
  | zero => simp [mixedClockJetOrder]
  | succ a ih => simp only [mixedClockJetOrder, ih]; omega

/-- The explicit finite-jet recursion for a clock derivatives of the spatial
b-jet. The two extra orders in State are retained throughout. -/
def finiteMixedClockJet (F : State E 0 → ℝ) (b : ℕ) :
    (a : ℕ) → State E (mixedClockJetOrder a b) → Jet E ℝ b
  | 0 => fun s => s.2 ⟨b, by simp only [mixedClockJetOrder]; omega⟩
  | a + 1 => fun s =>
      fderiv ℝ (finiteMixedClockJet F b a)
        (clockRestrictState (Nat.le_add_right _ 2) s)
        (finiteClockTimeDirection F (mixedClockJetOrder a b) s)

theorem finiteMixedClockJet_contDiffOn {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (a b : ℕ) :
    ContDiffOn ℝ ∞ (finiteMixedClockJet F b a) (prolongDomain D (mixedClockJetOrder a b)) := by
  induction a with
  | zero =>
      let L : State E b →L[ℝ] Jet E ℝ b :=
        (ContinuousLinearMap.proj ⟨b, by omega⟩).comp
          (ContinuousLinearMap.snd ℝ (E × ℝ) (JetPack E (b + 2)))
      exact L.contDiff.contDiffOn
  | succ a ih =>
      have hd := ih.fderiv_of_isOpen (prolongDomain_isOpen hD _) (m := ∞) (by simp)
      exact (hd.comp
        (clockRestrictState (Nat.le_add_right (mixedClockJetOrder a b) 2)).contDiff.contDiffOn
        (clockRestrictState_mapsTo D _)).clm_apply
        (finiteClockTimeDirection_contDiffOn hD hF _)

@[simp] theorem clockRestrictState_stateJ
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) {m r : ℕ} (h : m ≤ r) (p : E × ℝ) :
    clockRestrictState h (stateJ J r p) = stateJ J m p := rfl

theorem finiteState_hasDerivAt_of_clock
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {W : Set (E × ℝ)}
    (hClock : ∀ j p, p ∈ W → HasDerivAt (fun t => J j (p.1, t))
      (prolong F j (stateJ J j p)) p.2)
    (k : ℕ) {p : E × ℝ} (hp : p ∈ W) :
    HasDerivAt (fun t => stateJ J k (p.1, t))
      (finiteClockTimeDirection F k (stateJ J (k + 2) p)) p.2 := by
  have hBase : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : E), 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact hBase.prodMk (hasDerivAt_pi.mpr (fun j => hClock j.val p hp))

/-- Identity on actual mixed derivatives. Only the original finite spatial
clock equations occur as premises; no higher clock jets are supplied. -/
theorem finiteMixedClockJet_actual
    (J : (j : ℕ) → E × ℝ → Jet E ℝ j) (F : State E 0 → ℝ)
    {W : Set (E × ℝ)} (hW : IsOpen W) {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : MapsTo (stateJ J 0) W D)
    (hClock : ∀ j p, p ∈ W → HasDerivAt (fun t => J j (p.1, t))
      (prolong F j (stateJ J j p)) p.2)
    (a b : ℕ) : ∀ p ∈ W,
      iteratedDeriv a (fun t => J b (p.1, t)) p.2 =
        finiteMixedClockJet F b a (stateJ J (mixedClockJetOrder a b) p) := by
  induction a with
  | zero => intro p hp; rfl
  | succ a ih =>
      intro p hp
      have hMem : stateJ J (mixedClockJetOrder a b) p ∈
          prolongDomain D (mixedClockJetOrder a b) := hState hp
      have hDiff := ((finiteMixedClockJet_contDiffOn hD hF a b).contDiffAt
        ((prolongDomain_isOpen hD _).mem_nhds hMem)).differentiableAt (by simp)
      have hDerivative := hDiff.hasFDerivAt.comp_hasDerivAt p.2
        (finiteState_hasDerivAt_of_clock J F hClock (mixedClockJetOrder a b) hp)
      have hEq : (fun t => iteratedDeriv a (fun s => J b (p.1, s)) t) =ᶠ[𝓝 p.2]
          (fun t => finiteMixedClockJet F b a
            (stateJ J (mixedClockJetOrder a b) (p.1, t))) := by
        have hN : {t : ℝ | (p.1, t) ∈ W} ∈ 𝓝 p.2 :=
          (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
        filter_upwards [hN] with t ht
        exact ih (p.1, t) ht
      rw [iteratedDeriv_succ, hEq.deriv_eq]
      exact hDerivative.deriv

/-- Compactness turns the computed mixed-jet map into a bound selected before
every member of any family whose actual spatial state lies in this range. -/
theorem finiteMixedClockJet_compact_bound {F : State E 0 → ℝ} {D : Set (State E 0)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D) (a b : ℕ)
    {K : Set (State E (mixedClockJetOrder a b))} (hK : IsCompact K)
    (hKD : K ⊆ prolongDomain D (mixedClockJetOrder a b)) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ K, ‖finiteMixedClockJet F b a s‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((finiteMixedClockJet_contDiffOn hD hF a b).continuousOn.mono hKD)
  exact ⟨max 1 B + 1, by positivity,
    fun s hs => (hB s hs).trans (by linarith [le_max_right (1 : ℝ) B])⟩

theorem actual_mixed_clock_jets_uniformly_bounded
    {ι : Type*} (J : ι → (j : ℕ) → E × ℝ → Jet E ℝ j)
    (F : State E 0 → ℝ) {W : Set (E × ℝ)} (hW : IsOpen W)
    {D : Set (State E 0)} (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F D)
    (hState : ∀ i, MapsTo (stateJ (J i) 0) W D)
    (hClock : ∀ i j p, p ∈ W → HasDerivAt (fun t => J i j (p.1, t))
      (prolong F j (stateJ (J i) j p)) p.2)
    (a b : ℕ) {Q : Set (E × ℝ)} (hQW : Q ⊆ W)
    {K : Set (State E (mixedClockJetOrder a b))} (hK : IsCompact K)
    (hKD : K ⊆ prolongDomain D (mixedClockJetOrder a b))
    (hRange : ∀ i p, p ∈ Q → stateJ (J i) (mixedClockJetOrder a b) p ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ Q →
      ‖iteratedDeriv a (fun t => J i b (p.1, t)) p.2‖ ≤ B := by
  obtain ⟨B, hB, hBound⟩ := finiteMixedClockJet_compact_bound hD hF a b hK hKD
  refine ⟨B, hB, ?_⟩
  intro i p hp
  rw [finiteMixedClockJet_actual (J i) F hW hD hF (hState i) (hClock i) a b p (hQW hp)]
  exact hBound _ (hRange i p hp)

end Yau.NodeProofs.F01Aux
