import spec.CHAIN.CONTRACTS

/-!
Planning-phase F4 regression: conditional assembly from the exact registered
producer contracts. No paper producer or unconditional endpoint is proved here.
The actual F01 flow, C07 charts, Y04 models and U02 map are selected below;
none of them is a caller-supplied replacement or an extra premise.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section

namespace Yau.Blueprint.EndpointAssemblyAttacks

open Yau Yau.Blueprint Yau.BlueprintContracts

variable {n : ℕ}

/-- Structural C05 inlet check, not a proof of simple connectivity.
Every component uses precisely F01's X/o/h/U/P/ρ witnesses. -/
theorem c05_inlet_from_exact_producers
    (hF01 : F01_contract) (hF04 : F04_contract)
    (hC01 : C01_contract) (hC04 : C04_contract) : C05InputProducer := by
  intro n X o
  obtain ⟨h, U, P, ρ, hflow⟩ := hF01 n X o
  exact ⟨h, U, P, ρ, ⟨hflow, hF04 n X o h U P ρ hflow⟩,
    hC01 n X o h U P ρ hflow, hC04 n X o h U P ρ hflow⟩

/-- Conditional assembly only: a proof of the reviewed C05 step remains an
explicit unproved input; this test applies it to the actual four contracts. -/
theorem c05_from_reviewed_step
    (hF01 : F01_contract) (hF04 : F04_contract)
    (hC01 : C01_contract) (hC04 : C04_contract)
    (hC05step : C05_step_contract) : C05_contract :=
  (hC05step hF01 hF04 hC01 hC04).2

/-- The clock used by U02 is the canonical grid produced by Y04, because
the returned time parameter is an actual inverse to this flow's volume clock.
This is an interface identity, not an independently chosen scalar clock. -/
theorem degree_on_actual_clock
    {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {time : ℝ → ℝ} {s₀ : ℝ} {s : ℕ → ℝ} {G : ℕ → PolyMap n} {hm : ℝ}
    (hclock : Alignment.ClockParameter X o h ρ time s₀)
    (hlate : ∀ k, s₀ ≤ s k) (hdegree : ForwardDegreeControl G s hm) :
    ForwardDegreeControl G (fun k => ρ o (time (s k))) hm := by
  have hsame : (fun k => ρ o (time (s k))) = s := by
    funext k
    exact (hclock.2.2.1 (s k) (hlate k)).2
  rw [hsame]
  exact hdegree

/-- Exact U05 incoming edge test. In particular, Y04's universal conditional
construction is used only AFTER extracting a genuine late regular start
from that very output's BadCharging clause. -/
theorem u05_from_exact_producers
    (hF01 : F01_contract) (hF04 : F04_contract) (hE03 : E03_contract)
    (hC04 : C04_contract) (hC07 : C07_contract) (hY04 : Y04_contract)
    (hU02 : U02_contract) (hU03 : U03_contract) : U05_contract := by
  intro n _hn X
  obtain ⟨o⟩ := (inferInstance : Nonempty (Pt X))
  obtain ⟨h, U, P, ρ, hflow⟩ := hF01 n X o
  have hstage : FlowStage X o h U P ρ := ⟨hflow, hF04 n X o h U P ρ hflow⟩
  have hwindows : RicciWindows X o h ρ := hC04 n X o h U P ρ hflow
  have hjoint : Alignment.JointPositiveClock X h := (hE03 n X o h U P ρ hflow).1
  obtain ⟨r₀, r₁, σ, C, Cb, t₀, Φ, F, f, hcharts⟩ :=
    hC07 n X o h U P ρ hstage
  -- The U02 jet order is chosen before Y04 fixes Cd and Dstar.
  obtain ⟨d, σ', γ', hd, _hγ, _hgap, _hσ, hwidth⟩ :=
    hU02 n X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hstage hwindows hcharts
  obtain ⟨Cd, Dstar, _hCd, _hDstar, hmodels⟩ := hY04 n d hd
  obtain ⟨time, s₀, a₀, b₀, hclock, _ha₀, _ha₁, _hb₀, _hrate, hgridModels⟩ :=
    hmodels X o h U P ρ r₀ r₁ σ C Cb t₀ Φ F f hstage hwindows hjoint hcharts
  -- Only now choose a width small enough for the U02 estimates.
  obtain ⟨h₀, hh₀, hh₀le, hglobal⟩ := hwidth Cd Dstar
  let hm := h₀ / 2
  have hhm : 0 < hm := by dsimp [hm]; linarith
  have hhm₀ : hm < h₀ := by dsimp [hm]; linarith
  have hhm₁ : hm < 1 := lt_of_lt_of_le hhm₀ hh₀le
  obtain ⟨N, M, _hN, _hNa, _hM, _hthreshold, _hsmall,
      jBound, _hjBoundN, _hclockBound, hcharging,
      scale, K, eps, b, _hscale, _hK, _heps, _hepsn, _hb,
      jLate, _hjLate, hstart⟩ := hgridModels hm hhm hhm₁
  obtain ⟨_hmono, _hpos, _hfull, _hprefix, _hnoInfinite, hregular, _hgood⟩ := hcharging
  obtain ⟨j₀, hj₀, hreg⟩ := hregular jLate
  obtain ⟨_hlayout, htimes, H, Hinv, G, Ginv, _g, _E, _L,
      hpolys, _hwindow, _hweights, _hcompat, _hmacroDegree, hdegree⟩ :=
    hstart j₀ ((le_max_left jLate jBound).trans hj₀) hreg
  let s := Alignment.gridClock (Alignment.sampledSpeed o h time hm) N M hm j₀
  let tk := fun k => time (s k)
  have hactualDegree : ForwardDegreeControl G (fun k => ρ o (tk k)) hm :=
    degree_on_actual_clock hclock (fun k => (htimes k).1) hdegree
  obtain ⟨Ψ, Ψinv, global, _hcoordinates, _hmap, _hinverse, himage⟩ :=
    hglobal hm hhm hhm₀ tk H Hinv G Ginv hpolys
      (Filter.Eventually.of_forall (fun k =>
        (hclock.2.2.1 (s k) (htimes k).1).1.le))
  -- U03 consumes the SAME G, clock and global returned above; out is indexed
  -- by that actual global and cannot be replaced by an unrelated map witness.
  obtain ⟨out⟩ := hU03 n X.manifold global G Ginv (fun k => ρ o (tk k))
    σ' γ' hm himage hactualDegree
  exact ⟨global, ⟨out⟩⟩

/-- Exact END incoming edge test. Existence now comes from U05, while U04
and I01 are instantiated on precisely its dependent global/out pair. -/
theorem end_from_exact_incoming_contracts
    (hU05 : U05_contract) (hU04 : U04_contract) (hI01 : I01_contract) : END_contract := by
  intro n hn X
  obtain ⟨global, ⟨out⟩⟩ := hU05 n hn X
  exact hI01 n X.manifold global out (hU04 n X.manifold global out)

/-- The whole existential/endpoint splice compiles with only the registered
producer premises and packaging goals. These are all still open assumptions. -/
theorem endpoint_from_exact_producers
    (hF01 : F01_contract) (hF04 : F04_contract) (hE03 : E03_contract)
    (hC04 : C04_contract) (hC07 : C07_contract) (hY04 : Y04_contract)
    (hU02 : U02_contract) (hU03 : U03_contract)
    (hU04 : U04_contract) (hI01 : I01_contract) : END_contract :=
  end_from_exact_incoming_contracts
    (u05_from_exact_producers hF01 hF04 hE03 hC04 hC07 hY04 hU02 hU03) hU04 hI01

/-- Retain both the exact surjectivity proof and pointwise identity of the
map constructed from it. The quantified original manifold is unchanged. -/
theorem same_map_endpoint_from_exact_incoming_contracts
    (hU05 : U05_contract) (hU04 : U04_contract) (hI01 : I01_contract)
    (n : ℕ) (hn : 1 ≤ n) (X : KahlerManifold n) :
    ∃ (global : Uniformization.OpenCoordinateData n X.manifold) (out : U03Output global),
      U04 global out ∧ BiholomorphicToComplexEuclidean X.manifold ∧
      global.image = Set.univ ∧
      (global.toGlobal out.1).manifold = X.manifold ∧
      ∀ x : Pt X, (global.toGlobal out.1).diffeomorph x = global.map x := by
  obtain ⟨global, ⟨out⟩⟩ := hU05 n hn X
  have hpack := hU04 n X.manifold global out
  exact ⟨global, out, hpack, hI01 n X.manifold global out hpack,
    out.1, rfl, fun _ => rfl⟩

/-! A concrete check on the danger of ignoring Y04's existence clause.
For this exponential scalar sequence every macro is bad. Universal statements
conditioned on Regular therefore hold vacuously, but BadCharging rejects it.
This is a scalar counterexample only, not a geometric flow countermodel. -/

def allBadSpeed (j : ℕ) : ℝ := Real.exp (2 * (j : ℝ))

theorem all_macros_bad (j : ℕ) : Alignment.Bad allBadSpeed 1 1 j := by
  refine ⟨j + 1, ⟨by omega, ?_⟩, by omega, by omega⟩
  simp only [allBadSpeed, Real.log_exp]
  push_cast
  linarith

theorem conditional_regular_start_can_be_vacuous :
    (∀ j, Alignment.Regular allBadSpeed 1 1 j →
      Alignment.GridLayout allBadSpeed 1 1 (1 / 2) j) ∧
      ¬ ∃ j, Alignment.Regular allBadSpeed 1 1 j := by
  constructor
  · intro j hreg
    exact False.elim (hreg (all_macros_bad j))
  · rintro ⟨j, hreg⟩
    exact hreg (all_macros_bad j)

theorem actual_charging_rejects_vacuous_start (jBound Dstar : ℕ) (hm b₀ : ℝ) :
    ¬ Alignment.BadCharging allBadSpeed jBound 1 Dstar 1 hm b₀ := by
  intro h
  obtain ⟨j, _hj, hreg⟩ := h.2.2.2.2.2.1 0
  exact hreg (all_macros_bad j)

#check (U03_contract : Prop)
#check (U04_contract : Prop)
#check (U05_contract : Prop)
#print axioms degree_on_actual_clock
#print axioms u05_from_exact_producers
#print axioms end_from_exact_incoming_contracts
#print axioms endpoint_from_exact_producers
#print axioms same_map_endpoint_from_exact_incoming_contracts
#print axioms all_macros_bad
#print axioms conditional_regular_start_can_be_vacuous
#print axioms actual_charging_rejects_vacuous_start

end Yau.Blueprint.EndpointAssemblyAttacks
