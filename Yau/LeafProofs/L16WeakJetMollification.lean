import Yau.LeafProofs.L16MixedSobolev
import Yau.LeafProofs.L03

/-!
# Mollification of finite coordinate weak jets

All derivatives are genuine coordinate evaluations of Fréchet derivatives, all
integrals use actual finite-product Lebesgue volume, and every weak-jet condition
is tested against compact smooth functions. No derivative of the rough input is
used in the conclusions.
-/

open MeasureTheory Filter
open scoped Topology ContDiff Convolution BigOperators
noncomputable section
namespace Yau.LeafProofs.L16Aux

set_option backward.isDefEq.respectTransparency false

/-- A finite weak jet, retaining the literal rough function at the empty word. -/
def FiniteCoordinateWeakJet {m : ℕ} (N : ℕ) (u : (Fin m → ℝ) → ℝ)
    (U : List (Fin m) → (Fin m → ℝ) → ℝ) : Prop :=
  U [] = u ∧
  (∀ v, v.length ≤ N → MemLp (U v) 2 volume ∧ HasCompactSupport (U v)) ∧
  ∀ v, v.length < N → ∀ i : Fin m, ∀ φ : (Fin m → ℝ) → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, U v x * fderiv ℝ φ x (Pi.single i 1)) = -(∫ x, U (i :: v) x * φ x)

/-- The dyadic dilations of a fixed, actual smooth kernel. -/
def coordinateMollifier {m : ℕ} (ρ : (Fin m → ℝ) → ℝ) (k : ℕ) :
    (Fin m → ℝ) → ℝ :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier ρ ((1 / 2 : ℝ) ^ k)

/-- The actual convolution, applied to the original raw function. -/
def coordinateMollify {m : ℕ} (ρ : (Fin m → ℝ) → ℝ) (k : ℕ)
    (u : (Fin m → ℝ) → ℝ) : (Fin m → ℝ) → ℝ :=
  coordinateMollifier ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u

private theorem dyadic_pos (k : ℕ) : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) k

private theorem coordinateMollifier_smooth {m : ℕ} {ρ : (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (k : ℕ) : ContDiff ℝ ∞ (coordinateMollifier ρ k) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_contDiff_top _ _ hρ

private theorem coordinateMollifier_compact {m : ℕ} {ρ : (Fin m → ℝ) → ℝ}
    (hcρ : HasCompactSupport ρ) (k : ℕ) : HasCompactSupport (coordinateMollifier ρ k) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_compact _ (dyadic_pos k).ne' hcρ

theorem coordinateMollify_smooth {m : ℕ} {ρ u : (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hu : Integrable u volume)
    (k : ℕ) : ContDiff ℝ ∞ (coordinateMollify ρ k u) :=
  (coordinateMollifier_compact hcρ k).contDiff_convolution_left _
    (coordinateMollifier_smooth hρ k) hu.locallyIntegrable

theorem coordinateMollify_compact {m : ℕ} {ρ u : (Fin m → ℝ) → ℝ}
    (hcρ : HasCompactSupport ρ) (hcu : HasCompactSupport u) (k : ℕ) :
    HasCompactSupport (coordinateMollify ρ k u) :=
  (coordinateMollifier_compact hcρ k).convolution _ hcu

/-- Weak directional differentiation commutes with genuine convolution on finite
real coordinate space. The weak equation is used only on compact smooth tests. -/
theorem finitePi_weak_directionalDerivative_convolution {m : ℕ}
    {u g : (Fin m → ℝ) → ℝ} (hu : Integrable u volume) (e : Fin m → ℝ)
    (hWeak : ∀ φ : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x e) = -(∫ x, g x * φ x))
    (ρ : (Fin m → ℝ) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (x : Fin m → ℝ) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hSystem : Yau.LeafProofs.L03.firstOrderSystemWeakEquation volume
      (fun _ : Unit => e)
      (fun (_ : Unit) (_ : Unit) (_ : Unit) (_ : Fin m → ℝ) => (1 : ℝ))
      (fun (_ : Unit) (_ : Unit) (_ : Fin m → ℝ) => (0 : ℝ))
      (fun (x : Fin m → ℝ) (_ : Unit) => u x)
      (fun (x : Fin m → ℝ) (_ : Unit) => g x) := by
    intro r φ hφ hcφ
    have h := hWeak φ hφ hcφ
    simp only [Fintype.sum_unique, fderiv_fun_const, Pi.zero_apply, zero_apply,
      one_mul, zero_mul, mul_zero, add_zero, integral_zero] at *
    simp only [mul_comm] at h ⊢
    linarith
  have h := Yau.LeafProofs.L03.firstOrderSystemWeakEquation_mollifier_identity volume
    (fun _ : Unit => e)
    (fun (_ : Unit) (_ : Unit) (_ : Unit) (_ : Fin m → ℝ) => (1 : ℝ))
    (fun (_ : Unit) (_ : Unit) (_ : Fin m → ℝ) => (0 : ℝ))
    (fun _ _ _ => contDiff_const) (fun _ _ _ => (0 : NNReal))
    (fun _ _ _ => LipschitzWith.const _)
    (fun (x : Fin m → ℝ) (_ : Unit) => u x)
    (fun (x : Fin m → ℝ) (_ : Unit) => g x)
    (fun _ => hu) hSystem ρ hρ hcρ () x
  simp only [Fintype.sum_unique, one_mul, zero_mul, add_zero, sub_self,
    Yau.LeafProofs.L03.friedrichsCommutatorKernel, fderiv_fun_const, Pi.zero_apply,
    zero_apply, mul_zero, integral_zero, zero_add] at h
  simp only [MeasureTheory.convolution_lsmul, smul_eq_mul, mul_zero, integral_zero, sub_zero] at h
  exact sub_eq_zero.mp h

/-- Every actual derivative through the available finite order equals the
mollification of its specified rough weak derivative, pointwise everywhere. -/
theorem coordinateWordDerivative_coordinateMollify {m N : ℕ}
    {ρ u : (Fin m → ℝ) → ℝ} {U : List (Fin m) → (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hU : FiniteCoordinateWeakJet N u U) (k : ℕ) (v : List (Fin m)) (hv : v.length ≤ N) :
    coordinateWordDerivative (coordinateMollify ρ k u) v = coordinateMollify ρ k (U v) := by
  induction v with
  | nil => simp only [coordinateWordDerivative_nil, hU.1]
  | cons i v ih =>
      have hv' : v.length < N := by simp only [List.length_cons] at hv; omega
      have hi := ih (Nat.le_of_lt hv')
      simp only [coordinateWordDerivative]
      rw [hi]
      funext x
      exact finitePi_weak_directionalDerivative_convolution
        (Yau.LeafProofs.L03.memLp_two_compact_integrable volume _
          (hU.2.1 v (Nat.le_of_lt hv')).1 (hU.2.1 v (Nat.le_of_lt hv')).2)
        (Pi.single i 1) (hU.2.2 v hv' i) _
        (coordinateMollifier_smooth hρ k) (coordinateMollifier_compact hcρ k) x

/-- Composition of head-outer coordinate words is literal list concatenation. -/
theorem coordinateWordDerivative_append {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (v w : List (Fin m)) :
    coordinateWordDerivative (coordinateWordDerivative f w) v =
      coordinateWordDerivative f (v ++ w) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [coordinateWordDerivative, List.cons_append, ih]

/-- Genuine L² control of the mollified raw input. -/
theorem coordinateMollify_memLp {m : ℕ} {ρ u : (Fin m → ℝ) → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hu : MemLp u 2 volume) (hcu : HasCompactSupport u) (k : ℕ) :
    MemLp (coordinateMollify ρ k u) 2 volume := by
  have h0 (x) : 0 ≤ coordinateMollifier ρ k x :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (dyadic_pos k).le _)) (hρ0 _)
  have h1 : (∫ x, coordinateMollifier ρ k x) = 1 :=
    (Yau.LeafProofs.L03.rescaledFriedrichsMollifier_integral volume ρ (dyadic_pos k)).trans hρ1
  exact (Yau.LeafProofs.L03.probability_convolution_L2_bound volume _ h0 h1 u
    (Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu hcu)
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)).1

/-- Strong L² convergence of the actual mollifications. -/
theorem coordinateMollify_L2_tendsto {m : ℕ} {ρ u : (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hu : MemLp u 2 volume) (hcu : HasCompactSupport u) :
    Tendsto (fun k => ∫ x, ‖coordinateMollify ρ k u x - u x‖ ^ 2) atTop (𝓝 0) :=
  Yau.LeafProofs.L03.rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp
    volume ρ (hρ.of_le (by simp)) hcρ hρ0 hρ1 (fun k => (1 / 2 : ℝ) ^ k)
    dyadic_pos (fun k => pow_le_one₀ (by norm_num) (by norm_num))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) u hu hcu

/-- Each actual coordinate derivative has proper L² membership and converges
strongly in L² to the corresponding raw member of the finite weak jet. -/
theorem coordinateWordDerivative_coordinateMollify_strongL2 {m N : ℕ}
    {ρ u : (Fin m → ℝ) → ℝ} {U : List (Fin m) → (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hU : FiniteCoordinateWeakJet N u U) (v : List (Fin m)) (hv : v.length ≤ N) :
    (∀ k, MemLp (coordinateWordDerivative (coordinateMollify ρ k u) v) 2 volume) ∧
    Tendsto (fun k => ∫ x,
      ‖coordinateWordDerivative (coordinateMollify ρ k u) v x - U v x‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [coordinateWordDerivative_coordinateMollify hρ hcρ hU _ v hv]
  exact ⟨fun k => coordinateMollify_memLp hρ0 hρ1 (hU.2.1 v hv).1 (hU.2.1 v hv).2 k,
    coordinateMollify_L2_tendsto hρ hcρ hρ0 hρ1 (hU.2.1 v hv).1 (hU.2.1 v hv).2⟩

private theorem memLp_integrable_sub_sq {m : ℕ} {a b : (Fin m → ℝ) → ℝ}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    Integrable (fun x => (a x - b x) ^ 2) volume := by
  have h := ha.sub hb
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
    (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

private theorem integral_sub_sq_le_two_errors {m : ℕ} {a b c : (Fin m → ℝ) → ℝ}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) (hc : MemLp c 2 volume) :
    (∫ x, (a x - b x) ^ 2) ≤
      2 * (∫ x, (a x - c x) ^ 2) + 2 * (∫ x, (b x - c x) ^ 2) := by
  have hab := memLp_integrable_sub_sq ha hb
  have hac := memLp_integrable_sub_sq ha hc
  have hbc := memLp_integrable_sub_sq hb hc
  calc
    _ ≤ ∫ x, (2 * (a x - c x) ^ 2 + 2 * (b x - c x) ^ 2) :=
      integral_mono hab ((hac.const_mul 2).add (hbc.const_mul 2))
        (fun x => by nlinarith [sq_nonneg (a x + b x - 2 * c x)])
    _ = _ := by rw [integral_add (hac.const_mul 2) (hbc.const_mul 2),
      integral_const_mul, integral_const_mul]

/-- A finite jet through order `w.length + m` makes the sequence of actual
mollified coordinate derivatives uniformly Cauchy on the entire coordinate space. -/
theorem coordinateWordDerivative_coordinateMollify_uniformCauchy {m N : ℕ}
    {ρ u : (Fin m → ℝ) → ℝ} {U : List (Fin m) → (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hU : FiniteCoordinateWeakJet N u U) (w : List (Fin m)) (hw : w.length + m ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ x : Fin m → ℝ,
      |coordinateWordDerivative (coordinateMollify ρ k u) w x -
        coordinateWordDerivative (coordinateMollify ρ l u) w x| < ε := by
  classical
  let f : ℕ → (Fin m → ℝ) → ℝ :=
    fun k => coordinateWordDerivative (coordinateMollify ρ k u) w
  have hu : MemLp u 2 volume ∧ HasCompactSupport u := by
    simpa only [List.length_nil, hU.1] using hU.2.1 [] (Nat.zero_le N)
  have hui : Integrable u volume :=
    Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu.1 hu.2
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) :=
    contDiff_coordinateWordDerivative (coordinateMollify_smooth hρ hcρ hui k) w
  have hcf (k : ℕ) : HasCompactSupport (f k) :=
    hasCompactSupport_coordinateWordDerivative (coordinateMollify_compact hcρ hu.2 k) w
  let V : Finset (Fin m) → List (Fin m) := fun s => s.sort (· ≤ ·) ++ w
  have hV (s : Finset (Fin m)) : (V s).length ≤ N := by
    have hs : s.card ≤ m := by simpa only [Fintype.card_fin] using s.card_le_univ
    simp only [V, List.length_append, Finset.length_sort]
    omega
  have hmix (k : ℕ) (s : Finset (Fin m)) :
      mixedDerivative (f k) s = coordinateMollify ρ k (U (V s)) := by
    change coordinateWordDerivative (coordinateWordDerivative (coordinateMollify ρ k u) w)
      (s.sort (· ≤ ·)) = _
    rw [coordinateWordDerivative_append]
    exact coordinateWordDerivative_coordinateMollify hρ hcρ hU k (V s) (hV s)
  have hmix_mem (k : ℕ) (s : Finset (Fin m)) :
      MemLp (mixedDerivative (f k) s) 2 volume := by
    rw [hmix]
    exact coordinateMollify_memLp hρ0 hρ1 (hU.2.1 _ (hV s)).1 (hU.2.1 _ (hV s)).2 k
  have hsq (s : Finset (Fin m)) :
      Tendsto (fun k => ∫ x, (mixedDerivative (f k) s x - U (V s) x) ^ 2)
        atTop (𝓝 0) := by
    simp_rw [hmix]
    simpa only [Real.norm_eq_abs, sq_abs] using coordinateMollify_L2_tendsto
      hρ hcρ hρ0 hρ1 (hU.2.1 _ (hV s)).1 (hU.2.1 _ (hV s)).2
  let E : ℕ → ℝ := fun k => ∑ s : Finset (Fin m),
    ∫ x, (mixedDerivative (f k) s x - U (V s) x) ^ 2
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun s _ => hsq s)
  apply uniform_cauchy_of_mixed_integral_sq_cauchy hf hcf
  intro δ hδ
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hE.eventually_lt_const (show 0 < δ / 4 by positivity))
  refine ⟨K, fun k hk l hl => ?_⟩
  calc
    _ ≤ ∑ s : Finset (Fin m),
        (2 * (∫ x, (mixedDerivative (f k) s x - U (V s) x) ^ 2) +
          2 * (∫ x, (mixedDerivative (f l) s x - U (V s) x) ^ 2)) :=
      Finset.sum_le_sum fun s _ => integral_sub_sq_le_two_errors
        (hmix_mem k s) (hmix_mem l s) (hU.2.1 _ (hV s)).1
    _ = 2 * E k + 2 * E l := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < δ := by have hk' := hK k hk; have hl' := hK l hl; linarith

/-- Arbitrarily high finite weak jets suffice: no coherent infinite family is
required, since each word uses only the jet of order `w.length + m`. -/
theorem coordinateWordDerivative_coordinateMollify_uniformCauchy_of_finiteJets {m : ℕ}
    {ρ u : (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hjets : ∀ N : ℕ, ∃ U : List (Fin m) → (Fin m → ℝ) → ℝ,
      FiniteCoordinateWeakJet N u U) (w : List (Fin m)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ x : Fin m → ℝ,
      |coordinateWordDerivative (coordinateMollify ρ k u) w x -
        coordinateWordDerivative (coordinateMollify ρ l u) w x| < ε := by
  obtain ⟨U, hU⟩ := hjets (w.length + m)
  exact coordinateWordDerivative_coordinateMollify_uniformCauchy
    hρ hcρ hρ0 hρ1 hU w le_rfl

end Yau.LeafProofs.L16Aux
