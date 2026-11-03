import Yau.Proofs.B01Coordinate
import Yau.Proofs.D03Germ

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Bundle

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

/-- Coordinate germs of an actual holomorphic vector map. -/
def vectorGerm {q : ℕ} (F : ℂ → ComplexVector q) (hF : AnalyticAt ℂ F 0) :
    Fin q → AnalyticGerm := fun i =>
  ofAnalytic (fun z => F z i)
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q => ℂ) i).analyticAt (F 0)).comp hF)

@[simp] theorem vectorGerm_apply_ofAnalytic {q : ℕ} (F : ℂ → ComplexVector q)
    (hF : AnalyticAt ℂ F 0) (i : Fin q) :
    vectorGerm F hF i = ofAnalytic (fun z => F z i)
      (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q => ℂ) i).analyticAt (F 0)).comp hF) := rfl

theorem vectorGerm_eq_iff {q : ℕ} (F G : ℂ → ComplexVector q)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    vectorGerm F hF = vectorGerm G hG ↔ F =ᶠ[𝓝 0] G := by
  constructor
  · intro h
    have hi (i : Fin q) : (fun z => F z i) =ᶠ[𝓝 0] (fun z => G z i) :=
      (ofAnalytic_eq_iff _ _).mp (congrFun h i)
    filter_upwards [Filter.eventually_all.2 hi] with z hz
    ext i
    exact hz i
  · intro h
    funext i
    apply (ofAnalytic_eq_iff _ _).2
    exact h.mono (fun z hz => congrArg (fun v : ComplexVector q => v i) hz)

@[simp] theorem vectorGerm_zero (q : ℕ) :
    vectorGerm (fun _ : ℂ => (0 : ComplexVector q)) analyticAt_const = 0 := rfl

@[simp] theorem vectorGerm_add {q : ℕ} (F G : ℂ → ComplexVector q)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    vectorGerm (F + G) (hF.add hG) = vectorGerm F hF + vectorGerm G hG := by
  funext i
  apply Subtype.ext
  rfl

@[simp] theorem vectorGerm_smul {q : ℕ} (f : ℂ → ℂ) (F : ℂ → ComplexVector q)
    (hf : AnalyticAt ℂ f 0) (hF : AnalyticAt ℂ F 0) :
    vectorGerm (fun z => f z • F z) (hf.smul hF) =
      ofAnalytic f hf • vectorGerm F hF := by
  funext i
  apply Subtype.ext
  rfl

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Local regularity in the original bundle atlas, with no new restricted bundle. -/
def HolomorphicSectionOn (b : Section E) (Ω : Set M.Carrier) : Prop :=
  ∀ a, DifferentiableOn ℂ (sectionCoefficients (r := r) E b a)
    (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' Ω)

def discSectionDomain (c : DiscCoordinate M) (ρ : ℝ) : Set M.Carrier :=
  {x | 0 < ‖c x‖ ∧ ‖c x‖ < ρ}

theorem discSectionDomain_isOpen (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (ρ : ℝ) :
    IsOpen (discSectionDomain c ρ) :=
  (isOpen_lt continuous_const (B01Aux.disc_continuous c hc).norm).inter
    (isOpen_lt (B01Aux.disc_continuous c hc).norm continuous_const)

theorem discSectionDomain_mono (c : DiscCoordinate M) {ρ τ : ℝ} (h : ρ ≤ τ) :
    discSectionDomain c ρ ⊆ discSectionDomain c τ := fun _ hx => ⟨hx.1, hx.2.trans_le h⟩

theorem holomorphicSectionOn_mono {b : Section E} {Ω Θ : Set M.Carrier}
    (hb : HolomorphicSectionOn (r := r) E b Ω) (hΩ : Θ ⊆ Ω) :
    HolomorphicSectionOn (r := r) E b Θ :=
  fun a => (hb a).mono (inter_subset_inter_right _ (preimage_mono hΩ))

theorem holomorphicSectionOn_zero (Ω : Set M.Carrier) :
    HolomorphicSectionOn (r := r) E (fun x => 0) Ω := by
  intro a
  have he : sectionCoefficients (r := r) E (fun x => 0) a =
      fun _ : ComplexVector 1 => (0 : ComplexVector r) := by
    funext z
    simp only [sectionCoefficients, map_zero]
  rw [he]
  exact differentiableOn_const (0 : ComplexVector r)

theorem holomorphicSectionOn_add {b d : Section E} {Ω : Set M.Carrier}
    (hb : HolomorphicSectionOn (r := r) E b Ω)
    (hd : HolomorphicSectionOn (r := r) E d Ω) :
    HolomorphicSectionOn (r := r) E (fun x => b x + d x) Ω := by
  intro a
  have he : sectionCoefficients (r := r) E (fun x => b x + d x) a =
      sectionCoefficients (r := r) E b a + sectionCoefficients (r := r) E d a := by
    funext z
    simp only [sectionCoefficients, map_add, Pi.add_apply]
  rw [he]
  exact (hb a).add (hd a)

theorem holomorphicSectionOn_smul {b : Section E} {Ω : Set M.Carrier} (f : M.Carrier → ℂ)
    (hb : HolomorphicSectionOn (r := r) E b Ω)
    (hf : ∀ a, DifferentiableOn ℂ (fun z => f (chartInv a z))
      (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' Ω)) :
    HolomorphicSectionOn (r := r) E (fun x => f x • b x) Ω := by
  intro a
  have he : sectionCoefficients (r := r) E (fun x => f x • b x) a =
      fun z => f (chartInv a z) • sectionCoefficients (r := r) E b a z := by
    funext z
    exact map_smul _ _ _
  rw [he]
  exact (hf a).smul (hb a)

end Yau.Proofs.D03Aux
