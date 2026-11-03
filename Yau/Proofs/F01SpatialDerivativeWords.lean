import Yau.Proofs.F01ClosedSpatialTimeJet

/-! Finite words of genuine spatial directional derivatives preserve the
closed time equation and its zero initial jets. Every such derivative has
its own parabolic C2 zero extension; no joint second-time extension is claimed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def spatialDerivativeWord : List E → (E × ℝ → F) → E × ℝ → F
  | [], f => f
  | v :: vs, f => fun p => fderiv ℝ (fun z => spatialDerivativeWord vs f (z, p.2)) p.1 v

theorem spatialDerivativeWord_smooth {f : E × ℝ → F} {S : Set E} {T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T)) (vs : List E) :
    ContDiffOn ℝ ∞ (spatialDerivativeWord vs f) (S ×ˢ Icc 0 T) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact closed_slab_space_direction_smooth hS (uniqueDiffOn_Icc hT) ih v

theorem spatialDerivativeWord_initial_zero {f : E × ℝ → F} {S : Set E}
    (hS : IsOpen S) (hf0 : ∀ x ∈ S, f (x, 0) = 0) (vs : List E) :
    ∀ x ∈ S, spatialDerivativeWord vs f (x, 0) = 0 := by
  induction vs with
  | nil => exact hf0
  | cons v vs ih =>
    intro x hx
    have heq : (fun z => spatialDerivativeWord vs f (z, 0)) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih z hz
    change fderiv ℝ (fun z => spatialDerivativeWord vs f (z, 0)) x v = 0
    rw [heq.fderiv_eq]
    simp

theorem spatialDerivativeWord_time_jet {f P : E × ℝ → F} {S : Set E} {T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) (Icc 0 T) t) (vs : List E) :
    ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs f (x, s))
        (spatialDerivativeWord vs P (x, t)) (Icc 0 T) t := by
  induction vs with
  | nil => exact hJet
  | cons v vs ih =>
    intro x hx t ht
    exact closed_space_direction_time_jet hS hT (spatialDerivativeWord_smooth hS hT hf vs) ih hx ht v

theorem spatialDerivativeWord_zeroExtension_C2 {n : ℕ}
    {f P : Yau.Parabolic.Point n → ℝ} {S : Set (Yau.Parabolic.Space n)} {a T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (ha : a < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    (hf0 : ∀ x ∈ S, f (x, 0) = 0) (hP0 : ∀ x ∈ S, P (x, 0) = 0)
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) (Icc 0 T) t)
    (vs : List (Yau.Parabolic.Space n)) :
    Yau.Parabolic.C2 (S ×ˢ Icc a T) (forwardZeroSpaceTime (spatialDerivativeWord vs f)) := by
  apply forwardZeroSpaceTime_parabolic_C2 hS hT ha (spatialDerivativeWord_smooth hS hT hf vs)
    (spatialDerivativeWord_initial_zero hS hf0 vs)
  intro x hx
  have hj := spatialDerivativeWord_time_jet hS hT hf hJet vs x hx 0 ⟨le_rfl, hT.le⟩
  rw [spatialDerivativeWord_initial_zero hS hP0 vs x hx] at hj
  exact hj

end Yau.NodeProofs.F01Aux
