import Yau.LeafProofs.L10InteriorJets

/-! The first letter of the word commutator, for the original operator. -/

noncomputable section
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

def ellipticPartial {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ComplexVector n → F) (i : RIdx n) (x : ComplexVector n) : F :=
  fderiv ℝ u x (realVec i)

theorem ellipticPartial_contDiffOn {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ComplexVector n → F} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) (i : RIdx n) : ContDiffOn ℝ ∞ (ellipticPartial u i) O :=
  elliptic_contDiffOn_directionalDerivative hO hu (realVec i)

theorem ellipticPartial_commute {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (i j : RIdx n) :
    ellipticPartial (ellipticPartial u j) i x = ellipticPartial (ellipticPartial u i) j x :=
  elliptic_directional_derivatives_commute ((hu.contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (realVec j) (realVec i)

theorem ellipticPartial_three_commute {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (i p q : RIdx n) :
    ellipticPartial (ellipticPartial (ellipticPartial u q) p) i x =
      ellipticPartial (ellipticPartial (ellipticPartial u i) q) p x := by
  rw [ellipticPartial_commute hO (ellipticPartial_contDiffOn hO hu q) hx i p]
  have heq : ellipticPartial (ellipticPartial u q) i =ᶠ[𝓝 x]
      ellipticPartial (ellipticPartial u i) q := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact ellipticPartial_commute hO hu hy i q
  exact congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L (realVec p)) heq.fderiv_eq

def ellipticFirstCommutator {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℂ)
    (i : RIdx n) (x : ComplexVector n) : ℂ :=
  (∑ p, ∑ q, ellipticPartial (fun y => a y p q) i x •
    ellipticPartial (ellipticPartial u q) p x) +
  ∑ p, ellipticPartial (fun y => b y p) i x • ellipticPartial u p x

theorem ellipticFirstCommutator_contDiffOn {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) (i : RIdx n) :
    ContDiffOn ℝ ∞ (ellipticFirstCommutator a b u i) O := by
  classical
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro p _
    apply ContDiffOn.sum
    intro q _
    exact (ellipticPartial_contDiffOn hO (ha p q) i).smul
      (ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p)
  · apply ContDiffOn.sum
    intro p _
    exact (ellipticPartial_contDiffOn hO (hb p) i).smul (ellipticPartial_contDiffOn hO hu p)

theorem ellipticPartial_smul {n : ℕ}
    {a : ComplexVector n → ℝ} {u : ComplexVector n → ℂ} {x : ComplexVector n}
    (ha : DifferentiableAt ℝ a x) (hu : DifferentiableAt ℝ u x) (i : RIdx n) :
    ellipticPartial (fun y => a y • u y) i x =
      a x • ellipticPartial u i x + ellipticPartial a i x • u x := by
  unfold ellipticPartial
  rw [fderiv_fun_smul ha hu]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

theorem ellipticPartial_sum {n : ℕ} {ι : Type*} {S : Finset ι}
    {f : ι → ComplexVector n → ℂ} {x : ComplexVector n}
    (hf : ∀ j ∈ S, DifferentiableAt ℝ (f j) x) (i : RIdx n) :
    ellipticPartial (fun y => ∑ j ∈ S, f j y) i x =
      ∑ j ∈ S, ellipticPartial (f j) i x := by
  unfold ellipticPartial
  rw [fderiv_fun_sum hf]
  simp only [sum_apply]

theorem ellipticPartial_add {n : ℕ}
    {f g : ComplexVector n → ℂ} {x : ComplexVector n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : RIdx n) :
    ellipticPartial (fun y => f y + g y) i x =
      ellipticPartial f i x + ellipticPartial g i x := by
  unfold ellipticPartial
  rw [fderiv_fun_add hf hg]
  simp only [add_apply]

theorem ellipticOp_eq_sum_partials {n : ℕ}
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℂ) (x : ComplexVector n) :
    LeafCandidates.ellipticOp a b u x =
      (∑ p, ∑ q, a x p q • ellipticPartial (ellipticPartial u q) p x) +
        ∑ p, b x p • ellipticPartial u p x := by
  simp only [LeafCandidates.ellipticOp, ellipticPartial, Complex.real_smul]
  rfl

theorem ellipticFirstCommutator_identity {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (i : RIdx n) :
    ellipticPartial (LeafCandidates.ellipticOp a b u) i x =
      LeafCandidates.ellipticOp a b (ellipticPartial u i) x + ellipticFirstCommutator a b u i x := by
  classical
  let Aterm (p q : RIdx n) (y : ComplexVector n) :=
    a y p q • ellipticPartial (ellipticPartial u q) p y
  let Bterm (p : RIdx n) (y : ComplexVector n) := b y p • ellipticPartial u p y
  have hAsmooth (p q : RIdx n) : ContDiffOn ℝ ∞ (Aterm p q) O :=
    (ha p q).smul (ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p)
  have hBsmooth (p : RIdx n) : ContDiffOn ℝ ∞ (Bterm p) O :=
    (hb p).smul (ellipticPartial_contDiffOn hO hu p)
  have hAdiff (p q : RIdx n) : DifferentiableAt ℝ (Aterm p q) x :=
    ((hAsmooth p q).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hBdiff (p : RIdx n) : DifferentiableAt ℝ (Bterm p) x :=
    ((hBsmooth p).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hAderiv (p q : RIdx n) : ellipticPartial (Aterm p q) i x =
      a x p q • ellipticPartial (ellipticPartial (ellipticPartial u i) q) p x +
        ellipticPartial (fun y => a y p q) i x • ellipticPartial (ellipticPartial u q) p x := by
    rw [show Aterm p q = (fun y => a y p q • ellipticPartial (ellipticPartial u q) p y) from rfl,
      ellipticPartial_smul (((ha p q).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (((ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)),
      ellipticPartial_three_commute hO hu hx i p q]
  have hBderiv (p : RIdx n) : ellipticPartial (Bterm p) i x =
      b x p • ellipticPartial (ellipticPartial u i) p x +
        ellipticPartial (fun y => b y p) i x • ellipticPartial u p x := by
    rw [show Bterm p = (fun y => b y p • ellipticPartial u p y) from rfl,
      ellipticPartial_smul (((hb p).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (((ellipticPartial_contDiffOn hO hu p).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)),
      ellipticPartial_commute hO hu hx i p]
  have hsumA : ellipticPartial (fun y => ∑ p, ∑ q, Aterm p q y) i x =
      ∑ p, ∑ q, ellipticPartial (Aterm p q) i x := by
    rw [ellipticPartial_sum (fun p _ => DifferentiableAt.fun_sum (fun q _ => hAdiff p q))]
    apply Finset.sum_congr rfl
    intro p _
    exact ellipticPartial_sum (fun q _ => hAdiff p q) i
  have hsumB : ellipticPartial (fun y => ∑ p, Bterm p y) i x =
      ∑ p, ellipticPartial (Bterm p) i x := ellipticPartial_sum (fun p _ => hBdiff p) i
  have heq : LeafCandidates.ellipticOp a b u = fun y => (∑ p, ∑ q, Aterm p q y) + ∑ p, Bterm p y := by
    funext y
    exact ellipticOp_eq_sum_partials a b u y
  rw [heq, ellipticPartial_add
    (DifferentiableAt.fun_sum (fun p _ => DifferentiableAt.fun_sum (fun q _ => hAdiff p q)))
    (DifferentiableAt.fun_sum (fun p _ => hBdiff p)), hsumA, hsumB]
  simp only [hAderiv, hBderiv, Finset.sum_add_distrib,
    ellipticOp_eq_sum_partials, ellipticFirstCommutator]
  ring

end Yau.LeafProofs
