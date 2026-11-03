import Yau.LeafProofs.L16TimeTransport

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem schauderBound_add_with_low_pair {n : ℕ} {α C D : ℝ} {Q : Set (Point n)}
    {u v : Point n → ℝ} (hu : SchauderBound α Q u C) (hv : SchauderBound α Q v D)
    (huLow : HolderBound α Q (fun p => (u p,spatialD u p)) C)
    (hvLow : HolderBound α Q (fun p => (v p,spatialD v p)) D) :
    SchauderBound α Q (fun p => u p+v p) (C+D) ∧
    HolderBound α Q (fun p => (u p+v p,spatialD (fun q => u q+v q) p)) (C+D) := by
  have h := full_jet_add hu.1 hv.1 (holderBound_fst huLow) (holderBound_fst hvLow)
    (holderBound_snd huLow) (holderBound_snd hvLow) hu.2.2.2.1 hv.2.2.2.1 hu.2.2.2.2 hv.2.2.2.2
  refine ⟨⟨h.1,h.2.1.1,?_,h.2.2.2.1,h.2.2.2.2⟩,h.2.1.1,?_,?_⟩
  · intro p hp
    exact ⟨by simpa only [Real.norm_eq_abs] using h.2.1.2.1 p hp,h.2.2.1.2.1 p hp⟩
  · intro p hp
    exact max_le (h.2.1.2.1 p hp) (h.2.2.1.2.1 p hp)
  · intro p hp q hq
    exact max_le (h.2.1.2.2 p hp q hq) (h.2.2.1.2.2 p hp q hq)

def traceCorrectedSource {n : ℕ} (τ : ℝ) (u : Point n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  f p+(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
    a p i j*spatialDD (spatialTraceLift τ u) p (Yau.realVec i) (Yau.realVec j))+
    ∑ i : Yau.RIdx n, b p i*spatialD (spatialTraceLift τ u) p (Yau.realVec i)

theorem traceCorrectedSource_holderBound {n : ℕ} {α C F M l r τ : ℝ}
    (hα : 0 < α) {Q : Set (Point n)} {u f : Point n → ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ l r) u C)
    (huLow : HolderBound α (cylinder Set.univ l r) (fun p => (u p,spatialD u p)) C)
    (hτ : τ ∈ Set.Icc l r) (ha : HolderBound α Q a M)
    (hb : ∀ i, HolderBound α Q (fun p => b p i) M) (hf : HolderBound α Q f F) :
    HolderBound α Q (traceCorrectedSource τ u a b f)
      (F+(Fintype.card (Yau.RIdx n) : ℝ)^2*(M*C+M*C)+
        (Fintype.card (Yau.RIdx n) : ℝ)*(2*M*C)) := by
  have hLift := schauderBound_spatialTraceLift hα hu hτ Q
  have hLow : HolderBound α Q
      (fun p => (spatialTraceLift τ u p,spatialD (spatialTraceLift τ u) p)) C :=
    holderBound_spatialTraceLift hα huLow hτ Q
  have hPrincipal := hessian_contraction_holderBound ha.1 hu.2.1
    (fun i j => holderBound_matrix_entry ha i j)
    (fun i j p hp => by simpa only [Real.norm_eq_abs] using
      (holderBound_matrix_entry ha i j).2.1 p hp)
    hLift.2.2.2.1 hLift.2.2.2.1.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
    holderBound_mul (hb i) (holderBound_gradient_component (holderBound_snd hLow) i))
  have h := holderBound_add (holderBound_add hf hPrincipal) hDrift
  change HolderBound α Q (fun p => traceCorrectedSource τ u a b f p) _
  simpa only [traceCorrectedSource,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using h

/-- An existing spatial trace supplies arbitrary initial data for the
short inverse; the shifted right-hand side uses its actual Hessian. -/
theorem short_inverse_with_spatial_trace {n : ℕ} {α T C F M l r τ CS : ℝ}
    (hα : 0 < α) {u f : Point n → ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ l r) u C)
    (huLow : HolderBound α (cylinder Set.univ l r) (fun p => (u p,spatialD u p)) C)
    (hτ : τ ∈ Set.Icc l r) (ha : HolderBound α (cylinder Set.univ 0 T) a M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hInverse : ∀ (g : Point n → ℝ) (G : ℝ), HolderBound α (cylinder Set.univ 0 T) g G →
      ∃ v : Point n → ℝ, SchauderBound α (cylinder Set.univ 0 T) v (CS*G) ∧
        HolderBound α (cylinder Set.univ 0 T) (fun p => (v p,spatialD v p)) (CS*G) ∧
        (∀ x, v (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
          linearOp (cylinder Set.univ 0 T) a b v p = g p) :
    ∃ (w : Point n → ℝ) (D : ℝ),
      SchauderBound α (cylinder Set.univ 0 T) w D ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (w p,spatialD w p)) D ∧
      (∀ x, w (x,0) = u (x,τ)) ∧ ∀ p ∈ cylinder Set.univ 0 T,
        linearOp (cylinder Set.univ 0 T) a b w p = f p := by
  let Q : Set (Point n) := cylinder Set.univ 0 T
  let G : ℝ := F+(Fintype.card (Yau.RIdx n) : ℝ)^2*(M*C+M*C)+
    (Fintype.card (Yau.RIdx n) : ℝ)*(2*M*C)
  have hSource := traceCorrectedSource_holderBound hα hu huLow hτ ha hb hf
  obtain ⟨v,hv,hvLow,hv0,hvOp⟩ := hInverse (traceCorrectedSource τ u a b f) G hSource
  have hLift := schauderBound_spatialTraceLift hα hu hτ Q
  have hLiftLow : HolderBound α Q
      (fun p => (spatialTraceLift τ u p,spatialD (spatialTraceLift τ u) p)) C :=
    holderBound_spatialTraceLift hα huLow hτ Q
  have hSum := schauderBound_add_with_low_pair hLift hv hLiftLow hvLow
  refine ⟨fun p => spatialTraceLift τ u p+v p,C+CS*G,hSum.1,hSum.2,?_,?_⟩
  · intro x
    simp only [spatialTraceLift,hv0,add_zero]
  · intro p hp
    rw [linearOp_add hLift.1 hv.1 hp,hvOp p hp]
    simp only [linearOp,timeD_spatialTraceLift,Pi.zero_apply,traceCorrectedSource]
    ring

theorem spatialD_eq_of_trace {n : ℕ} {τ : ℝ} {u v : Point n → ℝ}
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) (x : Space n) :
    spatialD u (x,τ) = spatialD v (x,τ) := by
  change fderiv ℝ (fun y => u (y,τ)) x = fderiv ℝ (fun y => v (y,τ)) x
  rw [show (fun y => u (y,τ)) = (fun y => v (y,τ)) from funext hTrace]

theorem spatialDD_eq_of_trace {n : ℕ} {τ : ℝ} {u v : Point n → ℝ}
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) (x : Space n) :
    spatialDD u (x,τ) = spatialDD v (x,τ) := by
  change fderiv ℝ (fderiv ℝ (fun y => u (y,τ))) x =
    fderiv ℝ (fderiv ℝ (fun y => v (y,τ))) x
  rw [show (fun y => u (y,τ)) = (fun y => v (y,τ)) from funext hTrace]

/-- Equality of the complete spatial trace and of the actual equations
forces the time derivatives to agree at a joining face. -/
theorem timeD_eq_of_trace_and_operator {n : ℕ} {τ : ℝ} {Q Q' : Set (Point n)}
    {u v : Point n → ℝ} (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hTrace : ∀ x, u (x,τ) = v (x,τ)) (x : Space n)
    (hOp : linearOp Q a b u (x,τ) = linearOp Q' a b v (x,τ)) :
    timeD Q u (x,τ) = timeD Q' v (x,τ) := by
  unfold linearOp at hOp
  rw [spatialD_eq_of_trace hTrace x,spatialDD_eq_of_trace hTrace x] at hOp
  linarith

theorem spatialD_initial_zero {n : ℕ} {u : Point n → ℝ} (hInitial : ∀ x, u (x,0) = 0)
    (x : Space n) : spatialD u (x,0) = 0 := by
  simpa only [spatialD_zero,Pi.zero_apply] using
    spatialD_eq_of_trace (τ := 0) (u := u) (v := fun _ => 0) hInitial x

theorem spatialDD_initial_zero {n : ℕ} {u : Point n → ℝ} (hInitial : ∀ x, u (x,0) = 0)
    (x : Space n) : spatialDD u (x,0) = 0 := by
  simpa only [spatialDD_zero,Pi.zero_apply] using
    spatialDD_eq_of_trace (τ := 0) (u := u) (v := fun _ => 0) hInitial x

theorem smooth_compact_short_classical_solution {n : ℕ} {α T lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧ ∀ S : ℝ, 0 < S → S ≤ δ →
      ∃ (u : Point n → ℝ) (D : ℝ), SchauderBound α (cylinder Set.univ 0 S) u D ∧
        HolderBound α (cylinder Set.univ 0 S) (fun p => (u p,spatialD u p)) D ∧
        (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 S,
          linearOp (cylinder Set.univ 0 S) a b u p = f p := by
  obtain ⟨M,L,hM,hL,ha,hb,hLip⟩ := smooth_coefficients_common_bounds hT hα hα1 hK hSmooth
    (fun x hx t ht => ⟨(hExterior x hx t ht).1,(hExterior x hx t ht).2.1⟩)
  obtain ⟨F,hF,hf⟩ := smooth_cylinder_compact_perturbation_holder hT hα hα1 hK hfSmooth
    (fun x hx t ht => (hExterior x hx t ht).2.2)
  obtain ⟨δ0,hδ0,hδ01,hInverse⟩ :=
    exists_uniform_short_schauder_inverse (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hL.le hK
  let δ : ℝ := min δ0 T
  refine ⟨δ,lt_min hδ0 hT,min_le_right _ _,?_⟩
  intro S hS hSδ
  have hST : S ≤ T := hSδ.trans (min_le_right _ _)
  have hSub : cylinder (n := n) Set.univ 0 S ⊆ cylinder Set.univ 0 T := cylinder_mono_time hST
  obtain ⟨C,hC,hSolve⟩ := hInverse S a b hS (hSδ.trans (min_le_left _ _))
    (holderBound_mono ha hSub) (fun i => holderBound_mono (hb i) hSub)
    (fun p hp q hq => hLip p (hSub hp) q (hSub hq)) (elliptic_mono hEll hSub)
    (fun p hp hpk => (hExterior p.1 hpk p.2 (hSub hp).2).1)
  obtain ⟨u,hu,hLow,h0,hOp⟩ := hSolve f F (holderBound_mono hf hSub)
  exact ⟨u,C*F,hu,hLow,h0,hOp⟩

theorem short_inverse_with_trace_on_next_slab {n : ℕ} {α T S τ C F M CS : ℝ}
    (hα : 0 < α) (hS : 0 < S) (hτ : 0 ≤ τ) (hST : S+τ ≤ T)
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 τ) u C)
    (huLow : HolderBound α (cylinder Set.univ 0 τ) (fun p => (u p,spatialD u p)) C)
    (ha : HolderBound α (cylinder Set.univ 0 T) a M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hInverse : ∀ (g : Point n → ℝ) (G : ℝ), HolderBound α (cylinder Set.univ 0 S) g G →
      ∃ v : Point n → ℝ, SchauderBound α (cylinder Set.univ 0 S) v (CS*G) ∧
        HolderBound α (cylinder Set.univ 0 S) (fun p => (v p,spatialD v p)) (CS*G) ∧
        (∀ x, v (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 S,
          linearOp (cylinder Set.univ 0 S) (timeTranslate τ a) (timeTranslate τ b) v p = g p) :
    ∃ (w : Point n → ℝ) (D : ℝ),
      SchauderBound α (cylinder Set.univ τ (τ+S)) w D ∧
      HolderBound α (cylinder Set.univ τ (τ+S)) (fun p => (w p,spatialD w p)) D ∧
      (∀ x, w (x,τ) = u (x,τ)) ∧ ∀ p ∈ cylinder Set.univ τ (τ+S),
        linearOp (cylinder Set.univ τ (τ+S)) a b w p = f p := by
  have haS := holderBound_timeTranslate_subslab hτ hST ha
  have hbS (i : Yau.RIdx n) := holderBound_timeTranslate_subslab hτ hST (hb i)
  have hfS := holderBound_timeTranslate_subslab hτ hST hf
  obtain ⟨w,D,hw,hLow,h0,hOp⟩ := short_inverse_with_spatial_trace hα hu huLow ⟨hτ,le_rfl⟩ haS hbS hfS hInverse
  change ∀ p ∈ cylinder Set.univ 0 S,
    linearOp (cylinder Set.univ 0 S) (timeTranslate τ a) (timeTranslate τ b) w p = timeTranslate τ f p at hOp
  refine ⟨timeTranslate (-τ) w,D,schauderBound_timeUntranslate hS hw,
    holderBound_timeUntranslate hLow,?_,?_⟩
  · intro x
    simpa only [timeTranslate,timeTranslatePoint,add_neg_cancel] using h0 x
  · intro p hp
    have hpS : timeTranslatePoint (-τ) p ∈ cylinder Set.univ 0 S :=
      ⟨Set.mem_univ _,by dsimp only [timeTranslatePoint]; linarith [hp.2.1],
        by dsimp only [timeTranslatePoint]; linarith [hp.2.2]⟩
    have h := linearOp_timeUntranslate hS hw.1 (timeTranslate τ a) (timeTranslate τ b) hp
    rw [timeTranslate_cancel,timeTranslate_cancel,hOp _ hpS] at h
    simpa only [timeTranslate,timeTranslatePoint,neg_add_cancel_right] using h

end Yau.LeafProofs.L16Aux
