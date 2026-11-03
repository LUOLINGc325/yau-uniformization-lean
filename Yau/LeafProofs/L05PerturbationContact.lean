import Yau.LeafProofs.L05PerturbationGeometry

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The temporal quadratic penalty produces a genuine ambient local maximum
inside one compact product. No joint differentiability of the input is used. -/
theorem perturb_penalty_contact {n : ℕ} (z : Point n) {R S : ℝ}
    (hR : 0<R) (hS : 0<S) (g : Point n → ℝ)
    (hg : ContinuousOn g (closedBall z.1 R ×ˢ Icc (z.2-S) (z.2+S)))
    (hslice : ∀ x ∈ closedBall z.1 R, g (x,z.2) = -‖x-z.1‖^4) :
    ∃ (J : ℝ) (p : Point n), 0≤J ∧
      p ∈ ball z.1 R ×ˢ Ioo (z.2-S) (z.2+S) ∧
      IsLocalMax (fun q => g q-J*(q.2-z.2)^2) p := by
  classical
  let K : Set (Point n) := closedBall z.1 R ×ˢ Icc (z.2-S) (z.2+S)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hzK : z ∈ K := ⟨by simpa using hR.le,by constructor <;> linarith⟩
  have heps : 0 < R^4/2 := by positivity
  obtain ⟨delta,hd,huniform⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hg) (R^4/2) heps
  let s : ℝ := min (S/2) (delta/2)
  have hs : 0<s := lt_min (by positivity) (by positivity)
  have hsS : s≤S := (min_le_left _ _).trans (by linarith)
  have hsd : s<delta := (min_le_right _ _).trans_lt (by linarith)
  let K' : Set (Point n) := closedBall z.1 R ×ˢ Icc (z.2-s) (z.2+s)
  have hsub : K' ⊆ K := by
    intro p hp
    exact ⟨hp.1,by constructor <;> linarith [hp.2.1,hp.2.2]⟩
  obtain ⟨m,hm,hmaxg⟩ := hK.exists_isMaxOn ⟨z,hzK⟩ hg
  let M : ℝ := max 0 (g m)
  have hM : 0≤M := le_max_left _ _
  have hbound : ∀ p∈K, g p≤M := by
    intro p hp
    exact (hmaxg hp).trans (le_max_right _ _)
  let J : ℝ := (M+1)/s^2
  have hJ : 0<J := div_pos (by linarith) (sq_pos_of_pos hs)
  have hJs : J*s^2=M+1 := div_mul_cancel₀ _ (pow_ne_zero _ hs.ne')
  let f : Point n → ℝ := fun p => g p-J*(p.2-z.2)^2
  have hf : ContinuousOn f K' := by
    exact (hg.mono hsub).sub (by fun_prop)
  have hzK' : z ∈ K' := ⟨hzK.1,by constructor <;> linarith⟩
  have hfz : f z=0 := by
    have hh := hslice z.1 hzK.1
    simpa [f] using hh
  obtain ⟨p,hp,hmax⟩ := ((isCompact_closedBall _ _).prod isCompact_Icc : IsCompact K').exists_isMaxOn
    ⟨z,hzK'⟩ hf
  have hfp : 0≤f p := by
    rw [←hfz]
    exact hmax hzK'
  have hspace : p.1 ∈ ball z.1 R := by
    by_contra hn
    have hpdist : dist p.1 z.1=R := le_antisymm hp.1 (le_of_not_gt hn)
    have hpn : ‖p.1-z.1‖=R := by simpa only [dist_eq_norm] using hpdist
    have hp0 : (p.1,z.2) ∈ K := ⟨hp.1,hzK.2⟩
    have htime : |p.2-z.2|≤ s := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have hdist : dist p (p.1,z.2)<delta := by
      simpa [Prod.dist_eq,Real.dist_eq] using htime.trans_lt hsd
    have hh := huniform p (hsub hp) (p.1,z.2) hp0 hdist
    rw [Real.dist_eq] at hh
    have hval := hslice p.1 hp.1
    rw [hpn] at hval
    have hle : g p-g (p.1,z.2)<R^4/2 := (le_abs_self _).trans_lt hh
    have hpen : 0≤J*(p.2-z.2)^2 := mul_nonneg hJ.le (sq_nonneg _)
    dsimp only [f] at hfp
    nlinarith [pow_pos hR 4]
  have htimeSq : (p.2-z.2)^2<s^2 := by
    have hgM := hbound p (hsub hp)
    dsimp only [f] at hfp
    nlinarith
  have htime := abs_lt_of_sq_lt_sq' htimeSq hs.le
  have htime' : p.2 ∈ Ioo (z.2-s) (z.2+s) := by
    constructor <;> linarith [htime.1,htime.2]
  have hopen : p ∈ ball z.1 R ×ˢ Ioo (z.2-s) (z.2+s) := ⟨hspace,htime'⟩
  refine ⟨J,p,hJ.le,⟨hspace,by constructor <;> linarith [htime'.1,htime'.2]⟩,?_⟩
  exact hmax.isLocalMax (mem_of_superset ((isOpen_ball.prod isOpen_Ioo).mem_nhds hopen)
    (fun _ h => ⟨ball_subset_closedBall h.1,h.2.1.le,h.2.2.le⟩))

end Yau.LeafProofs.L05Aux
