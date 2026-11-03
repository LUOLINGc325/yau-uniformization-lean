import Yau.LeafProofs.L05PerronQuartic

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option maxHeartbeats 1200000 in
theorem spatialTime_max_difference_jets {n : ℕ} {u v : Point n → ℝ} {p : Point n}
    (hu : ContDiffAt ℝ 2 (fun x : Space n => u (x,p.2)) p.1)
    (hv : ContDiffAt ℝ 2 (fun x : Space n => v (x,p.2)) p.1)
    (hut : DifferentiableAt ℝ (fun t => u (p.1,t)) p.2)
    (hvt : DifferentiableAt ℝ (fun t => v (p.1,t)) p.2)
    (hm : IsLocalMax (fun q => u q-v q) p) :
    deriv (fun t => u (p.1,t)) p.2=deriv (fun t => v (p.1,t)) p.2 ∧
      ((hessian v p : Mat n)-(hessian u p : Mat n)).PosSemidef := by
  have hxt : Tendsto (fun x : Space n => (x,p.2)) (𝓝 p.1) (𝓝 p) := by
    convert! (continuous_id.prodMk continuous_const).tendsto p.1 using 1 <;> simp only [id_eq,Prod.eta]
  have htt : Tendsto (fun t : ℝ => (p.1,t)) (𝓝 p.2) (𝓝 p) := by
    convert! (continuous_const.prodMk continuous_id).tendsto p.2 using 1 <;> simp only [id_eq,Prod.eta]
  have hmx : IsLocalMax (fun x : Space n => u (x,p.2)-v (x,p.2)) p.1 := hxt hm
  have hmt : IsLocalMax (fun t : ℝ => u (p.1,t)-v (p.1,t)) p.2 := htt hm
  have htime := hmt.hasDerivAt_eq_zero (hut.hasDerivAt.sub hvt.hasDerivAt)
  have hU : ContDiffAt ℝ 2 (fun q : Point n => u (q.1,p.2)) p := hu.comp p contDiffAt_fst
  have hV : ContDiffAt ℝ 2 (fun q : Point n => v (q.1,p.2)) p := hv.comp p contDiffAt_fst
  have hH := perron_spatial_localMax_hessian_nonpos (hU.sub hV) hmx
  rw [perron_hessian_sub hU hV] at hH
  change (-((hessian u p : Mat n)-(hessian v p : Mat n))).PosSemidef at hH
  refine ⟨by linarith only [htime],?_⟩
  convert! hH using 1
  abel

theorem c2_open_time_differentiableAt {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p ∈ Q) :
    DifferentiableAt ℝ (fun t => u (p.1,t)) p.2 ∧
      timeD Q u p=deriv (fun t => u (p.1,t)) p.2 := by
  have ht : Tendsto (fun t : ℝ => (p.1,t)) (𝓝 p.2) (𝓝 p) := by
    convert! (continuous_const.prodMk continuous_id).tendsto p.2 using 1 <;> simp only [id_eq,Prod.eta]
  have hs : {t | (p.1,t) ∈ Q} ∈ 𝓝 p.2 := ht (hQ.mem_nhds hp)
  exact ⟨(hu.2.2.2.2.2 p hp).differentiableAt hs,derivWithin_of_mem_nhds hs⟩

theorem timeD_open_restrict {n : ℕ} {Q S : Set (Point n)} (hQ : IsOpen Q) (hQS : Q ⊆ S)
    (u : Point n → ℝ) {p : Point n} (hp : p ∈ Q) : timeD Q u p=timeD S u p := by
  have ht : Tendsto (fun t : ℝ => (p.1,t)) (𝓝 p.2) (𝓝 p) := by
    convert! (continuous_const.prodMk continuous_id).tendsto p.2 using 1 <;> simp only [id_eq,Prod.eta]
  have hq : {t | (p.1,t) ∈ Q} ∈ 𝓝 p.2 := ht (hQ.mem_nhds hp)
  have hs : {t | (p.1,t) ∈ S} ∈ 𝓝 p.2 := mem_of_superset hq (fun _ hx => hQS hx)
  unfold timeD
  rw [derivWithin_of_mem_nhds hq,derivWithin_of_mem_nhds hs]

theorem c2_open_restrict {n : ℕ} {Q S : Set (Point n)} (hQ : IsOpen Q) (hQS : Q ⊆ S)
    {u : Point n → ℝ} (hu : C2 S u) : C2 Q u := by
  refine ⟨hu.1.mono hQS,hu.2.1.mono hQS,hu.2.2.1.mono hQS,?_,
    fun p hp => hu.2.2.2.2.1 p (hQS hp),?_⟩
  · exact (hu.2.2.2.1.mono hQS).congr (fun p hp => timeD_open_restrict hQ hQS u hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hQS hp)).mono (fun t ht => hQS ht)

theorem timeD_univ_eq_time_deriv {n : ℕ} (phi : Point n → ℝ) (p : Point n) :
    timeD Set.univ phi p=deriv (fun t => phi (p.1,t)) p.2 := by
  change derivWithin (fun t => phi (p.1,t)) Set.univ p.2=_
  rw [derivWithin_univ]

theorem parabolic_touchAbove_jets {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p ∈ Q)
    {phi : Point n → ℝ} (hphi : ContDiffAt ℝ 2 phi p) (ht : touchAbove phi u p) :
    timeD Q u p=timeD Set.univ phi p ∧
      ((hessian phi p : Mat n)-(hessian u p : Mat n)).PosSemidef := by
  have htU := c2_open_time_differentiableAt hQ hu hp
  have hsP := hphi.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have htP := (hphi.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
  have hm : IsLocalMax (fun q => u q-phi q) p := by
    filter_upwards [ht.2] with q hq
    change u q-phi q ≤ u p-phi p
    linarith only [hq,ht.1]
  have hh := spatialTime_max_difference_jets (hu.2.2.2.2.1 p hp) hsP htU.1 htP hm
  exact ⟨htU.2.trans (hh.1.trans (timeD_univ_eq_time_deriv phi p).symm),hh.2⟩

theorem parabolic_touchBelow_jets {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p ∈ Q)
    {phi : Point n → ℝ} (hphi : ContDiffAt ℝ 2 phi p) (ht : touchBelow phi u p) :
    timeD Q u p=timeD Set.univ phi p ∧
      ((hessian u p : Mat n)-(hessian phi p : Mat n)).PosSemidef := by
  have htU := c2_open_time_differentiableAt hQ hu hp
  have hsP := hphi.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have htP := (hphi.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
  have hm : IsLocalMax (fun q => phi q-u q) p := by
    filter_upwards [ht.2] with q hq
    change phi q-u q ≤ phi p-u p
    linarith only [hq,ht.1]
  have hh := spatialTime_max_difference_jets hsP (hu.2.2.2.2.1 p hp) htP htU.1 hm
  exact ⟨htU.2.trans (hh.1.symm.trans (timeD_univ_eq_time_deriv phi p).symm),hh.2⟩

theorem parabolic_classical_sub {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {ell L : ℝ} (hell : 0 ≤ ell) {G : Sym n → Point n → ℝ}
    (hG : ∀ p ∈ Q, globalElliptic (fun H => G H p) ell L)
    {u f : Point n → ℝ} (hu : C2 Q u)
    (hs : ∀ p ∈ Q, timeD Q u p-G (hessian u p) p ≤ f p) : viscositySub Q G f u := by
  intro p hp phi hphi ht
  obtain ⟨htime,hH⟩ := parabolic_touchAbove_jets hQ hu hp hphi ht
  have hm := perron_globalElliptic_mono hell (hG p hp) hH
  have hh := hs p hp
  change timeD Set.univ phi p-G (hessian phi p) p ≤ f p
  rw [htime] at hh
  linarith only [hh,hm]

theorem parabolic_classical_super {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {ell L : ℝ} (hell : 0 ≤ ell) {G : Sym n → Point n → ℝ}
    (hG : ∀ p ∈ Q, globalElliptic (fun H => G H p) ell L)
    {u f : Point n → ℝ} (hu : C2 Q u)
    (hs : ∀ p ∈ Q, f p ≤ timeD Q u p-G (hessian u p) p) : viscositySuper Q G f u := by
  intro p hp phi hphi ht
  obtain ⟨htime,hH⟩ := parabolic_touchBelow_jets hQ hu hp hphi ht
  have hm := perron_globalElliptic_mono hell (hG p hp) hH
  have hh := hs p hp
  change f p ≤ timeD Set.univ phi p-G (hessian phi p) p
  rw [htime] at hh
  linarith only [hh,hm]

end Yau.LeafProofs.L05Aux
