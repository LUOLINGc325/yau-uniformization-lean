import Yau.LeafProofs.L16L2Products

open MeasureTheory Filter
open scoped Topology ContDiff Convolution
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def compactEnergyFunctional {n : ℕ} (ψ w : Point n → ℝ)
    (H P : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ) : ℝ :=
  -(1/2 : ℝ)*(∫ p, fderiv ℝ ψ p (0,1)*w p*w p)+
    (∑ i, ((∫ p, ψ p*P p i*H p i)+(∫ p, fderiv ℝ ψ p (Yau.realVec i,0)*P p i*w p)))-
    (∫ p, ψ p*R p*w p)

theorem integral_energy_eq_compactEnergyFunctional {n : ℕ}
    {ψ w R : Point n → ℝ} {H P : Point n → Yau.RIdx n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hw : MemLp w 2 volume) (hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hP : ∀ i, MemLp (fun p => P p i) 2 volume) (hR : MemLp R 2 volume) :
    (∫ p, -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
      (∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p) =
    compactEnergyFunctional ψ w H P R := by
  have hTop : MemLp ψ (⊤ : ENNReal) volume := hψ.continuous.memLp_top_of_hasCompactSupport hcψ _
  have hDTop (e : Point n) : MemLp (fun p => fderiv ℝ ψ p e) (⊤ : ENNReal) volume :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ e) _
  let A : Point n → ℝ := fun p => fderiv ℝ ψ p (0,1)*w p*w p
  let B : Yau.RIdx n → Point n → ℝ := fun i p => ψ p*P p i*H p i
  let C : Yau.RIdx n → Point n → ℝ := fun i p => fderiv ℝ ψ p (Yau.realVec i,0)*P p i*w p
  let D : Point n → ℝ := fun p => ψ p*R p*w p
  have hA : Integrable A volume := integrable_weighted_mul_of_memLp (hDTop _) hw hw
  have hB (i : Yau.RIdx n) : Integrable (B i) volume := integrable_weighted_mul_of_memLp hTop (hP i) (hH i)
  have hC (i : Yau.RIdx n) : Integrable (C i) volume := integrable_weighted_mul_of_memLp (hDTop _) (hP i) hw
  have hD : Integrable D volume := integrable_weighted_mul_of_memLp hTop hR hw
  have hSum : Integrable (fun p => ∑ i, (B i p+C i p)) volume :=
    integrable_finsetSum Finset.univ (fun i _ => (hB i).add (hC i))
  have hFun : (fun p => -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
      (∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p) =
      fun p => -(1/2 : ℝ)*A p+(∑ i, (B i p+C i p))-D p := by
    funext p
    have hSumEq : (∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0))) =
        ∑ i, (B i p+C i p) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [B,C]
      ring
    rw [hSumEq]
    dsimp only [A,D]
    ring
  rw [hFun]
  have hSplit1 := integral_sub ((hA.const_mul (-(1/2 : ℝ))).add hSum) hD
  have hSplit2 := integral_add (hA.const_mul (-(1/2 : ℝ))) hSum
  simp only [Pi.add_apply] at hSplit1 hSplit2
  have hBi (i : Yau.RIdx n) : Integrable (fun p => B i p+C i p) volume := (hB i).add (hC i)
  rw [hSplit1,hSplit2,integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hBi i)]
  have hAdd (i : Yau.RIdx n) : (∫ p, B i p+C i p) = (∫ p, B i p)+(∫ p, C i p) := by
    simpa only [Pi.add_apply] using integral_add (hB i) (hC i)
  simp_rw [hAdd]
  rfl

theorem compactEnergyFunctional_tendsto {n : ℕ} {ψ w R : Point n → ℝ}
    {H P : Point n → Yau.RIdx n → ℝ}
    {wk Rk : ℕ → Point n → ℝ} {Hk Pk : ℕ → Point n → Yau.RIdx n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hw : MemLp w 2 volume) (hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hP : ∀ i, MemLp (fun p => P p i) 2 volume) (hR : MemLp R 2 volume)
    (hwk : ∀ k, MemLp (wk k) 2 volume) (hHk : ∀ k i, MemLp (fun p => Hk k p i) 2 volume)
    (hPk : ∀ k i, MemLp (fun p => Pk k p i) 2 volume) (hRk : ∀ k, MemLp (Rk k) 2 volume)
    (hWlim : Tendsto (fun k => ∫ p, ‖wk k p-w p‖^2) atTop (𝓝 0))
    (hHlim : ∀ i, Tendsto (fun k => ∫ p, ‖Hk k p i-H p i‖^2) atTop (𝓝 0))
    (hPlim : ∀ i, Tendsto (fun k => ∫ p, ‖Pk k p i-P p i‖^2) atTop (𝓝 0))
    (hRlim : Tendsto (fun k => ∫ p, ‖Rk k p-R p‖^2) atTop (𝓝 0)) :
    Tendsto (fun k => compactEnergyFunctional ψ (wk k) (Hk k) (Pk k) (Rk k)) atTop
      (𝓝 (compactEnergyFunctional ψ w H P R)) := by
  have hTop : MemLp ψ (⊤ : ENNReal) volume := hψ.continuous.memLp_top_of_hasCompactSupport hcψ _
  have hDTop (e : Point n) : MemLp (fun p => fderiv ℝ ψ p e) (⊤ : ENNReal) volume :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ e) _
  apply Tendsto.sub
  · apply Tendsto.add
    · exact (tendsto_integral_weighted_mul_of_L2 hwk hwk hw hw (hDTop _) hWlim hWlim).const_mul _
    · apply tendsto_finsetSum
      intro i _
      exact (tendsto_integral_weighted_mul_of_L2 (fun k => hPk k i) (fun k => hHk k i)
        (hP i) (hH i) hTop (hPlim i) (hHlim i)).add
        (tendsto_integral_weighted_mul_of_L2 (fun k => hPk k i) hwk (hP i) hw (hDTop _) (hPlim i) hWlim)
  · exact tendsto_integral_weighted_mul_of_L2 hRk hwk hR hw hTop hRlim hWlim

theorem weakDivergenceEvolution_compact_energy_identity {n : ℕ}
    {w ψ R : Point n → ℝ} {H P : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hP : ∀ i, MemLp (fun p => P p i) 2 volume) (hR : MemLp R 2 volume)
    (hcw : HasCompactSupport w) (hcH : ∀ i, HasCompactSupport (fun p => H p i))
    (hcP : ∀ i, HasCompactSupport (fun p => P p i)) (hcR : HasCompactSupport R)
    (hGrad : WeakGradient Set.univ Set.univ w H)
    (hEq : WeakDivergenceEvolution Set.univ Set.univ w P R)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    compactEnergyFunctional ψ w H P R = 0 := by
  let ε : ℕ → ℝ := fun k => (1/2 : ℝ)^k
  have hε (k : ℕ) : 0 < ε k := pow_pos (by norm_num) k
  have hε1 (k : ℕ) : ε k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let wk : ℕ → Point n → ℝ := fun k => jointMollify (ε k) w
  let Hk : ℕ → Point n → Yau.RIdx n → ℝ := fun k p i => jointMollify (ε k) (fun q => H q i) p
  let Pk : ℕ → Point n → Yau.RIdx n → ℝ := fun k p i => jointMollify (ε k) (fun q => P q i) p
  let Rk : ℕ → Point n → ℝ := fun k => jointMollify (ε k) R
  have hw1 := Yau.LeafProofs.L03.memLp_two_compact_integrable volume w hw hcw
  have hP1 (i : Yau.RIdx n) := Yau.LeafProofs.L03.memLp_two_compact_integrable volume _ (hP i) (hcP i)
  have hR1 := Yau.LeafProofs.L03.memLp_two_compact_integrable volume R hR hcR
  have hwk (k : ℕ) : MemLp (wk k) 2 volume := jointMollify_memLp (hε k) hw hcw
  have hHk (k : ℕ) (i : Yau.RIdx n) : MemLp (fun p => Hk k p i) 2 volume :=
    jointMollify_memLp (hε k) (hH i) (hcH i)
  have hPk (k : ℕ) (i : Yau.RIdx n) : MemLp (fun p => Pk k p i) 2 volume :=
    jointMollify_memLp (hε k) (hP i) (hcP i)
  have hRk (k : ℕ) : MemLp (Rk k) 2 volume := jointMollify_memLp (hε k) hR hcR
  have hwSmooth (k : ℕ) : ContDiff ℝ ∞ (wk k) := jointMollify_smooth (hε k) hw1
  have hPSmooth (k : ℕ) (i : Yau.RIdx n) : ContDiff ℝ ∞ (fun p => Pk k p i) :=
    jointMollify_smooth (hε k) (hP1 i)
  have hPDE (k : ℕ) (p : Point n) : fderiv ℝ (wk k) p (0,1) =
      (∑ i, fderiv ℝ (fun q => Pk k q i) p (Yau.realVec i,0))+Rk k p :=
    weakDivergenceEvolution_convolution hEq hw1 hP1 hR1 _
      (jointMollifierScaled_smooth (ε k)) (jointMollifierScaled_compact (hε k)) p
  have hDwk (k : ℕ) (p : Point n) (i : Yau.RIdx n) :
      fderiv ℝ (wk k) p (Yau.realVec i,0) = Hk k p i :=
    (d_eq_joint_fderiv ((hwSmooth k).differentiable (by simp) p) i).symm.trans
      (weakGradient_jointMollify_spatial (hε k) hw1 hGrad p i)
  have hZero (k : ℕ) : compactEnergyFunctional ψ (wk k) (Hk k) (Pk k) (Rk k) = 0 := by
    have h := smooth_divergence_energy_identity (hwSmooth k) (hPSmooth k) hψ hcψ (hPDE k)
    simp_rw [hDwk k] at h
    exact (integral_energy_eq_compactEnergyFunctional hψ hcψ (hwk k) (hHk k) (hPk k) (hRk k)).symm.trans h
  have hLim := compactEnergyFunctional_tendsto hψ hcψ hw hH hP hR hwk hHk hPk hRk
    (jointMollify_L2_tendsto hε hε1 hεlim hw hcw)
    (fun i => jointMollify_L2_tendsto hε hε1 hεlim (hH i) (hcH i))
    (fun i => jointMollify_L2_tendsto hε hε1 hεlim (hP i) (hcP i))
    (jointMollify_L2_tendsto hε hε1 hεlim hR hcR)
  have hLimZero : Tendsto (fun k => compactEnergyFunctional ψ (wk k) (Hk k) (Pk k) (Rk k))
      atTop (𝓝 0) := by simp only [hZero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hLim hLimZero

theorem localEnergy_cutoff_energy_identity {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u ψ : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {η : Point n → ℝ} (hη : Test (O ×ˢ Set.Ioo l r) η)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    compactEnergyFunctional ψ (fun p => η p*u p)
      (fun p i => η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i)
      (fun p i => η p*energyFlux a G p i)
      (cutoffEvolutionSource u (energyFlux a G) (fun p => ∑ j, energyDrift a b p j*G p j) η) = 0 := by
  obtain ⟨hw,hH,hGrad⟩ := localEnergy_cutoff_weakH1 hO hE hη
  apply weakDivergenceEvolution_compact_energy_identity hw hH
    (fun i => localEnergy_cutoff_flux_memLp hO hSmooth hE hη i)
    (localEnergy_cutoff_evolutionSource_memLp hO hSmooth hE hη)
    hη.2.1.mul_right
    (fun i => hη.2.1.mul_right.add (test_spatialDerivative hη i).2.1.mul_left)
    (fun _ => hη.2.1.mul_right) (cutoffEvolutionSource_compact _ _ _ hη)
    hGrad (weakEquation_homogeneous_cutoff hEq hη) hψ hcψ

theorem exists_test_eq_one_near_compact {n : ℕ} {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q) :
    ∃ η : Point n → ℝ, Test Q η ∧ ∀ p ∈ K, η =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨V,hV,hKV,hVQ,hVC⟩ := exists_open_between_and_isCompact_closure hK hQ hKQ
  obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨η,hη,_hRange,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW (isClosed_closure : IsClosed (closure V)) hVW
  have hcη : HasCompactSupport η := by
    change IsCompact (tsupport η)
    simpa only [tsupport,hSupport] using hWC
  have hηQ : tsupport η ⊆ Q := by simpa only [tsupport,hSupport] using hWQ
  refine ⟨η,⟨hη,hcη,hηQ⟩,?_⟩
  intro p hp
  filter_upwards [hV.mem_nhds (hKV hp)] with q hq
  exact (hOne q).mp (subset_closure hq)

theorem integral_weighted_mul_congr_on {n : ℕ} {K : Set (Point n)}
    {η f g f' g' : Point n → ℝ} (hZero : ∀ p ∉ K, η p = 0)
    (hF : Set.EqOn f f' K) (hG : Set.EqOn g g' K) :
    (∫ p, η p*f p*g p) = ∫ p, η p*f' p*g' p := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  by_cases hp : p ∈ K
  · rw [hF hp,hG hp]
  · simp only [hZero p hp,zero_mul]

theorem compactEnergyFunctional_congr_on_support {n : ℕ}
    {ψ w w' R R' : Point n → ℝ} {H H' P P' : Point n → Yau.RIdx n → ℝ}
    (hW : Set.EqOn w w' (tsupport ψ))
    (hH : ∀ i, Set.EqOn (fun p => H p i) (fun p => H' p i) (tsupport ψ))
    (hP : ∀ i, Set.EqOn (fun p => P p i) (fun p => P' p i) (tsupport ψ))
    (hR : Set.EqOn R R' (tsupport ψ)) :
    compactEnergyFunctional ψ w H P R = compactEnergyFunctional ψ w' H' P' R' := by
  have hZero (p : Point n) (hp : p ∉ tsupport ψ) : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
  have hDZero (e : Point n) (p : Point n) (hp : p ∉ tsupport ψ) : fderiv ℝ ψ p e = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ hp,zero_apply]
  simp only [compactEnergyFunctional,
    integral_weighted_mul_congr_on (hDZero (0,1)) hW hW,
    integral_weighted_mul_congr_on hZero (hP _) (hH _),
    integral_weighted_mul_congr_on (hDZero _) (hP _) hW,
    integral_weighted_mul_congr_on hZero hR hW]

theorem localEnergy_homogeneous_compact_energy_identity {n : ℕ}
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u ψ : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    (hψ : Test (O ×ˢ Set.Ioo l r) ψ) :
    compactEnergyFunctional ψ u G (energyFlux a G) (fun p => ∑ j, energyDrift a b p j*G p j) = 0 := by
  obtain ⟨η,hη,hNear⟩ := exists_test_eq_one_near_compact (hO.prod isOpen_Ioo) hψ.2.1 hψ.2.2
  have hValue (p : Point n) (hp : p ∈ tsupport ψ) : η p = 1 := (hNear p hp).eq_of_nhds
  have hD (p : Point n) (hp : p ∈ tsupport ψ) : fderiv ℝ η p = 0 := by
    simpa only [fderiv_fun_const,Pi.zero_apply] using (hNear p hp).fderiv_eq (𝕜 := ℝ)
  have hSpace (p : Point n) (hp : p ∈ tsupport ψ) (i : Yau.RIdx n) :
      d (fun x => η (x,p.2)) p.1 i = 0 := by
    rw [d_eq_joint_fderiv (hη.1.differentiable (by simp) p) i,hD p hp,zero_apply]
  have hTime (p : Point n) (hp : p ∈ tsupport ψ) : deriv (fun t => η (p.1,t)) p.2 = 0 := by
    rw [test_timeDerivative_eq_joint_fderiv (hη.1.differentiable (by simp) p),hD p hp,zero_apply]
  have hIdent := compactEnergyFunctional_congr_on_support
    (ψ := ψ) (w := fun p => η p*u p) (w' := u)
    (H := fun p i => η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i) (H' := G)
    (P := fun p i => η p*energyFlux a G p i) (P' := energyFlux a G)
    (R := cutoffEvolutionSource u (energyFlux a G) (fun p => ∑ j, energyDrift a b p j*G p j) η)
    (R' := fun p => ∑ j, energyDrift a b p j*G p j)
    (fun p hp => by simp only [hValue p hp,one_mul])
    (fun i p hp => by simp only [hValue p hp,hSpace p hp i,one_mul,mul_zero,add_zero])
    (fun i p hp => by simp only [hValue p hp,one_mul])
    (fun p hp => by simp only [cutoffEvolutionSource,hValue p hp,hTime p hp,hSpace p hp,
      one_mul,mul_zero,add_zero,Finset.sum_const_zero,sub_zero])
  exact hIdent.symm.trans (localEnergy_cutoff_energy_identity hO hSmooth hE hEq hη hψ.1 hψ.2.1)

end Yau.LeafProofs.L16Aux
