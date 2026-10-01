import KiknadzeKrasnov.SwirlMaximum
import KiknadzeKrasnov.EndpointRatio
import KiknadzeKrasnov.MultimodeQualification

namespace KiknadzeKrasnov
noncomputable section
open Set Filter
open scoped Topology

/-- The physical angular momentum tends to the independent line-circulation coefficient. -/
theorem multimodeSwirl_radius_tendsto_line {n : ℕ}
    {gammaLine s : ℝ} {circ beta : Fin n → ℝ}
    (hs : 0 < s) (hb : ∀ i, 0 < beta i) :
    Tendsto (fun r => r * multimodeSwirl gammaLine circ s beta r)
      (𝓝[>] 0) (𝓝 (gammaLine / (2 * Real.pi))) := by
  have hP : ∀ i, Tendsto (fun r => distributedCirculation (circ i) s (beta i) r)
      (𝓝[>] 0) (𝓝 0) := by
    intro i
    have hx0 : Tendsto (fun r : ℝ => scaledX (beta i) r) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun r : ℝ => scaledX (beta i) r) 0 := by
        unfold scaledX
        fun_prop
      simpa [scaledX] using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hc.tendsto
    have hx : Tendsto (fun r : ℝ => scaledX (beta i) r) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx0
      filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      unfold scaledX
      exact mul_pos (hb i) (sq_pos_of_pos hr)
    have h := (lowerGamma_tendsto_zero_nhdsGT hs).comp hx
    unfold distributedCirculation regLowerGamma
    simpa [Function.comp_def] using (h.div_const (gammaFn s)).const_mul (circ i)
  have hsum : Tendsto (fun r => ∑ i, distributedCirculation (circ i) s (beta i) r)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i hi => hP i)
  have hlim : Tendsto (fun r => (gammaLine + ∑ i,
      distributedCirculation (circ i) s (beta i) r) / (2 * Real.pi))
      (𝓝[>] 0) (𝓝 (gammaLine / (2 * Real.pi))) := by
    simpa using (hsum.const_add gammaLine).div_const (2 * Real.pi)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  unfold multimodeSwirl multimodeCirculationValue
  field_simp [hr.ne', Real.pi_ne_zero]

/-- On the punctured branch the actual finite-mode swirl is continuous. -/
theorem multimodeSwirl_continuousOn {n : ℕ} {gammaLine s : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hb : ∀ i, 0 < beta i) :
    ContinuousOn (multimodeSwirl gammaLine circ s beta) (Ioi (0 : ℝ)) := by
  intro r hr
  exact (multimodeSwirl_hasDerivAt hs hr hb).continuousAt.continuousWithinAt

/-- All FTC hypotheses for the pressure integral follow from positive reference and radius. -/
theorem multimodeSwirl_pressure_hasDerivAt {n : ℕ} {gammaLine s rRef r : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hb : ∀ i, 0 < beta i)
    (href : 0 < rRef) (hr : 0 < r) :
    HasDerivAt (swirlPressurePotential (multimodeSwirl gammaLine circ s beta) rRef)
      (multimodeSwirl gammaLine circ s beta r ^ 2 / r) r := by
  let f : ℝ → ℝ := fun y => multimodeSwirl gammaLine circ s beta y ^ 2 / y
  have hc : ∀ y > 0, ContinuousAt f y := by
    intro y hy
    exact (multimodeSwirl_hasDerivAt hs hy hb).continuousAt.pow 2 |>.div
      continuousAt_id hy.ne'
  apply swirlPressurePotential_hasDerivAt
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    have hpos : 0 < y := lt_of_lt_of_le (lt_min href hr) hy.1
    exact (hc y hpos).continuousWithinAt
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun y hy => hc y hy) r hr
  · exact hc r hr

/-- Axis regularity of a finite-mode field forces the independent line circulation to vanish. -/
theorem multimodeSwirl_finite_axis_limit_forces_line_zero {n : ℕ} {gammaLine s U : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hb : ∀ i, 0 < beta i)
    (hu : Tendsto (multimodeSwirl gammaLine circ s beta) (𝓝[>] 0) (𝓝 U)) :
    gammaLine = 0 := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hz : Tendsto (fun r => r * multimodeSwirl gammaLine circ s beta r)
      (𝓝[>] 0) (𝓝 0) := by simpa using hr.mul hu
  have he := tendsto_nhds_unique (multimodeSwirl_radius_tendsto_line hs hb) hz
  exact (div_eq_zero_iff).mp he |>.resolve_right (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The swirl-pressure integral has the leading line-circulation contribution.
The explicit derivative hypothesis is supplied by the existing FTC certificate. -/
theorem swirlPressurePotential_leading_term {Pi u : ℝ → ℝ} {line : ℝ}
    (hPi : ∀ᶠ r in 𝓝[>] (0 : ℝ), HasDerivAt Pi (u r ^ 2 / r) r)
    (hu : Tendsto (fun r => r * u r) (𝓝[>] 0) (𝓝 line)) :
    Tendsto (fun r => r ^ 2 * Pi r) (𝓝[>] 0) (𝓝 (-line ^ 2 / 2)) := by
  have hratio : Tendsto (fun r => (u r ^ 2 / r) / (-2 * r ^ (-3 : ℝ)))
      (𝓝[>] 0) (𝓝 (-line ^ 2 / 2)) := by
    have hlim := (hu.pow 2).div_const (-2)
    have hz : Tendsto (fun r => (r * u r) ^ 2 / (-2))
        (𝓝[>] 0) (𝓝 (-line ^ 2 / 2)) := by convert hlim using 1; ring
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    rw [Real.rpow_neg hr.le]
    norm_num [Real.rpow_natCast]
    field_simp [hr.ne']
  have hg : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun r : ℝ => r ^ (-2 : ℝ)) (-2 * r ^ (-3 : ℝ)) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    convert Real.hasDerivAt_rpow_const (p := (-2 : ℝ)) (Or.inl hr.ne') using 1; norm_num
  have hgn : ∀ᶠ r in 𝓝[>] (0 : ℝ), -2 * r ^ (-3 : ℝ) < 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    exact mul_neg_of_neg_of_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  have hgt : Tendsto (fun r : ℝ => r ^ (-2 : ℝ)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by norm_num)
  have hlim := endpoint_ratio_tendsto hPi hg hgn hgt hratio
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  rw [Real.rpow_neg hr.le]
  norm_num [Real.rpow_natCast]
  ring

/-- Correct near-axis pressure coefficient with optional central line circulation.
For the KK field line=Gamma_line/(2 pi); all other parameters are fixed at the snapshot. -/
theorem pressureFieldAtTime_axis_coefficient {rho a aDot b bDot q p0 z line : ℝ}
    {Pi u : ℝ → ℝ}
    (hPi : ∀ᶠ r in 𝓝[>] (0 : ℝ), HasDerivAt Pi (u r ^ 2 / r) r)
    (hu : Tendsto (fun r => r * u r) (𝓝[>] 0) (𝓝 line)) :
    Tendsto (fun r => r ^ 2 * pressureFieldAtTime rho a aDot b bDot q p0 Pi r z)
      (𝓝[>] 0) (𝓝 (-rho * (q ^ 2 + line ^ 2) / 2)) := by
  have hPiLim := swirlPressurePotential_leading_term hPi hu
  let regular : ℝ → ℝ := fun r => r ^ 2 *
    (p0 + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2 -
      rho / 2 * (aDot + a ^ 2) * z ^ 2 - rho * (bDot + a * b) * z)
  have hreg : Tendsto regular (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt regular 0 := by dsimp [regular]; fun_prop
    simpa [regular] using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hc.tendsto
  have hlim := (hreg.sub_const (rho * q ^ 2 / 2)).add (hPiLim.const_mul rho)
  have hz : Tendsto (fun r => regular r - rho * q ^ 2 / 2 + rho * (r ^ 2 * Pi r))
      (𝓝[>] 0) (𝓝 (-rho * (q ^ 2 + line ^ 2) / 2)) := by
    convert hlim using 1; ring
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  unfold regular pressureFieldAtTime
  field_simp [hr.ne']
  ring

/-- Original ledger pressure coefficient, now explicitly on the zero-line branch. -/
theorem pressureFieldAtTime_axis_coefficient_zero_line {rho a aDot b bDot q p0 z : ℝ}
    {Pi u : ℝ → ℝ}
    (hPi : ∀ᶠ r in 𝓝[>] (0 : ℝ), HasDerivAt Pi (u r ^ 2 / r) r)
    (hu : Tendsto (fun r => r * u r) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => r ^ 2 * pressureFieldAtTime rho a aDot b bDot q p0 Pi r z)
      (𝓝[>] 0) (𝓝 (-rho * q ^ 2 / 2)) := by
  simpa using pressureFieldAtTime_axis_coefficient hPi hu

/-- Direct near-axis pressure certificate for the actual finite-mode field and its actual swirl integral. -/
theorem multimodePressure_axis_coefficient {n : ℕ}
    {rho a aDot b bDot q p0 z gammaLine s rRef : ℝ} {circ beta : Fin n → ℝ}
    (hs : 0 < s) (hb : ∀ i, 0 < beta i) (href : 0 < rRef) :
    Tendsto (fun r => r ^ 2 * pressureFieldAtTime rho a aDot b bDot q p0
      (swirlPressurePotential (multimodeSwirl gammaLine circ s beta) rRef) r z)
      (𝓝[>] 0) (𝓝 (-rho * (q ^ 2 + (gammaLine / (2 * Real.pi)) ^ 2) / 2)) := by
  apply pressureFieldAtTime_axis_coefficient
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact multimodeSwirl_pressure_hasDerivAt hs hb href hr
  · exact multimodeSwirl_radius_tendsto_line hs hb

end
end KiknadzeKrasnov
